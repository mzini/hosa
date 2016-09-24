module HoSA.Data.Expression (
  Symbol (..)
  , Variable (..)
  , Expression (..)
  , Equation (..)
  , Location
  , UntypedExpression
  , UntypedEquation
  -- ops
  , IsSymbol (..)
  , isConstructor
  , funs
  , fvars
  , tfuns
  , tfvars
  , tfunsDL
  , tfvarsDL
  , sexpr
  , fromSexpr
  , headSymbol
  , definedSymbol
  -- parsing
  , fromFile
  , ParseError
  -- pretty
  , prettyExpression
  , prettyEquation
  ) where

import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Maybe (fromJust)
import HoSA.Utils (ppSeq)


----------------------------------------------------------------------
-- data types
----------------------------------------------------------------------

data Symbol = Symbol { symName :: String, defined :: Bool }
  deriving (Eq, Ord, Show)

-- TODO: generalise


newtype Variable = Variable { varName :: String }
  deriving (Eq, Ord, Show)

class IsSymbol f where
  isDefined :: f -> Bool

instance IsSymbol Symbol where
  isDefined = defined

isConstructor :: IsSymbol f => f -> Bool
isConstructor = not . isDefined

type Location = Int

data Expression f v tp =
  Var v tp
  | Pair (tp,tp) (Expression f v tp) (Expression f v tp)
  | Fun f tp Location
  | Apply tp (Expression f v tp) (Expression f v tp)
  | LetP tp (Expression f v tp) ((v,tp),(v,tp)) (Expression f v tp)  
--  | Lam v (Expression f v tp)  

-- TODO: generalise
pattern NIL = Symbol "[]" False
pattern CONS = Symbol "(:)" False

enil :: Location -> UntypedExpression Symbol v
enil = Fun NIL ()
econs :: Location -> UntypedExpression Symbol v -> UntypedExpression Symbol v -> UntypedExpression Symbol v
econs l h t = Apply () (Apply () (Fun CONS () l) h) t

data Equation f v tp = Equation { lhs :: Expression f v tp, rhs :: Expression f v tp }


type UntypedExpression f v = Expression f v ()
type UntypedEquation f v = Equation f v ()

-- ops
----------------------------------------------------------------------

tfunsDL :: Expression f v tp -> [(f,tp,Location)] -> [(f,tp,Location)]
tfunsDL (Var _ _)        = id
tfunsDL (Fun f tp l)     = (:) (f,tp,l)
tfunsDL (Pair _ t1 t2)   = tfunsDL t2 . tfunsDL t1
tfunsDL (Apply _ t1 t2)  = tfunsDL t2 . tfunsDL t1
tfunsDL (LetP _ t1 _ t2) = tfunsDL t2 . tfunsDL t1

tfvarsDL :: Eq v => Expression f v tp -> [(v,tp)] -> [(v,tp)]
tfvarsDL (Var v tp)                   = (:) (v,tp)
tfvarsDL (Fun _ _ _)                  = id
tfvarsDL (Pair _ t1 t2)               = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (Apply _ t1 t2)              = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (LetP _ t1 ((x,_),(y,_)) t2) =
  (++) (filter (\ (z,_) -> z == x || z == y) (tfvarsDL t2 [])) . tfvarsDL t1

tfuns :: Expression f v tp -> [(f,tp,Location)]
tfuns = flip tfunsDL []

tfvars :: Eq v => Expression f v tp -> [(v,tp)]
tfvars = flip tfvarsDL []

funs :: Expression f v tp -> [f]
funs e = [ f | (f,_,_) <- tfunsDL e []]

fvars :: Eq v => Expression f v tp -> [v]
fvars = map fst . flip tfvarsDL []


sexpr :: Expression f v tp -> (Expression f v tp, [Expression f v tp])
sexpr (Apply _ t1 t2) = (h, rest ++ [t2]) where (h,rest) = sexpr t1
sexpr t = (t,[])

fromSexpr :: UntypedExpression f v -> [UntypedExpression f v] -> UntypedExpression f v
fromSexpr = foldl (Apply ())

headSymbol :: Expression f v tp -> Maybe (f,tp)
headSymbol (Fun f tp _)   = Just (f,tp)
headSymbol (Apply _ t1 _) = headSymbol t1
headSymbol _              = Nothing

definedSymbol :: Equation f v tp -> (f,tp)
definedSymbol = fromJust . headSymbol . lhs

----------------------------------------------------------------------
-- parsing
----------------------------------------------------------------------

type Parser = CharParser Location

freshLocation :: Parser Location
freshLocation = updateState (+1) >> getState

-- lexing
------------------------------------------------------------

whiteSpace1 :: Parser String
whiteSpace1 = many1 ((space <|> tab <|> newline) <?> "whitespace")

comment :: Parser String
comment = (string "(*" >> manyTill anyChar (try (string "*)"))) <?> "comment"

lexeme :: Parser a -> Parser a
lexeme p = p <* many (try comment <|> whiteSpace1)

identifier :: Parser String -> Parser String
identifier p = do
  s <- lexeme p
  if s `elem` reservedWords
   then unexpected ("reserved word " ++ show s)
   else return s

ident :: Parser String
ident = many (try alphaNum <|> oneOf "'_/#?")

variable :: Parser Variable
variable = Variable <$> identifier ((:) <$> lower <*> ident) <?> "variable" where

constructor :: Parser Symbol
constructor = constr <$> identifier ((:) <$> (try upper <|> digit) <*> ident) <?> "constructor" where
  constr n = Symbol { symName = n, defined = False }

symbol :: Parser Symbol
symbol = defsym <$> identifier ((:) <$> lower <*> ident) <?> "symbol" where
  defsym n = Symbol { symName = n, defined = True }
  
parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))

comma :: Parser Char
comma = lexeme (char ',')

reserved :: String -> Parser ()
reserved = void . lexeme . string

pair :: Parser a -> Parser b -> Parser (a,b)
pair pa pb = parens $ do
  a <- pa
  _ <- comma
  b <- pb
  return (a,b)

reservedWords :: [String]
reservedWords = words "let be in ; = [ ] ::"

-- parsers
------------------------------------------------------------

fun :: Symbol -> Parser (UntypedExpression Symbol Variable)
fun f = Fun f () <$> freshLocation

var :: Variable -> Parser (UntypedExpression Symbol Variable)
var v = return (Var v ())

-- lstP :: Parser (UntypedExpression Symbol Variable) -> Parser (UntypedExpression Symbol Variable)
-- lstP e = try (parens pList) <|> pList
--   where 
--     pList = try (reserved "[]" >> enil <$> freshLocation)
--             <|> (e >>= \ h ->
--                     try (reserved "::" >> )
--                     <|> return h)

lstP :: [UntypedExpression Symbol Variable] -> Parser (UntypedExpression Symbol Variable)
lstP [] = enil <$> freshLocation
lstP [e] = return e
lstP (e:es') = econs <$> freshLocation <*> return e <*> lstP es'

nilP :: Parser (UntypedExpression Symbol Variable)
nilP = reserved "[]" >> (enil <$> freshLocation)
  
lhsP :: Parser (UntypedExpression Symbol Variable)
lhsP = application (s <?> "function") arg where
  
  application h rest = foldl (Apply ()) <$> h <*> many rest
  
  arg = (p `sepBy1` reserved ":") >>= lstP
  
  p = try nilP <|> try c <|> try v <|> parens (application arg arg)
    
  s = (symbol >>= fun) <?> "function symbol"
  
  c = (constructor >>= fun) <?> "constructor"
  
  v = (variable >>= var) <?> "variable"

rhsP :: [Variable] -> Parser (UntypedExpression Symbol Variable)
rhsP = expression where
  
  expression vs = foldl (Apply ()) <$> arg vs <*> many (arg vs)
  
  arg vs = (p `sepBy1` reserved ":") >>= lstP where
    p = l vs <|> try nilP <|> try c <|> try (v vs) <|> try s <|> par vs

  par vs = foldr1 (Pair ((),())) <$> parens (expression vs `sepBy1` comma)
    
  c = (constructor >>= fun) <?> "constructor"
  
  v vs = do
    x <- variable
    if x `elem` vs then return (Var x ()) else unexpected "variable expected."
    
  s = (symbol >>= fun) <?> "function symbol"

  l vs = do
    try (reserved "let")
    t1 <- expression vs
    reserved "be"
    (v1,v2) <- pair variable variable
    reserved "in"
    t2 <- expression (v1 : v2 : vs)
    return (LetP () t1 ((v1,()),(v2,())) t2)

eqP :: Parser (UntypedEquation Symbol Variable)
eqP = do {l <- lhsP; reserved "="; r <- rhsP (fvars l); return (Equation l r); } <?> "equation"

eqsP :: Parser [UntypedEquation Symbol Variable]
eqsP = do {rs <- eqP `endBy` reserved ";"; return rs}


fromFile :: MonadIO m => FilePath -> m (Either ParseError [UntypedEquation Symbol Variable])
fromFile file = runParser parser 0 sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parser = many (try comment <|> whiteSpace1) *> (eqsP) <* eof


-- pretty printing
----------------------------------------------------------------------

-- instance PP.Pretty Symbol where pretty f = PP.bold (PP.text (symbolName f))
-- instance PP.Pretty Variable where pretty (Variable v) = PP.text v

ppTuple :: (PP.Pretty a, PP.Pretty b) => (a,b) -> PP.Doc
ppTuple (a,b) = PP.parens (ppSeq (PP.text ", ") [ PP.pretty a, PP.pretty b])

prettyExpression :: Bool -> (f -> PP.Doc) -> (v -> PP.Doc) -> Expression f v tp -> PP.Doc
prettyExpression showLabel ppFun ppVar = pp id where
  pp _ (Var v _) = ppVar v
  pp _ (Fun f _ l)
    | showLabel = ppFun f PP.<> PP.text "@" PP.<> PP.int l
    | otherwise = ppFun f 
  pp _ (Pair _ t1 t2) = ppTuple (pp id t1, pp id t2)
  pp par (Apply _ t1 t2) =
    par (pp id t1 PP.</> pp PP.parens t2)
  pp par (LetP _ t1 ((x,_),(y,_)) t2) =
    par (PP.align (PP.text "let" PP.<+> ppTuple (ppVar x, ppVar y)
                   PP.<+> PP.text "=" PP.<+> pp id t1
                   PP.<$> PP.hang 3 (PP.text "in" PP.<+> pp id t2)))

prettyEquation :: (f -> PP.Doc) -> (v -> PP.Doc) -> Equation f v tp -> PP.Doc
prettyEquation ppFun ppVar eqn = pp False (lhs eqn) PP.<+> PP.text "=" PP.</> pp False (rhs eqn) where
  pp showLabel = prettyExpression showLabel ppFun ppVar

instance PP.Pretty Symbol where
  pretty f | defined f = PP.bold (PP.text (symName f))
           | otherwise = (PP.text (symName f))
                         
instance PP.Pretty Variable where pretty = PP.text . varName

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Expression f v tp) where
  pretty = prettyExpression False PP.pretty PP.pretty
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Equation f v tp) where
  pretty = prettyEquation PP.pretty PP.pretty
