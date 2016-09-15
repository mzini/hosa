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
  , funsDL
  , fvars
  , fvarsDL
  , sexpr
  , fromSexpr
  , mapExpression
  , mapExpressionM
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
import qualified Data.Map as M
import Data.Maybe (isJust,fromJust)
import HoSA.Utils (ppSeq)


----------------------------------------------------------------------
-- data types
----------------------------------------------------------------------

data Symbol = Symbol { symName :: String, defined :: Bool }
  deriving (Eq, Ord, Show)

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
  | Fun f tp Location 
  | Pair (Expression f v tp) (Expression f v tp)  
  | Apply (Expression f v tp) (Expression f v tp)
--  | Lam v (Expression f v tp)  
  | LetP (Expression f v tp) ((v,tp),(v,tp)) (Expression f v tp)

data Equation f v tp = Equation { lhs :: Expression f v tp, rhs :: Expression f v tp }


type UntypedExpression f v = Expression f v ()
type UntypedEquation f v = Equation f v ()

-- ops
----------------------------------------------------------------------

funs :: Expression f v tp -> [f]
funs = flip funsDL []

fvars :: Eq v => Expression f v tp -> [v]
fvars = flip fvarsDL []

funsDL :: Expression f v tp -> [f] -> [f]
funsDL (Var _ _) = id
funsDL (Fun f _ _) = (:) f
funsDL (Pair t1 t2) = funsDL t2 . funsDL t1
funsDL (Apply t1 t2) = funsDL t2 . funsDL t1
funsDL (LetP t1 _ t2) = funsDL t2 . funsDL t1

fvarsDL :: Eq v => Expression f v tp -> [v] -> [v]
fvarsDL (Var v _) = (:) v
fvarsDL (Fun f _ _) = id
fvarsDL (Pair t1 t2) = fvarsDL t2 . fvarsDL t1
fvarsDL (Apply t1 t2) = fvarsDL t2 . fvarsDL t1
fvarsDL (LetP t1 ((x,_),(y,_)) t2) = (++) (filter (\ z -> z == x || z == y) (fvarsDL t2 [])) . fvarsDL t1
                                  
mapExpression :: (f -> tp -> Location -> (f',tp')) -> (v -> tp -> (v',tp')) -> Expression f v tp -> Expression f' v' tp'
mapExpression _ g (Var v tp) = uncurry Var (g v tp)
mapExpression f _ (Fun s tp l) = Fun s' tp' l where (s',tp') = f s tp l
mapExpression f g (Pair t1 t2) = Pair (mapExpression f g t1) (mapExpression f g t2)
mapExpression f g (Apply t1 t2) = Apply (mapExpression f g t1) (mapExpression f g t2)
mapExpression f g (LetP t1 ((x1,tp1),(x2,tp2)) t2) = LetP (mapExpression f g t1) (g x1 tp1,g x2 tp2) (mapExpression f g t2)

mapExpressionM :: Applicative m => (f -> tp -> Location -> m (f',tp')) -> (v -> tp -> m (v',tp')) -> Expression f v tp -> m (Expression f' v' tp')
mapExpressionM _ g (Var v tp) = uncurry Var <$> g v tp
mapExpressionM f _ (Fun s tp l) = fun <$> f s tp l where fun (s',tp') = Fun s' tp' l
mapExpressionM f g (Pair t1 t2) = Pair <$> mapExpressionM f g t1 <*> mapExpressionM f g t2
mapExpressionM f g (Apply t1 t2) = Apply <$> mapExpressionM f g t1 <*> mapExpressionM f g t2
mapExpressionM f g (LetP t1 ((x1,tp1),(x2,tp2)) t2) =
  LetP <$> mapExpressionM f g t1 <*> ((,) <$> g x1 tp1 <*> g x2 tp2) <*> mapExpressionM f g t2


sexpr :: Expression f v tp -> (Expression f v tp, [Expression f v tp])
sexpr (Apply t1 t2) = (h, rest ++ [t2]) where (h,rest) = sexpr t1
sexpr t = (t,[])

fromSexpr :: Expression f v tp -> [Expression f v tp] -> Expression f v tp
fromSexpr = foldl Apply

headSymbol :: Expression f v tp -> Maybe (f,tp)
headSymbol (Fun f tp _) = Just (f,tp)
headSymbol (Apply t1 _) = headSymbol t1
headSymbol Var {} = Nothing
headSymbol Pair {} = Nothing
headSymbol LetP {} = Nothing

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
  comma
  b <- pb
  return (a,b)

reservedWords :: [String]
reservedWords = words "let be in ; ="

-- parsers
------------------------------------------------------------

fun :: Symbol -> Parser (UntypedExpression Symbol Variable)
fun f = Fun f () <$> freshLocation

var :: Variable -> Parser (UntypedExpression Symbol Variable)
var v = return (Var v ())

lhsP :: Parser (UntypedExpression Symbol Variable)
lhsP = application (s <?> "function") arg where
  
  application h rest = foldl Apply <$> h <*> many rest
  
  hd = try c <|> parens (application hd arg)
  
  arg = try c <|> try v <|> parens (application arg arg)
  
  s = (symbol >>= fun) <?> "function symbol"
  
  c = (constructor >>= fun) <?> "constructor"
  
  v = (variable >>= var) <?> "variable"


rhsP :: [Variable] -> Parser (UntypedExpression Symbol Variable)
rhsP = expression where
  
  expression vs = foldl Apply <$> arg vs <*> many (arg vs)
  
  arg vs = l vs <|> try c <|> try (v vs) <|> try s <|> par vs
  
  par vs = foldr1 Pair <$> parens (expression vs `sepBy1` comma)
    
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
    return (LetP t1 ((v1,()),(v2,())) t2)

eqP :: Parser (UntypedEquation Symbol Variable)
eqP = do {l <- lhsP; lexeme (string "="); r <- rhsP (fvars l); return (Equation l r); } <?> "equation"

eqsP :: Parser [UntypedEquation Symbol Variable]
eqsP = do {rs <- eqP `endBy` sep; return rs} where
  sep = lexeme (string ";")


fromFile :: MonadIO m => FilePath -> m (Either ParseError [UntypedEquation Symbol Variable])
fromFile file = runParser parse 0 sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parse = many (try comment <|> whiteSpace1) *> (eqsP) <* eof


-- pretty printing
----------------------------------------------------------------------

-- instance PP.Pretty Symbol where pretty f = PP.bold (PP.text (symbolName f))
-- instance PP.Pretty Variable where pretty (Variable v) = PP.text v

ppTuple :: (PP.Pretty a, PP.Pretty b) => (a,b) -> PP.Doc
ppTuple (a,b) = PP.parens (ppSeq (PP.text ", ") [ PP.pretty a, PP.pretty b])

prettyExpression :: (f -> PP.Doc) -> (v -> PP.Doc) -> Expression f v tp -> PP.Doc
prettyExpression ppFun ppVar = pp id where
  pp _ (Var v _) = ppVar v
  pp _ (Fun f _ _) = ppFun f
  pp _ (Pair t1 t2) = ppTuple (prettyExpression ppFun ppVar t1, prettyExpression ppFun ppVar t2)
  pp par (Apply t1 t2) =
    par (pp id t1 PP.</> pp PP.parens t2)
  pp par (LetP t1 ((x,_),(y,_)) t2) =
    par (PP.align (PP.text "let" PP.<+> ppTuple (ppVar x, ppVar y) PP.<+> PP.text "=" PP.<+> pp id t1
                    PP.<$> PP.hang 3 (PP.text "in" PP.<+> pp id t2)))

prettyEquation :: (f -> PP.Doc) -> (v -> PP.Doc) -> Equation f v tp -> PP.Doc
prettyEquation ppFun ppVar eqn = pp (lhs eqn) PP.<+> PP.text "=" PP.</> pp (rhs eqn) where
  pp = prettyExpression ppFun ppVar

instance PP.Pretty Symbol where
  pretty f | defined f = PP.bold (PP.text (symName f))
           | otherwise = (PP.text (symName f))
                         
instance PP.Pretty Variable where pretty = PP.text . varName

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Expression f v tp) where
  pretty = prettyExpression PP.pretty PP.pretty
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Equation f v tp) where
  pretty = prettyEquation PP.pretty PP.pretty
