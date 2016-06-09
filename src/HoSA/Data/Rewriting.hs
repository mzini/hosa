module HoSA.Data.Rewriting (
  -- * Types
  Variable (..)
  , Symbol (..)
  , Term (..)
  , Rule (..)
  , ATRS (..)
  -- * Operations
  , TermLike (..)
  , tmap
  , headSymbol
  , fvars
  , funs
  -- * Parsing
  , fromFile
  , ParseError
  -- * Typing
  , (:::)(..)
) where

import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import HoSA.Utils (ppSeq)

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

data Term f v =
  Var v
  | Fun f
  | Pair (Term f v) (Term f v)  
  | Apply (Term f v) (Term f v)
  | Let (Term f v) (v,v) (Term f v)

data Rule f v = Rule { lhs :: Term f v, rhs :: Term f v }

newtype ATRS f v = ATRS { rules :: [Rule f v] }

tmap :: (f -> f') -> (v -> v') -> Term f v -> Term f' v'
tmap _ g (Var v) = Var (g v)
tmap f _ (Fun s) = Fun (f s)
tmap f g (Pair t1 t2) = Pair (tmap f g t1) (tmap f g t2)
tmap f g (Apply t1 t2) = Apply (tmap f g t1) (tmap f g t2)
tmap f g (Let t1 (x1,x2) t2) = Let (tmap f g t1) (g x1,g x2) (tmap f g t2)

headSymbol :: Term f v -> Maybe f
headSymbol (Fun f) = Just f
headSymbol (Apply t1 _) = headSymbol t1
headSymbol Var {} = Nothing
headSymbol Pair {} = Nothing
headSymbol Let {} = Nothing


-- term like structures

class TermLike a where
  type S a  
  type V a
  funsDL :: a -> [S a] -> [S a]
  fvarsDL :: a -> [V a] -> [V a]

funs :: TermLike a => a -> [S a]
funs = flip funsDL []

fvars :: TermLike a => a -> [V a]
fvars = flip fvarsDL []

instance Eq v => TermLike (Term f v) where
  type S (Term f v) = f  
  type V (Term f v) = v
  
  funsDL (Var _) = id
  funsDL (Fun f) = (:) f
  funsDL (Pair t1 t2) = funsDL t2 . funsDL t1
  funsDL (Apply t1 t2) = funsDL t2 . funsDL t1
  funsDL (Let t1 _ t2) = funsDL t2 . funsDL t1

  fvarsDL (Var v) = (:) v
  fvarsDL (Fun f) = id
  fvarsDL (Pair t1 t2) = fvarsDL t2 . fvarsDL t1
  fvarsDL (Apply t1 t2) = fvarsDL t2 . fvarsDL t1
  fvarsDL (Let t1 (x,y) t2) = (++) (filter (\ z -> z == x || z == y) (fvarsDL t2 [])) . fvarsDL t1
                                  
instance Eq v => TermLike (Rule f v) where
  type S (Rule f v) = f  
  type V (Rule f v) = v
  funsDL rl = funsDL (lhs rl) . funsDL (rhs rl)
  fvarsDL rl = fvarsDL (lhs rl) . fvarsDL (rhs rl)  

instance Eq v => TermLike [Rule f v] where
  type S [Rule f v] = f
  type V [Rule f v] = v
  funsDL = flip (foldr funsDL)
  fvarsDL = flip (foldr fvarsDL)
  
instance Eq v => TermLike (ATRS f v) where
  type S (ATRS f v) = f
  type V (ATRS f v) = v
  funsDL = funsDL . rules
  fvarsDL = fvarsDL . rules
               
----------------------------------------------------------------------
-- Parsing
----------------------------------------------------------------------

newtype Symbol = Symbol String deriving (Eq, Ord, Show)
newtype Variable = Variable String deriving (Eq, Ord, Show)

type Parser = CharParser ()

fromFile :: MonadIO m => FilePath -> m (Either ParseError (ATRS Symbol Variable))
fromFile file = runParser parse () sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parse = many (try comment <|> whiteSpace1) *> (ATRS <$> rulesP) <* eof
  

-- lexing
----------------------------------------------------------------------

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
variable = Variable <$> identifier ((:) <$> lower <*> ident) <?> "variable"

constructor :: Parser Symbol
constructor = Symbol <$> identifier ((:) <$> (try upper <|> digit) <*> ident) <?> "constructor"

symbol :: Parser Symbol
symbol = Symbol <$> identifier ((:) <$> lower <*> ident) <?> "symbol"

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

-- parsers
----------------------------------------------------------------------

reservedWords :: [String]
reservedWords = words "let be in ; ="

lhsP :: Parser (Term Symbol Variable)
lhsP = application (s <?> "function") arg where
  
  application h rest = foldl Apply <$> h <*> many rest
  
  hd = try c <|> parens (application hd arg)
  
  arg = try c <|> try v <|> parens (application arg arg) -- <|> par where
    -- par = foldr1 Pair <$> parens (application arg arg `sepBy1` comma)
  
  s = (Fun <$> symbol) <?> "function symbol"
  
  c = (Fun <$> constructor) <?> "constructor"
  
  v = (Var <$> variable) <?> "variable"


rhsP :: [Variable] -> Parser (Term Symbol Variable)
rhsP = term where
  
  term vs = foldl Apply <$> arg vs <*> many (arg vs)
  
  arg vs = l vs <|> try c <|> try (v vs) <|> try s <|> par vs
  
  par vs = foldr1 Pair <$> parens (term vs `sepBy1` comma)
    
  c = (Fun <$> constructor) <?> "constructor"
  
  v vs = do
    x <- variable
    if x `elem` vs then return (Var x) else unexpected "variable expected."
    
  s = (Fun <$> symbol) <?> "function symbol"

  l vs = do
    try (reserved "let")
    t1 <- term vs
    reserved "be"
    (v1,v2) <- pair variable variable
    reserved "in"
    t2 <- term (v1 : v2 : vs)
    return (Let t1 (v1,v2) t2)

ruleP :: Parser (Rule Symbol Variable)
ruleP = do {l <- lhsP; lexeme (string "="); r <- rhsP (fvars l); return (Rule l r); } <?> "rule"

rulesP :: Parser [Rule Symbol Variable]
rulesP = do {rs <- ruleP `endBy` sep; return rs} where
  sep = lexeme (string ";")

  
-- pretty printing
----------------------------------------------------------------------

instance PP.Pretty Symbol where pretty (Symbol n) = PP.bold (PP.text n)
instance PP.Pretty Variable where pretty (Variable v) = PP.text v

ppTuple :: (PP.Pretty a, PP.Pretty b) => (a,b) -> PP.Doc
ppTuple (a,b) = PP.parens (ppSeq (PP.text ", ") [ PP.pretty a, PP.pretty b])


instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Term f v) where
  pretty = pp id where
    pp _ (Var v) = PP.pretty v
    pp _ (Fun f) = PP.pretty f
    pp _ (Pair t1 t2) = ppTuple (t1,t2)
    pp par (Apply t1 t2) =
      par (pp id t1 PP.</> pp PP.parens t2)
    pp par (Let t1 (x,y) t2) =
      par (PP.text "let" PP.<+> pp id t1
           PP.<+> PP.text "be" PP.<+> ppTuple (x,y)
           PP.<+> PP.text "in" PP.</> PP.pretty t2)
          
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Rule f v) where
  pretty rl = PP.pretty (lhs rl) PP.<+> PP.text "=" PP.</> PP.pretty (rhs rl)

----------------------------------------------------------------------
-- Typing
----------------------------------------------------------------------

data e ::: t = e ::: t
infixr 1 :::    



