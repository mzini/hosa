module HoSA.Parse (
  Variable (..)
  , Symbol (..)
  , Term
  , Rule
  , fromFile
  , ParseError
) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.Rule as R

newtype Symbol = Symbol String deriving (Eq, Ord, Show)
newtype Variable = Variable String deriving (Eq, Ord, Show)


type Term = T.ATerm Symbol Variable

type Rule = R.ARule Symbol Variable

type Parser = CharParser ()


fromFile :: MonadIO m => FilePath -> m (Either ParseError [Rule])
fromFile file = runParser parse () sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parse = many (try comment <|> whiteSpace1) *> rulesP <* eof
----------------------------------------------------------------------
-- lexing
----------------------------------------------------------------------

whiteSpace1 :: Parser String
whiteSpace1 = many1 ((space <|> tab <|> newline) <?> "whitespace")

comment :: Parser String
comment = (string "(*" >> manyTill anyChar (try (string "*)"))) <?> "comment"

lexeme :: Parser a -> Parser a
lexeme p = p <* many (try comment <|> whiteSpace1)

identifier :: Parser String -> Parser String
identifier = lexeme

ident :: Parser String
ident = many (try alphaNum <|> oneOf "'_/#?")

variable :: Parser Variable
variable = Variable <$> identifier ((:) <$> lower <*> ident) <?> "variable"

constructor :: Parser Symbol
constructor = Symbol <$> identifier ((:) <$> (try upper <|> digit) <*> ident) <?> "constructor"

symbol :: Parser Symbol
symbol = Symbol <$> identifier ((:) <$> lower <*> ident) <?> "variable"

parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))


----------------------------------------------------------------------
-- parsers
----------------------------------------------------------------------


lhsP :: Parser Term
lhsP = application (s <?> "function") where
  
  s = (T.fun <$> symbol <*> return []) <?> "function symbol"
  
  c = (T.fun <$> constructor <*> return []) <?> "constructor"
  
  v = (T.var <$> variable) <?> "variable"

  hd = try c <|> parens (application hd)
  
  arg = try c <|> try v <|> parens (application hd)
  
  application h = foldl T.app <$> h <*> many arg
         

rhsP :: [Variable] -> Parser Term
rhsP vs = term where
  term = foldl T.app <$> arg <*> many arg
  arg = try c <|> try v <|> try s <|> parens term
  c = (T.fun <$> constructor <*> return []) <?> "constructor"
  v = do
    x <- variable
    if x `elem` vs then return (T.var x) else unexpected "variable expected."
  s = (T.fun <$> symbol <*> return []) <?> "function symbol"

ruleP :: Parser Rule
ruleP = do {l <- lhsP; lexeme (string "="); r <- rhsP (T.vars l); return (R.Rule l r); } <?> "rule"

rulesP :: Parser [Rule]
rulesP = do {rs <- ruleP `endBy` sep; return rs} where
  sep = lexeme (string ";")
  
