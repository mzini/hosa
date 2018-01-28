module HoSA.Data.Program.Parse
  (
    Parser
  , ParseError
  , fromFile
  )

where

import Data.Char(digitToInt)
import Data.List(foldl')
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)

import qualified Data.Map as M
import Control.Monad (void)
import Control.Monad.IO.Class (MonadIO, liftIO)

import Data.Either (partitionEithers)
import Control.Arrow ((***))
import HoSA.Utils
import HoSA.Data.Program.Types
import HoSA.Data.Program.Expression
import HoSA.Data.MLTypes



----------------------------------------------------------------------
-- Parser Combinator
----------------------------------------------------------------------

type Parser = CharParser Location

freshLocation :: Parser Location
freshLocation = updateState succ >> getState

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
constructor = constr <$> identifier ((:) <$> (try upper <|> digit) <*> ident) <?> "constructor" where
  constr n = Symbol { symName = n, defined = False }

symbol :: Parser Symbol
symbol = defsym <$> identifier ((:) <$> lower <*> ident) <?> "symbol" where
  defsym n = Symbol { symName = n, defined = True }
  
parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))

comma :: Parser Char
comma = lexeme (char ',')

natural :: Parser Int
natural = foldl' (\a i -> a * 10 + digitToInt i) 0 <$> many1 digit

reserved :: String -> Parser ()
reserved = void . lexeme . string

ppair :: Parser a -> Parser b -> Parser (a,b)
ppair pa pb = parens $ do
  a <- pa
  _ <- comma
  b <- pb
  return (a,b)

reservedWords :: [String]
reservedWords = words "data if then else let be in ; = : [ ] :: -> |"

----------------------------------------------------------------------
-- parsers
----------------------------------------------------------------------

-- expressions

enil :: Location -> UntypedExpression Symbol v
enil = Fun NIL ()

econs :: Location -> UntypedExpression Symbol v
      -> UntypedExpression Symbol v -> UntypedExpression Symbol v
econs l h = Apply () (Apply () (Fun CONS () l) h)

fun :: Symbol -> Parser (UntypedExpression Symbol Variable)
fun f = Fun f () <$> freshLocation

var :: Variable -> Parser (UntypedExpression Symbol Variable)
var v = return (Var v ())

nilP :: Parser (UntypedExpression Symbol Variable)
nilP = reserved "[]" >> (enil <$> freshLocation)

consP :: Parser (UntypedExpression Symbol Variable)
consP = parens (reserved ":") >> (Fun CONS () <$> freshLocation)

lstP :: [UntypedExpression Symbol Variable] -> Parser (UntypedExpression Symbol Variable)
lstP [] = enil <$> freshLocation
lstP [e] = return e
lstP (e:es') = econs <$> freshLocation <*> return e <*> lstP es'

  
lhsP :: Parser (UntypedExpression Symbol Variable)
lhsP = application (s <?> "function") arg where
  
  application h rest = foldl (Apply ()) <$> h <*> many rest
  
  arg = (p `sepBy1` reserved ":") >>= lstP
  
  p = try nilP <|> try c <|> try v <|> par 

  par = foldr1 (Pair ((),())) <$> parens (application arg arg `sepBy1` comma)
  
  s = (symbol >>= fun) <?> "function symbol"
  
  c = (constructor >>= fun) <?> "constructor"
  
  v = (variable >>= var) <?> "variable"

rhsP :: [Variable] -> Parser (UntypedExpression Symbol Variable)
rhsP = expression where

  expression vs = (e `sepBy1` reserved ":") >>= lstP where
    e = foldl (Apply ()) <$> arg <*> many arg
    arg = i vs <|> l vs <|> try consP <|> try nilP <|> try c <|> try (v vs) <|> try s <|> par vs

  par vs = foldr1 (Pair ((),())) <$> parens (expression vs `sepBy1` comma)
    
  c = (constructor >>= fun) <?> "constructor"
  
  v vs = do
    x <- variable
    if x `elem` vs then return (Var x ()) else unexpected "variable expected."
    
  s = (symbol >>= fun) <?> "function symbol"

  i vs =
    If () <$> (try (reserved "if") >> expression vs)
          <*> (reserved "then" >> expression vs)
          <*> (reserved "else" >> expression vs)
    
  l vs = do
    try (reserved "let")
    t1 <- expression vs
    reserved "be"
    (v1,v2) <- ppair variable variable
    reserved "in"
    t2 <- expression (v1 : v2 : vs)
    return (LetP () t1 ((v1,()),(v2,())) t2)

choiceP :: [Variable] -> Parser (Distribution (UntypedExpression Symbol Variable))
choiceP vs = try multi <|> singleton where
  multi = between (lexeme (char '{')) (lexeme (char '}')) $ do
    cs <- flip sepEndBy1 (lexeme (char ';')) $ do
      p <- lexeme natural
      reserved ":"
      t <- rhsP vs
      return (p,t)
    let s = sum [p | (p,_) <- cs]
    return (Distribution s [(p, t) | (p,t) <- cs])
  singleton = (Distribution 1 . replicate 1 .(1,)) <$> rhsP vs
    

eqP :: Parser (UntypedEquation Symbol Variable)
eqP = do {l <- lhsP; reserved "="; r <- choiceP (fvars l); return (Equation l r); } <?> "equation"

eqsP :: Parser [UntypedEquation Symbol Variable]
eqsP = eqP `endBy1` reserved ";"

-- types

  
datatypeDeclP :: Parser (Environment Symbol)
datatypeDeclP = do
  reserved "data"
  n <- typeName
  vs <- many typeVarName
  let venv = runUnique $ sequence [(v,) . TyVar <$> unique | v <- vs]
      lhs = TyCon n [ v | (_,v) <- venv]
  reserved "="
  d <- M.fromList <$> constrDeclP lhs venv `sepBy` reserved "|"
  reserved ";"
  return d
  where
    typeVarName = identifier ((:) <$> lower <*> ident) <?> "variable"
    typeName = identifier ((:) <$> upper <*> ident) <?> "type name"

    constrDeclP lhs vs = do
      n <- constructor
      tpe <- foldr (:->) lhs <$> many (try tyVar <|> try dataTypeConst <|> tyParens)
      return (n, tpe)
        where
          typeP = tyFun <?> "type"
          tyFun = foldr1 (:->) <$> tyNFun `sepBy1` reserved "->"
          tyNFun = try dataType
                   <|> tyParens
                   <|> tyVar
          dataTypeConst = TyCon <$> typeName <*> return []
          dataType = TyCon <$> typeName <*> many typeP
          tyParens = foldr1 (:*:) <$> parens (typeP `sepBy1` comma)
          tyVar = do
            v <- typeVarName 
            case lookup v vs of
              Just vid -> return vid
              Nothing -> unexpected ("undeclared variable in data type declaration: " ++ show v)


-- 

fromFile :: MonadIO m => FilePath -> m (Either ParseError (Environment Symbol, [UntypedEquation Symbol Variable]))
fromFile file = runParser parser (uniqueFromInt 0) sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parser = cmts *> (flatten <$> decls) <* eof where
    cmts = many (try comment <|> whiteSpace1)
    decls =  many (try (Left <$> datatypeDeclP) <|> (Right <$> eqsP)) <* eof
    flatten = (M.unions *** concat) . partitionEithers
    






