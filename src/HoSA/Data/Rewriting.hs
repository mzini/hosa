module HoSA.Data.Rewriting (
  -- * Types
  Variable (..)
  , FunId (..)
  , Symbol (..)
  , Term
  , Rule
  , fun
  , tuple
  -- * Operations
  , module T
  , R.ARule
  , R.lhs
  , R.rhs
  , R.rule
  , rulesFuns
  -- * View
  , View (..)
  , view
  -- * Parsing
  , fromFile
  , ParseError
  -- * Typing
  , (:::)(..)
  , TypedTerm
  , TypedRule
  , unType
  , TView (..)
  , tview
  , tvar
  , tfun
  , ttuple
) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Text.Parsec
import Text.ParserCombinators.Parsec (CharParser)
import Data.Rewriting.Applicative.Term as T hiding (Term, aterm, atermM, AView (..), TConst, Var, fun)
import qualified Data.Rewriting.Applicative.Term as T
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import HoSA.Utils (ppSeq)


newtype FunId = FunId String deriving (Eq, Ord, Show)
              
data Symbol = Symbol FunId
            | Tuple deriving (Eq, Ord, Show)

newtype Variable = Variable String deriving (Eq, Ord, Show)


type Term = ATerm Symbol Variable

type Rule = R.ARule Symbol Variable

data View =
  Appl Term Term
  | Pair Term Term
  | Var Variable
  | Const FunId

view :: Term -> View
view (T.Var v) = Var v
view (T.Fun App [t1,t2]) = Appl t1 t2
view (T.Fun (Sym Tuple) [t1,t2]) = Pair t1 t2
view (T.Fun (Sym (Symbol f)) []) = Const f
view _ = error "Rewriting.view: Illformed applicative term"

fun :: FunId -> Term
fun f = T.fun (Symbol f) []
  
tuple :: Term -> Term -> Term
tuple a b = T.fun Tuple [a,b]

rulesFuns :: [R.ARule f v] -> [f]
rulesFuns = RS.funs

----------------------------------------------------------------------
-- Parsing
----------------------------------------------------------------------

type Parser = CharParser ()

fromFile :: MonadIO m => FilePath -> m (Either ParseError [Rule])
fromFile file = runParser parse () sn <$> liftIO (readFile file) where
  sn = "<file " ++ file ++ ">"
  parse = many (try comment <|> whiteSpace1) *> rulesP <* eof
  

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

constructor :: Parser FunId
constructor = FunId <$> identifier ((:) <$> (try upper <|> digit) <*> ident) <?> "constructor"

symbol :: Parser FunId
symbol = FunId <$> identifier ((:) <$> lower <*> ident) <?> "symbol"

parens :: Parser a -> Parser a
parens = between (char '(' >> notFollowedBy (char '*')) (lexeme (char ')'))

comma :: Parser Char
comma = lexeme (char ',')


-- parsers
----------------------------------------------------------------------

lhsP :: Parser Term
lhsP = application (s <?> "function") arg where
  
  application h rest = foldl app <$> h <*> many rest
  
  hd = try c <|> parens (application hd arg)
  
  arg = try c <|> try v <|> par where
    par = foldr1 tuple <$> parens (application arg arg `sepBy1` comma)
  
  s = (fun <$> symbol) <?> "function symbol"
  
  c = (fun <$> constructor) <?> "constructor"
  
  v = (var <$> variable) <?> "variable"


rhsP :: [Variable] -> Parser Term
rhsP vs = term where
  term = foldl app <$> arg <*> many arg
  
  arg = try c <|> try v <|> try s <|> par where
    par = foldr1 tuple <$> parens (term `sepBy1` comma)
    
  c = (fun <$> constructor) <?> "constructor"
  
  v = do
    x <- variable
    if x `elem` vs then return (T.var x) else unexpected "variable expected."
    
  s = (fun <$> symbol) <?> "function symbol"

ruleP :: Parser Rule
ruleP = do {l <- lhsP; lexeme (string "="); r <- rhsP (vars l); return (R.Rule l r); } <?> "rule"

rulesP :: Parser [Rule]
rulesP = do {rs <- ruleP `endBy` sep; return rs} where
  sep = lexeme (string ";")

  
-- pretty printing
----------------------------------------------------------------------

instance PP.Pretty FunId where pretty (FunId n) = PP.bold (PP.text n)
instance PP.Pretty Variable where pretty (Variable v) = PP.text v

instance {-# OVERLAPPING  #-} PP.Pretty Term where
  pretty = pp id where
    pp _ (view -> Var v) = PP.pretty v
    pp _ (view -> Const f) = PP.pretty f
    pp _ (view -> Pair t1 t2) = 
      PP.parens (ppSeq (PP.text ", ") [ pp id t1, pp id t2])
    pp par (view -> Appl t1 t2) =
      par (pp id t1 PP.</> pp PP.parens t2)
          
instance {-# OVERLAPPING  #-} PP.Pretty Rule where
  pretty rl = PP.pretty (R.lhs rl) PP.<+> PP.text "=" PP.</> PP.pretty (R.rhs rl)

----------------------------------------------------------------------
-- Typing
----------------------------------------------------------------------

data e ::: t = e ::: t
infixr 1 :::


type TypedTerm tps tpv = ATerm (Symbol ::: tps) (Variable ::: tpv)
type TypedRule tps tpv = R.ARule (Symbol ::: tps) (Variable ::: tpv)

data TView tps tpv =
  TAppl (TypedTerm tps tpv) (TypedTerm tps tpv)
  | TPair (TypedTerm tps tpv) (TypedTerm tps tpv)
  | TVar (Variable ::: tpv)
  | TConst (FunId ::: tps)

unType :: TypedTerm tps tpv -> Term
unType = amap drp drp where drp (f ::: _) = f

    
tview :: TypedTerm tps tpv -> TView tps tpv
tview (T.Var x) = TVar x
tview (T.Fun (Sym (Symbol f ::: tp)) []) = TConst (f ::: tp)
tview (T.Fun (Sym (Tuple ::: _)) [t1,t2]) = TPair t1 t2
tview (T.Fun App [t1,t2]) = TAppl t1 t2

tvar :: Variable -> tpv -> TypedTerm tps tpv
tvar v tp = T.var (v ::: tp)

tfun :: FunId -> tps -> TypedTerm tps tpv
tfun f tp = T.fun (Symbol f ::: tp) []
  
ttuple :: TypedTerm tps tpv -> TypedTerm tps tpv -> tps -> TypedTerm tps tpv
ttuple a b tp = T.fun (Tuple ::: tp) [a,b]



