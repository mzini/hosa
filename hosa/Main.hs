{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import System.Console.CmdArgs
import Data.Typeable (Typeable)
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Applicative.Problem as P
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Data.Rewriting.Applicative.Term as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Except
import System.Exit

import HoSA.Utils
import qualified HoSA.CallSite as C
import qualified HoSA.Infer as I
import qualified HoSA.Index as Ix
import qualified HoSA.Solve as S
import qualified HoSA.SizeType as SzT

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: S.Solver
                 , mainIs :: Maybe [String]
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "width, i.e. number of extra variables, of size-types"
       , input = def &= typFile &= argPos 0
       , solver = S.MiniSmt &= help "SMT solver (minismt, z3)"
       , mainIs = Nothing &= help "Main function to analyse"
       , clength = 1 &= help "length of call-site contexts" }
  &= help "Infer size-types for given ATRS"

abstraction :: HoSA -> C.CSAbstract Symbol
abstraction cfg = C.kca (clength cfg)

data Error = ParseError P.ProblemParseError
           | SimpleTypeError String
           | SizeTypeError (I.TypingError Symbol Var)
           | ConstraintUnsolvable
           | NonSimpleApplicative (String,Int)

type RunM = ExceptT Error IO    

newtype Symbol = Symbol String deriving (Eq, Ord, Show)
newtype Var = Var String deriving (Eq, Ord, Show)

type Rule = R.ARule Symbol Var
type STATRS = ST.STAtrs Symbol Var

fromFile :: HoSA -> RunM [Rule]
fromFile cfg = do
  p <- lift (P.fromFile (input cfg) (`elem` ["app","@","."]))
  rs <- assertRight ParseError (P.allRules <$> P.rules <$> p)
  let ts = T.withArity `map` (RS.lhss rs ++ RS.rhss rs)
  case listToMaybe [ p | p <- foldr T.funsDL [] ts , snd p > 0 ] of
    Nothing -> return (R.mapSides (T.amap Symbol Var) `map` rs)
    Just p -> throwError (NonSimpleApplicative p)

inferSimpleTypes :: [Rule] -> RunM STATRS
inferSimpleTypes = assertRight SimpleTypeError . ST.fromATRS

generateConstraints :: HoSA -> STATRS -> RunM (SzT.Signature Symbol Ix.Term, [C.AnnotatedRule Symbol Var], [Ix.Constraint])
generateConstraints cfg stars = 
  lift (I.generateConstraints (abstraction cfg) (width cfg) (map Symbol <$> mainIs cfg) stars)
  >>= assertRight SizeTypeError
  
solveConstraints :: HoSA -> SzT.Signature Symbol Ix.Term -> [Ix.Constraint] -> RunM (SzT.Signature Symbol (S.Polynomial Integer))
solveConstraints cfg asig cs =
  S.solveConstraints (solver cfg) asig cs
  >>= assertJust ConstraintUnsolvable

status :: PP.Pretty e => String -> e -> RunM ()
status n e = lift (putDocLn (PP.text n PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

run :: IO (Either Error ())
run = runExceptT $ do
  cfg <- lift (cmdArgs defaultConfig)
  atrs <- fromFile cfg >>= inferSimpleTypes
  (asig,ars,cs) <- generateConstraints cfg atrs
  status "Considered ATRS" (PP.vcat [PP.pretty r | r <- ars]
                            PP.<$$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty (ST.signature atrs)))
  sig <- solveConstraints cfg asig cs
  status "Signature" sig
  return ()

main :: IO ()
main = run >>= exit where
  exit (Left e@SizeTypeError{}) = putDocLn e >> exitWith ExitSuccess
  exit (Left e) = putDocLn e >> exitWith (ExitFailure (-1))
  exit _ = exitWith ExitSuccess


-- pretty printers
instance PP.Pretty Symbol where pretty (Symbol n) = PP.bold (PP.text n)
instance PP.Pretty Var where pretty (Var n) = PP.text n



instance PP.Pretty Error where
  pretty (ParseError e) =
    PP.text "Error parsing ATRS, reason was:"
    PP.</> PP.indent 2 (ppErr e)
    where
      ppErr (P.SomeParseError pe) = PP.text (show pe)
      ppErr _ = PP.empty
  pretty (SimpleTypeError e) =
    PP.text "Error inferring simple types, reason was:"
    PP.</> PP.indent 2 (PP.text e)
  pretty (SizeTypeError e) =
    PP.text "Error inferring size types, reason was:"
    PP.</> PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = 
    PP.text "Constraints cannot be solved"
  pretty (NonSimpleApplicative (f,i)) =
    PP.text "ATRS contains non-constant symbol"
    PP.<+> PP.squotes (PP.text f) PP.<+> PP.text "of arity" PP.<+> PP.int i


