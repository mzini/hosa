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
import HoSA.Parse (Term, Rule, Symbol (..), Variable (..), fromFile, ParseError)
import qualified HoSA.CallSite as C
import qualified HoSA.Infer as I
import qualified HoSA.Index as Ix
import qualified HoSA.Solve as S
import qualified HoSA.SizeType as SzT
import qualified GUBS as GUBS

deriving instance Typeable (GUBS.SMTSolver)
deriving instance Data (GUBS.SMTSolver)

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: GUBS.SMTSolver
                 , mainIs :: Maybe [String]
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "width, i.e. number of extra variables, of size-types"
       , input = def &= typFile &= argPos 0
       , solver = GUBS.MiniSmt &= help "SMT solver (minismt, z3)"
       , mainIs = Nothing &= help "Main function to analyse"
       , clength = 1 &= help "length of call-site contexts" }
  &= help "Infer size-types for given ATRS"

abstraction :: HoSA -> C.CSAbstract Symbol
abstraction cfg = C.kca (clength cfg)

data Error = ParseError ParseError
           | SimpleTypeError String
           | SizeTypeError (I.TypingError Symbol Variable)
           | ConstraintUnsolvable

type RunM = ExceptT Error IO    

type STATRS = ST.STAtrs Symbol Variable

atrsFromFile :: HoSA -> RunM [Rule]
atrsFromFile cfg = fromFile (input cfg) >>= assertRight ParseError 

inferSimpleTypes :: [Rule] -> RunM STATRS
inferSimpleTypes = assertRight SimpleTypeError . ST.fromATRS

generateConstraints :: HoSA -> STATRS -> RunM (SzT.Signature Symbol Ix.Term, [C.AnnotatedRule Symbol Variable], [Ix.Constraint])
generateConstraints cfg stars = 
  lift (I.generateConstraints (abstraction cfg) (width cfg) (map Symbol <$> mainIs cfg) stars)
  >>= assertRight SizeTypeError

constraintProcessor :: MonadIO m => HoSA -> S.Processor m
constraintProcessor cfg =
  try (smt 0) GUBS.>=> try (smt 1) GUBS.>=> smt 2 where
  smt = GUBS.smt (solver cfg)
  try = GUBS.try

solveConstraints :: HoSA -> SzT.Signature Symbol Ix.Term -> [Ix.Constraint] -> RunM (SzT.Signature Symbol (S.Polynomial Integer))
solveConstraints cfg asig cs =
  S.solveConstraints (constraintProcessor cfg) asig cs
  >>= assertJust ConstraintUnsolvable where

status :: PP.Pretty e => String -> e -> RunM ()
status n e = lift (putDocLn (PP.text n PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

run :: IO (Either Error ())
run = runExceptT $ do
  cfg <- lift (cmdArgs defaultConfig)
  atrs <- atrsFromFile cfg >>= inferSimpleTypes
  (asig,ars,cs) <- generateConstraints cfg atrs
  status "Considered ATRS" (PP.vcat [PP.pretty r | r <- ars]
                            PP.<$$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty (ST.signature atrs)))
  sig <- solveConstraints cfg asig cs
  status "Signature" sig
  return ()

main :: IO ()
main = run >>= exit where
  exit (Left e@SizeTypeError{}) = putDocLn e >> exitSuccess
  exit (Left e) = putDocLn e >> exitWith (ExitFailure (-1))
  exit _ = exitSuccess


-- pretty printers
instance PP.Pretty Symbol where pretty (Symbol n) = PP.bold (PP.text n)
instance PP.Pretty Variable where pretty (Variable n) = PP.text n



instance PP.Pretty Error where
  pretty (ParseError e) =
    PP.text "Error parsing ATRS, reason was:"
    PP.</> PP.indent 2 (PP.text (show e))
  pretty (SimpleTypeError e) =
    PP.text "Error inferring simple types, reason was:"
    PP.</> PP.indent 2 (PP.text e)
  pretty (SizeTypeError e) =
    PP.text "Error inferring size types, reason was:"
    PP.</> PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = 
    PP.text "Constraints cannot be solved"
  -- pretty (NonSimpleApplicative (f,i)) =
  --   PP.text "ATRS contains non-constant symbol"
  --   PP.<+> PP.squotes (PP.text f) PP.<+> PP.text "of arity" PP.<+> PP.int i


