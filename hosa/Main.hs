{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import Data.Tree (drawForest, Forest)
import System.Console.CmdArgs
import Data.Typeable (Typeable)
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Data.Rewriting.Applicative.Problem as P
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import qualified Data.Rewriting.Applicative.Term as T
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (when)
import System.Exit

import HoSA.Utils
import HoSA.Parse (Term, Rule, Symbol (..), Variable (..), fromFile, ParseError)
import qualified HoSA.CallSite as C
import qualified HoSA.Infer as I
import qualified HoSA.Index as Ix
import qualified HoSA.Solve as S
import qualified HoSA.SizeType as SzT
import GUBS

deriving instance Typeable (SMTSolver)
deriving instance Data (SMTSolver)

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: SMTSolver
                 , verbose :: Bool
                 , mainIs :: Maybe [String]
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "width, i.e. number of extra variables, of size-types"
       , input = def &= typFile &= argPos 0
       , solver = MiniSmt &= help "SMT solver (minismt, z3)"
       , mainIs = Nothing &= help "Main function to analyse"
       , verbose = False                           
       , clength = 0 &= help "length of call-site contexts" }
  &= help "Infer size-types for given ATRS"

abstraction :: HoSA -> C.CSAbstract Symbol
abstraction cfg = C.kca (clength cfg)

constraintProcessor :: MonadIO m => HoSA -> S.Processor m
constraintProcessor cfg =
  try (smt' 0) ==> try (smt' 1) ==> smt' 2 where
  smt' = smt (solver cfg)
  -- simplify = propagateUp --exhaustive (propagateUp <=> propagateDown)

data Error = ParseError ParseError
           | SimpleTypeError String
           | SizeTypeError (I.TypingError Symbol Variable)
           | ConstraintUnsolvable

type RunM = ExceptT Error (ReaderT HoSA IO)    

type STATRS = ST.STAtrs Symbol Variable

putExecLog :: Forest String -> RunM ()
putExecLog l = do 
   v <- reader verbose
   when v (liftIO (putStrLn (drawForest l))) 


status :: PP.Pretty e => String -> e -> RunM ()
status n e = liftIO (putDocLn (PP.text n PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

readATRS :: RunM [Rule]
readATRS = reader input >>= fromFile >>= assertRight ParseError 

inferSimpleTypes :: [Rule] -> RunM STATRS
inferSimpleTypes = assertRight SimpleTypeError . ST.fromATRS

generateConstraints :: STATRS -> RunM (SzT.Signature Symbol Ix.Term, [C.AnnotatedRule Symbol Variable], [Ix.Constraint])
generateConstraints stars = do 
  abstr <- reader abstraction
  w <- reader width
  ms <- fmap (map Symbol) <$> reader mainIs
  (res,ars,l) <- liftIO (I.generateConstraints abstr w ms stars)
  putExecLog l
  (\(s,c) -> (s,ars,c)) <$> assertRight SizeTypeError res

solveConstraints ::  SzT.Signature Symbol Ix.Term -> [Ix.Constraint] -> RunM (SzT.Signature Symbol (S.Polynomial Integer))
solveConstraints asig cs = do 
  p <- reader constraintProcessor  
  (msig,l) <- S.solveConstraints p asig cs
  putExecLog l
  assertJust ConstraintUnsolvable msig

runHosa :: IO (Either Error ())
runHosa = do
  cfg <- cmdArgs defaultConfig
  flip runReaderT cfg $ runExceptT $ do
    atrs <- readATRS >>= inferSimpleTypes
    (asig,ars,cs) <- generateConstraints atrs
    status "Considered ATRS" (PP.vcat [PP.pretty r | r <- ars]
                           PP.<$$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty (ST.signature atrs)))
    sig <- solveConstraints asig cs
    status "Signature" sig
    return ()

main :: IO ()
main = runHosa >>= exit where
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


