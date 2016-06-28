{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import Data.Tree (drawForest, Forest)
import System.Console.CmdArgs
import Data.Typeable (Typeable)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (when)
import System.Exit

import qualified Data.Map as M
import           HoSA.Utils
import           HoSA.Ticking
import           HoSA.Data.Rewriting
import qualified HoSA.Data.CallSite as C
import qualified HoSA.SizeType.Infer as I
import qualified HoSA.SizeType.Index as Ix
import qualified HoSA.Data.SimpleType as ST
import qualified HoSA.SizeType.SOConstraint as SOCS
import qualified HoSA.SizeType.Type as SzT
import GUBS hiding (Symbol, Variable, Var)

deriving instance Typeable (SMTSolver)
deriving instance Data (SMTSolver)

data SMTStrategy = Simple | SCC deriving (Show, Data, Typeable)

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: SMTSolver
                 , verbose :: Bool
                 , mainIs :: Maybe [String]
                 , smtStrategy :: SMTStrategy
                 , unticked :: Bool
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "width, i.e. number of extra variables, of size-types"
       , input = def &= typFile &= argPos 0
       , solver = MiniSmt &= help "SMT solver (minismt, z3)"
       , mainIs = Nothing &= help "Main function to analyse"
       , verbose = False
       , unticked = False
       , smtStrategy = Simple  &= help "SMT solver (simple, SCC)"
       , clength = 0 &= help "length of call-site contexts" }
  &= help "Infer size-types for given ATRS"

abstraction :: HoSA -> C.CSAbstract f
abstraction cfg = C.kca (clength cfg)

tickingFn :: HoSA -> ST.STAtrs Symbol Variable -> ST.STAtrs TSymbol TVariable
tickingFn cfg | unticked cfg = ntickATRS
              | otherwise = tickATRS
              
constraintProcessor :: MonadIO m => HoSA -> SOCS.Processor m
constraintProcessor cfg =
  case smtStrategy cfg of
    Simple -> try simplify ==> simple
    SCC -> try simplify ==> try (exhaustive (sccDecompose (try simplify ==> simple)))
  where
    simple = try (smt' 0) ==> try (smt' 1) ==> try (smt' 2)
    smt' = smt (solver cfg)
    simplify = exhaustive (propagateUp <=> propagateDown)

data Error = ParseError ParseError
           | SimpleTypeError (ST.TypingError Symbol Variable)
           | SizeTypeError (I.SzTypingError TSymbol TVariable)
           | ConstraintUnsolvable

type RunM = ExceptT Error (ReaderT HoSA (UniqueT IO))

putExecLog :: Forest String -> RunM ()
putExecLog l = do 
   v <- reader verbose
   when v (liftIO (putStrLn (drawForest l))) 


status :: PP.Pretty e => String -> e -> RunM ()
status n e = liftIO (putDocLn (PP.text n PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

readATRS :: RunM (ATRS Symbol Variable)
readATRS = reader input >>= fromFile >>= assertRight ParseError 

inferSimpleTypes :: ATRS Symbol Variable -> RunM (ST.STAtrs Symbol Variable)
inferSimpleTypes = assertRight SimpleTypeError . ST.inferSimpleType

generateConstraints :: ST.STAtrs TSymbol TVariable -> RunM (SzT.Signature TSymbol Ix.Term, [C.AnnotatedRule TSymbol TVariable], SOCS.SOCS)
generateConstraints stars = do 
  abstr <- reader abstraction
  w <- reader width
  ms <- return Nothing -- TODO fmap (map Symbol) <$> reader mainIs
  (res,ars,l) <- lift (lift (I.generateConstraints abstr w ms stars))
  putExecLog l
  (\(s,c) -> (s,ars,c)) <$> assertRight SizeTypeError res

solveConstraints ::  SzT.Signature TSymbol Ix.Term -> SOCS.SOCS -> RunM (SzT.Signature TSymbol (SOCS.Polynomial Integer))
solveConstraints asig cs = do 
  p <- reader constraintProcessor  
  (msig,l) <- lift (lift (SOCS.solveConstraints p asig cs))
  putExecLog l
  assertJust ConstraintUnsolvable msig

runHosa :: IO (Either Error ())
runHosa = do
  cfg <- cmdArgs defaultConfig
  runUniqueT $ flip runReaderT cfg $ runExceptT $ do
    tick <- reader tickingFn
    statrs <- tick <$> (readATRS >>= inferSimpleTypes)
    -- status "ATRS" (PP.pretty (ST.strlUntypedRule `map` ST.statrsRules statrs))
    -- status "Simple Type Signature" (PP.pretty (ST.statrsSignature statrs))
    (asig,ars,cs) <- generateConstraints statrs
    status "Considered ATRS" (PP.vcat [PP.pretty r | r <- ars]
                           PP.<$$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty (ST.statrsSignature statrs)))
    sig <- solveConstraints asig cs
    status "Signature" sig
    return ()

main :: IO ()
main = runHosa >>= exit where
  exit (Left e@SizeTypeError{}) = putDocLn e >> exitSuccess
  exit (Left e) = putDocLn e >> exitWith (ExitFailure (-1))
  exit _ = exitSuccess


-- pretty printers
   
instance PP.Pretty Error where
  pretty (ParseError e) =
    PP.indent 2 (PP.text (show e))
  pretty (SimpleTypeError e) =
    PP.indent 2 (PP.pretty e)
  pretty (SizeTypeError e) =
    PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = 
    PP.text "Constraints cannot be solved"


