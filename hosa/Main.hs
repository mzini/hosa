{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import Data.Tree (drawForest, Forest)
import System.Console.CmdArgs
import Data.Typeable (Typeable)
import Data.Traversable (traverse)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad (when, unless)
import System.Exit

import           Control.Arrow (second)
import qualified Data.Map as Map
import           HoSA.Utils
import           HoSA.Ticking
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram
import qualified HoSA.Data.CallSite as C
import qualified HoSA.SizeType.Infer as I
import qualified HoSA.Data.Index as Ix
import qualified HoSA.SizeType.SOConstraint as SOCS
import qualified HoSA.Data.SizeType as SzT
import           HoSA.Data.SizeType (SizeType (..), Schema, Type)
import GUBS hiding (Symbol, Variable, Var)

deriving instance Typeable (SMTSolver)
deriving instance Data (SMTSolver)

data SMTStrategy = Simple | SCC deriving (Show, Data, Typeable)
data AnalysisType = Time | Size deriving (Show, Data, Typeable)

data HoSA = HoSA { width :: Int
                 , clength :: Int
                 , solver :: SMTSolver
                 , verbose :: Bool
                 , mains :: Maybe [String]
                 -- , properSized :: Maybe [String]
                 , smtStrategy :: SMTStrategy
                 , analyse :: AnalysisType
                 , input :: FilePath}
          deriving (Show, Data, Typeable)

defaultConfig :: HoSA
defaultConfig =
  HoSA { width = 1 &= help "Sized-types width, i.e. number of extra variables"
       , input = def &= typFile &= argPos 0
       , solver = Z3 &= help "SMT solver (minismt, z3)."
       , mains = Nothing &= help "List of analysed main functions."
       -- , properSized  = Nothing &= help "Constructors with proper size annotation (defaults to all constructors)"
       , verbose = False
       , analyse = Size &= help "Analysis objective (size, time)."
       , smtStrategy = Simple  &= help "Constraint solving strategy (Simple, SCC)."
       , clength = 0 &= help "Length of call-site contexts." }
  &= help "Infer size-types for given ATRS"

abstraction :: HoSA -> C.CSAbstract f
abstraction cfg = C.kca (clength cfg)

startSymbols :: HoSA -> Maybe [Symbol]
startSymbols cfg = map sym <$> mains cfg where
  sym n = Symbol { symName = n, defined = True }
-- tickingFn :: HoSA -> ST.STAtrs Symbol Variable -> ST.STAtrs TSymbol TVariable
-- tickingFn (analyse -> Size) = ntickATRS
-- tickingFn (analyse -> Time) = tickATRS

-- sizedConstructors :: HoSA -> Maybe [TSymbol]
-- sizedConstructors (analyse -> Time) = Just [Tick]
-- sizedConstructors cfg = Nothing -- fmap (map TConstr) (properSized cfg)
                              
constraintProcessor :: MonadIO m => HoSA -> SOCS.Processor m
constraintProcessor cfg =
  case smtStrategy cfg of
    Simple -> logCS ==> try simplify ==> logCS ==> simple
    SCC -> logCS ==> try simplify ==> logCS ==> try (exhaustive (sccDecompose (try simplify ==> simple)))
  where
    logCS cs = logOpenConstraints cs >> return (Progress cs)
    simple =
      try (smt' defaultSMTOpts { degree = 1, maxCoeff = Just 1} )
      ==> try (smt' defaultSMTOpts { degree = 1 })
      ==> try (smt' defaultSMTOpts { degree = 2, maxCoeff = Just 1})
      ==> try (smt' defaultSMTOpts { degree = 2, shape = Mixed, maxCoeff = Just 2})      
    smt' = smt (solver cfg)
    simplify =
      try instantiate
      ==> try propagateEq
      ==> try (exhaustive (propagateUp <=> propagateDown))

data Error where
  ParseError :: ParseError -> Error
  SimpleTypeError :: (PP.Pretty f, PP.Pretty v) => TypingError f v -> Error
  SizeTypeError :: (PP.Pretty f, PP.Pretty v) => I.SzTypingError f v -> Error
  ConstraintUnsolvable :: Error

type RunM = ExceptT Error (ReaderT HoSA (UniqueT IO))

putExecLog :: Forest String -> RunM ()
putExecLog l = do 
   v <- reader verbose
   when v (liftIO (putStrLn (drawForest l))) 


status :: PP.Pretty e => String -> e -> RunM ()
status n e = liftIO (putDocLn (PP.text (n ++ ":") PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

readProgram :: RunM (TypedProgram Symbol Variable)
readProgram = reader input >>= fromFile >>= assertRight ParseError >>= inferTypes where
  inferTypes = assertRight SimpleTypeError . inferSimpleType

infer :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) => SzT.Signature f Ix.Term -> TypedProgram f v -> RunM (SzT.Signature f (SOCS.Polynomial Integer))
infer sig p = generateConstraints sig p >>= solveConstraints sig where
  generateConstraints sig p = do
    (res,l) <- lift (lift (I.generateConstraints sig p))
    putExecLog l
    assertRight SizeTypeError res
  solveConstraints sig cs = do 
    p <- reader constraintProcessor  
    (msig,l) <- lift (lift (SOCS.solveConstraints p sig cs))
    putExecLog l
    assertJust ConstraintUnsolvable msig
  

timeAnalysis :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  TypedProgram f v -> RunM (SzT.Signature (TSymbol f) (SOCS.Polynomial Integer))
timeAnalysis p = do
  w <- reader width
  let (ticked,aux) = tickProgram p
  let p' = ticked `progUnion` aux
  status "Instrumented Program" p'
  status "Auxiliary Equations" aux
  status "Abstract Signature" (abstractSignature w)
  infer (abstractSignature w) p'
  where
    -- TODO: move to Ticking code; run each generation in separate unique monad
    abstractSignature w = Map.fromList ((Tick, tickSchema) : functionDecls w)
    tickSchema = SzQArr [1] (SzBase Clock (Ix.bvar 1)) (SzBase Clock (Ix.Succ (Ix.bvar 1)))
    functionDecls w = runUnique (decls w `concatMapM` (Map.toList (signature p)))
    decls w (f,tp) = do
      (vs,t) <- open <$> I.abstractSchema w (auxType tp ar)
      let auxDecls = [ (TSymbol f (ar-i), close (auxDecl vs t i)) | i <- [0..ar-1]]
      if isDefined f
        then return auxDecls
        else return ((TConstr f, close (vs,constrDecl t)) : auxDecls)
        where
          ar = arity p f

          constrDecl :: Type Ix.Term -> Type Ix.Term
          constrDecl (SzArr _ (SzPair t _)) = t
          constrDecl (SzArr n t) = SzArr n (constrDecl t)
          constrDecl t = t

          -- TODO, use unique monad
          auxDecl :: [Ix.VarId] -> Type Ix.Term -> Int -> ([Ix.VarId],Type Ix.Term)
          auxDecl vs t 0 = (vs,t)
          auxDecl vs (SzArr n p) i = (vs', SzArr n (SzArr clock (SzPair p' clock)))
            where
              (vs', p') = auxDecl (v:vs) p (i-1)
              v = maximum (0:vs) + 1
              clock :: SizeType knd Ix.Term
              clock = SzBase Clock (Ix.bvar v)
          
          open :: Schema Ix.Term -> ([Ix.VarId], Type Ix.Term)
          open (SzBase bt ix) = ([], SzBase bt ix)
          open (SzQArr ixs n p) = (ixs, SzArr n p)

          close :: ([Ix.VarId], Type Ix.Term) -> Schema Ix.Term
          close (_, SzBase bt ix) = SzBase bt ix
          close (ixs, SzArr n p) = SzQArr ixs n p

sizeAnalysis :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  TypedProgram f v -> RunM (SzT.Signature f (SOCS.Polynomial Integer))
sizeAnalysis p = do
  w <- reader width
  infer (abstractSignature w) p
  where
    abstractSignature w = runUnique (traverse (I.abstractSchema w) (signature p))
  
prettyRS :: (PP.Pretty r, PP.Pretty f) => [r] -> Signature f -> PP.Doc
prettyRS rs sig = 
  PP.vcat [PP.pretty r | r <- rs]
  PP.<$$> PP.hang 2 (PP.text "where" PP.<$> PP.pretty sig)

runHosa :: IO (Either Error ())
runHosa = do
  cfg <- cmdArgs defaultConfig
  runUniqueT $ flip runReaderT cfg $ runExceptT $ do
    fs <- reader startSymbols
    abstr <- reader abstraction
    p <- C.withCallContexts abstr fs <$> readProgram
    status "Calling-context annotated program" (PP.pretty p)
    analysis <- reader analyse
    case analysis of
      Time -> timeAnalysis p >>= status "Timed Signature"
      Size -> sizeAnalysis p >>= status "Sized-Type Signature"      
    -- when (timeAnalysis 
    -- -- when (timeAnalysis cfg) $ status "Unticked ATRS" (prettyRS (ST.strlUntypedRule `map` ST.statrsRules input) (ST.statrsSignature input))
    -- (asig,ars,cs) <- generateConstraints statrs
    -- status "Considered ATRS" (prettyRS ars (ST.statrsSignature statrs))
    -- sig <- solveConstraints asig cs
    -- status "Signature" sig
    -- return ()

main :: IO ()
main = runHosa >>= exit where
  exit (Left e@SizeTypeError{}) = putDocLn e >> exitSuccess
  exit (Left e) = putDocLn e >> exitWith (ExitFailure (-1))
  exit _ = exitSuccess


-- pretty printers
   
instance PP.Pretty Error where
  pretty (ParseError e) = PP.indent 2 (PP.text (show e))
  pretty (SimpleTypeError e) = PP.indent 2 (PP.pretty e)
  pretty (SizeTypeError e) = PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = PP.text "Constraints cannot be solved"


