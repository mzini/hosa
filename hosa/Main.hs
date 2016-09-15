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

import           Control.Arrow (first,second)
import qualified Data.Map as Map
import qualified Data.Set as Set
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

-- abstract schemas
----------------------------------------------------------------------

freshIxTerm :: MonadUnique m => Set.Set Ix.VarId -> m Ix.Term
freshIxTerm vs = do
  f <- Ix.Sym Nothing <$> unique
  return (Ix.Fun f (Ix.bvar `map` Set.toList vs))
  
close :: (Set.Set Ix.VarId, Set.Set Ix.VarId, Type Ix.Term) -> Schema Ix.Term
close (_, _, SzBase bt ix) = SzBase bt ix
close (vs1, vs2, SzArr n p) = SzQArr (Set.toList (vs1 `Set.union` vs2)) n p

freshVarIds :: MonadUnique m => Int -> m [Ix.VarId]
freshVarIds n = map uniqueToInt <$> uniques n


abstractSchema :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Schema Ix.Term)
abstractSchema width f tp = close <$> abstractType width f tp

abstractType :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Set.Set Ix.VarId, Set.Set Ix.VarId, Type Ix.Term)
abstractType width f = runUniqueT . annotatePositive 0 Set.empty
  where
    annotateBaseType vs bt = SzBase bt <$> lift (freshIxTerm vs)

    -- returns: negative free variables, positive free variables, type
    annotatePositive w vs (TyBase bt) = do
      is <- freshVarIds w
      let vs' = Set.fromList is `Set.union` vs
      (Set.empty, vs',) <$> annotateBaseType vs' bt
    annotatePositive w vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotatePositive w vs tp1
      (fvsn2, fvsp2, t2) <- annotatePositive w vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    annotatePositive w vs (n :-> p) = annotateArr w vs n p
    
    -- returns: free variables, schema
    annotateNegative _ (TyBase bt) = do
      [i] <- freshVarIds 1
      return (Set.singleton i, SzBase bt (Ix.bvar i))
    annotateNegative vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr width vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')
    
    -- returns: negative free variables, positive free variables, type
    annotateArr w vs n p = do
      (fvsn, n') <- annotateNegative vs n
      (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
      return (fvsn `Set.union` nvsp, pvsp, SzArr n' p')        

abstractTimeSchema :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Schema Ix.Term)
abstractTimeSchema width f tp = close <$> abstractTimeType width f tp

abstractTimeType :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Set.Set Ix.VarId, Set.Set Ix.VarId, Type Ix.Term)
abstractTimeType width f = runUniqueT . annotatePositive 0 Set.empty
  where
    annotateBaseType vs bt = SzBase bt <$> lift (freshIxTerm vs)

    -- returns: negative free variables, positive free variables, type
    annotatePositive w vs (TyBase bt) = do
      is <- freshVarIds w
      let vs' = Set.fromList is `Set.union` vs
      (Set.empty, vs',) <$> annotateBaseType vs' bt
    annotatePositive w vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotatePositive w vs tp1
      (fvsn2, fvsp2, t2) <- annotatePositive w vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    -- annotatePositive w vs (n :-> p@TyBase{}) = do
    --   (fvsn, n') <- annotateNegative vs n
    --   (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
    --   [i] <- freshVarIds 1
    --   let ci = SzBase Clock (Ix.bvar i)
    --   co <- annotateBaseType (Set.insert i pvsp) Clock
    --   return (Set.insert i (fvsn `Set.union` nvsp), Set.insert i pvsp, SzArr n' (SzArr ci (SzPair p' co)))
    annotatePositive w vs (n :-> p) = annotateArr w vs n p
    
    -- returns: free variables, schema
    annotateNegative _ (TyBase bt) = do
      [i] <- freshVarIds 1
      return (Set.singleton i, SzBase bt (Ix.bvar i))
    annotateNegative vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr width vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')
    

    -- returns: negative free variables, positive free variables, type
    annotateArr w vs n p = do
      (fvsn, n') <- annotateNegative vs n
      (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
      [i] <- freshVarIds 1
      let ci = SzBase Clock (Ix.bvar i)
      co <- case p of
              _ :-> _             -> return (SzBase Clock (Ix.bvar i))
              _ | isConstructor f -> return (SzBase Clock (Ix.bvar i))
              _                   -> annotateBaseType (Set.insert i pvsp) Clock
      return (Set.insert i (fvsn `Set.union` nvsp), Set.insert i pvsp, SzArr n' (SzArr ci (SzPair p' co)))


-- execution monad
----------------------------------------------------------------------
data Error where
  ParseError :: ParseError -> Error
  SimpleTypeError :: (PP.Pretty f, PP.Pretty v) => TypingError f v -> Error
  SizeTypeError :: (PP.Pretty f, PP.Pretty v) => I.SzTypingError f v -> Error
  ConstraintUnsolvable :: Error

instance PP.Pretty Error where
  pretty (ParseError e) = PP.indent 2 (PP.text (show e))
  pretty (SimpleTypeError e) = PP.indent 2 (PP.pretty e)
  pretty (SizeTypeError e) = PP.indent 2 (PP.pretty e)
  pretty ConstraintUnsolvable = PP.text "Constraints cannot be solved"


type RunM = ExceptT Error (ReaderT HoSA (UniqueT IO))

putExecLog :: Forest String -> RunM ()
putExecLog l = do 
   v <- reader verbose
   when v (liftIO (putStrLn (drawForest l))) 


status :: PP.Pretty e => String -> e -> RunM ()
status n e = liftIO (putDocLn (PP.text (n ++ ":") PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

-- commands
----------------------------------------------------------------------

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
  status "Instrumented Program" ticked
  status "Auxiliary Equations" aux
  status "Abstract Signature" (abstractSignature w) -- TODO
  infer (abstractSignature w) (ticked `progUnion` aux)
  where
    abstractSignature w = Map.fromList ((Tick, tickSchema) : functionDecls w)
    tickSchema = SzQArr [1] (SzBase Clock (Ix.bvar 1)) (SzBase Clock (Ix.Succ (Ix.bvar 1)))
    functionDecls w = runUnique (decls w `concatMapM` (Map.toList (signature p)))
    decls w (f,tp) = do
      (fvsn,fvsp,t) <- abstractTimeType w f tp
      let auxDecls = [(TSymbol f (i+1), close (fvsn,fvsp, suite t i)) | i <- [0 .. ar-1]]
      if isDefined f
        then return auxDecls
        else return ((TConstr f, close (fvsn,fvsp,suite t ar)) : auxDecls)
        where
          suite t 0 = t
          suite (SzArr n (SzArr _ (SzPair p _))) i = SzArr n (suite p (i-1))
          ar = arity p f
          
      -- (vs,t) <- open <$> undefined w (auxType tp ar) --TODO
      -- let auxDecls = [ (TSymbol f (ar-i), close (auxDecl vs t i)) | i <- [0..ar-1]]
      -- if isDefined f
      --   then return auxDecls
      --   else return ((TConstr f, close (vs,constrDecl t)) : auxDecls)
      --   where
      --     ar = arity p f

      --     constrDecl :: Type Ix.Term -> Type Ix.Term
      --     constrDecl (SzArr _ (SzPair t _)) = t
      --     constrDecl (SzArr n t) = SzArr n (constrDecl t)
      --     constrDecl t = t

      --     -- TODO, use unique monad
      --     auxDecl :: [Ix.VarId] -> Type Ix.Term -> Int -> ([Ix.VarId],Type Ix.Term)
      --     auxDecl vs t 0 = (vs,t)
      --     auxDecl vs (SzArr n p) i = (vs', SzArr n (SzArr clock (SzPair p' clock)))
      --       where
      --         (vs', p') = auxDecl (v:vs) p (i-1)
      --         v = maximum (0:vs) + 1
      --         clock :: SizeType knd Ix.Term
      --         clock = SzBase Clock (Ix.bvar v)
          
      --     open :: Schema Ix.Term -> ([Ix.VarId], Type Ix.Term)
      --     open (SzBase bt ix) = ([], SzBase bt ix)
      --     open (SzQArr ixs n p) = (ixs, SzArr n p)

      --     close :: ([Ix.VarId], Type Ix.Term) -> Schema Ix.Term
      --     close (_, SzBase bt ix) = SzBase bt ix
      --     close (ixs, SzArr n p) = SzQArr ixs n p

sizeAnalysis :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  TypedProgram f v -> RunM (SzT.Signature f (SOCS.Polynomial Integer))
sizeAnalysis p = do
  w <- reader width
  status "Abstract Signature" (abstractSignature w) -- TODO  
  infer (abstractSignature w) p
  where
    abstractSignature w = runUnique (Map.traverseWithKey (abstractSchema w) (signature p))
  
main :: IO ()
main = do
  cfg <- cmdArgs defaultConfig
  r <- runUniqueT $ flip runReaderT cfg $ runExceptT $ do
    fs <- reader startSymbols
    abstr <- reader abstraction
    p <- C.withCallContexts abstr fs <$> readProgram
    status "Calling-context annotated program" (PP.pretty p)
    analysis <- reader analyse
    case analysis of
      Time -> timeAnalysis p >>= status "Timed Signature"
      Size -> sizeAnalysis p >>= status "Sized-Type Signature"
  case r of
    Left e@SizeTypeError{} -> putDocLn e >> exitSuccess
    Left e -> putDocLn e >> exitWith (ExitFailure (-1))
    _ -> exitSuccess


