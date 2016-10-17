{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import           Control.Arrow (first,second)
import           Control.Monad (when, unless)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import           Data.Traversable (traverse)
import           Data.Tree (drawForest, Forest, Tree (..))
import           Data.Typeable (Typeable)
import           System.Console.CmdArgs
import           System.Exit
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (nub)

import           HoSA.Utils
import           HoSA.Ticking
import           HoSA.Data.Program
import           HoSA.Data.MLTypes
import qualified HoSA.SizeType.Infer as I
import qualified HoSA.Data.Index as Ix
import qualified HoSA.SizeType.SOConstraint as SOCS
import qualified HoSA.Data.SizeType as SzT
import           HoSA.Data.SizeType (SizeType (..), Schema, Type)
import           GUBS hiding (Symbol, Variable, Var, definedSymbol)

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
  HoSA { width = 1 &= help "Sized-types width, i.e. number of extra variables. Defaults to 1."
       , input = def &= typFile &= argPos 0
       , solver = Z3 &= help "SMT solver (minismt, z3). Defaults to z3."
       , mains = Nothing &= help "List of analysed main functions."
       , verbose = False
       , analyse = Size &= help "Analysis objective (size, time)."
       , smtStrategy = SCC  &= help "Constraint solving strategy (Simple, SCC). Defaults to SCC."
       , clength = 1 &= help "Length of call-site contexts. Defaults to 1." }
  &= help "Infer size-types for given ATRS"

abstraction :: Eq f => HoSA -> CSAbstract f
abstraction cfg = kca (clength cfg)

startSymbols :: HoSA -> Maybe [Symbol]
startSymbols cfg = map sym <$> mains cfg where
  sym n = Symbol { symName = n, defined = True }
                              
constraintProcessor :: MonadIO m => HoSA -> SOCS.Processor m
constraintProcessor cfg =
  case smtStrategy cfg of
    Simple -> logCS ==> try simplify ==> logCS ==> simple
    SCC -> logCS ==> try simplify ==> logCS ==> try (exhaustive (sccDecompose (logCS ==> try simplify ==> simple)))
  where
    logCS cs = logOpenConstraints cs >> return (Progress cs)
    logStr str cs = logMsg str >> return (Progress cs)
    simple =
      logStr "SMT: trying strongly linear interpretation"
      ==> try (smt' defaultSMTOpts { degree = 1, maxCoeff = Just 1} )
      ==> logStr "SMT: trying linear interpretation"      
      ==> try (smt' defaultSMTOpts { degree = 1 })
      ==> logStr "SMT: trying strongly multmixed interpretation"            
      ==> try (smt' defaultSMTOpts { degree = 2, maxCoeff = Just 1})
      ==> logStr "SMT: trying multmixed interpretation"            
      ==> try (smt' defaultSMTOpts { degree = 2, maxCoeff = Nothing})
      ==> logStr "SMT: trying mixed interpretation"                  
      ==> try (smt' defaultSMTOpts { degree = 2, shape = Mixed, maxCoeff = Nothing})      
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
  
close :: Type Ix.Term -> Schema Ix.Term
close (SzVar v)       = SzVar v
close (SzCon n ts ix) = SzCon n ts ix
close (SzPair t1 t2)  = SzPair (close t1) (close t2)
close t@(SzArr n p)   = SzQArr (Set.toList (bvs t)) n p where
  bvs :: SizeType knd Ix.Term -> Set.Set Ix.VarId
  bvs (SzVar _) = Set.empty
  bvs (SzCon _ ts ix) = Set.fromList (Ix.bvars ix) `Set.union` Set.unions [bvs t | t <- ts]
  bvs (SzPair t1 t2) = bvs t1 `Set.union` bvs t2
  bvs (SzArr n p) = bvs n `Set.union` bvs p
  bvs (SzQArr ixs n p) = (bvs n `Set.union` bvs p) Set.\\ Set.fromList ixs


freshVarIds :: MonadUnique m => Int -> m [Ix.VarId]
freshVarIds n = map uniqueToInt <$> uniques n

freshVarId :: MonadUnique m => m Ix.VarId
freshVarId = uniqueToInt <$> unique

abstractSchema :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Schema Ix.Term)
abstractSchema width f tp = close <$> abstractType width f tp

abstractType :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Type Ix.Term)
abstractType width f stp = thrd <$> runUniqueT (annotatePositive 0 Set.empty stp)
  where
    thrd (_,_,c) = c
    -- returns: negative free variables, positive free variables, type
    annotatePositive _ _  (TyVar v) = return (Set.empty, Set.empty, SzVar v)    
    annotatePositive w vs (TyCon n ts) = do
      (fvsn,fvsp,as) <- foldM (\ (fvsn,fvsp,as) t -> do
                                  (fvsn', fvsp', a) <- annotatePositive w vs t
                                  return (fvsn' `Set.union` fvsn'
                                         , fvsp' `Set.union` fvsp'
                                         , as ++ [SzT.toSchema a]))
                              (Set.empty,Set.empty,[])
                              ts
      is <- freshVarIds w
      let vs' = Set.fromList is `Set.union` vs
      ix <- if isDefined f
            then lift (freshIxTerm vs')
            else return (Ix.ixSucc (Ix.ixSum [Ix.bvar v | v <- Set.toList vs']))
      return (fvsp, vs' `Set.union` fvsp,SzCon n as ix)
    annotatePositive w vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotatePositive w vs tp1
      (fvsn2, fvsp2, t2) <- annotatePositive w vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    annotatePositive w vs (n :-> p) = annotateArr w vs n p
    
    -- returns: free variables, schema
    annotateNegative _ (TyVar v) = return (Set.empty, SzVar v)
    annotateNegative vs (tp1 :*: tp2) = do
      (fvs1, s1) <- annotateNegative vs tp1
      (fvs2, s2) <- annotateNegative vs tp2
      return (fvs1 `Set.union` fvs2, SzPair s1 s2)
    annotateNegative vs (TyCon n ts) = do
      (fvs,as) <- foldM (\ (fvs,as) t -> do
                            (fvs', a) <- annotateNegative vs t
                            return (fvs' `Set.union` fvs, as ++ [a]))
                        (Set.empty,[])
                        ts
      i <- freshVarId
      return (Set.insert i fvs, SzCon n as (Ix.bvar i))
    annotateNegative vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr width vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')
    
    -- returns: negative free variables, positive free variables, type
    annotateArr w vs n p = do
      (fvsn, n') <- annotateNegative Set.empty n
      (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
      return (fvsn `Set.union` nvsp, pvsp, SzArr n' p')        

abstractTimeType :: (IsSymbol f, MonadUnique m) => Int -> f -> SimpleType -> m (Type Ix.Term, Ix.VarId)
abstractTimeType width f stp = first thrd <$> runUniqueT ((,) <$> annotatePositive 0 Set.empty stp <*> freshVarId)
  where
    thrd (_,_,c) = c
    clock = SzCon "#" []
    -- returns: negative free variables, positive free variables, type
    annotatePositive _ _  (TyVar v) = return (Set.empty, Set.empty, SzVar v)    
    annotatePositive w vs (TyCon n ts) = do
      (fvsn,fvsp,as) <- foldM (\ (fvsn,fvsp,as) t -> do
                                  (fvsn', fvsp', a) <- annotatePositive w vs t
                                  return (fvsn' `Set.union` fvsn'
                                         , fvsp' `Set.union` fvsp'
                                         , as ++ [SzT.toSchema a]))
                              (Set.empty,Set.empty,[])
                              ts
      is <- freshVarIds w
      let vs' = Set.fromList is `Set.union` vs
      ix <- if isDefined f
            then lift (freshIxTerm vs')
            else return (Ix.ixSucc (Ix.ixSum [Ix.bvar v | v <- Set.toList vs']))
      return (fvsp, vs' `Set.union` fvsp,SzCon n as ix)
    annotatePositive w vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotatePositive w vs tp1
      (fvsn2, fvsp2, t2) <- annotatePositive w vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    annotatePositive w vs (n :-> p) = annotateArr w vs n p
    
    -- returns: free variables, schema
    annotateNegative _ (TyVar v) = return (Set.empty, SzVar v)
    annotateNegative vs (tp1 :*: tp2) = do
      (fvs1, s1) <- annotateNegative vs tp1
      (fvs2, s2) <- annotateNegative vs tp2
      return (fvs1 `Set.union` fvs2, SzPair s1 s2)
    annotateNegative vs (TyCon n ts) = do
      (fvs,as) <- foldM (\ (fvs,as) t -> do
                            (fvs', a) <- annotateNegative vs t
                            return (fvs' `Set.union` fvs, as ++ [a]))
                        (Set.empty,[])
                        ts
      i <- freshVarId
      return (Set.insert i fvs, SzCon n as (Ix.bvar i))
    annotateNegative vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr width vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')

    -- returns: negative free variables, positive free variables, type
    annotateArr w vs n p = do
      (fvsn, n') <- annotateNegative vs n
      (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
      i <- freshVarId
      let ci = clock (Ix.bvar i)
      co <- case p of
        _ :-> _             -> return (clock (Ix.bvar i))
        _ | isConstructor f -> return (clock (Ix.bvar i))
        _                   -> do
          ix <- lift (freshIxTerm pvsp)
          return (clock (Ix.ixSum [ix,Ix.bvar i]))
          -- lift (clock <$> (freshIxTerm (Set.insert i pvsp)))
      return (Set.insert i (fvsn `Set.union` nvsp)
             , Set.insert i pvsp
             , SzArr n' (SzArr ci (SzPair p' co)))


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

putExecLog :: PP.Pretty d => Forest d -> RunM ()
putExecLog l = do 
   v <- reader verbose
   when v (liftIO (putDocLn (ppForest l)))

status :: PP.Pretty e => String -> e -> RunM ()
status n e = liftIO (putDocLn (PP.text (n ++ ":") PP.<$> PP.indent 2 (PP.pretty e)) >> putStrLn "")

ppForest :: PP.Pretty p => Forest p -> PP.Doc
ppForest ts = PP.vcat [PP.text "+" PP.<+> ppTree t | t <- ts]

ppTree :: PP.Pretty p => Tree p -> PP.Doc
ppTree (Node n ts) = PP.group (PP.pretty n) PP.<$$> PP.text "" PP.<$$> PP.indent 2 (ppForest ts)
                               
-- commands
----------------------------------------------------------------------

constr :: String -> Symbol
constr n = Symbol n False

-- todo
initialEnv :: Environment Symbol
initialEnv = Map.fromList $
             [ (constr "[]", list alpha)
             , (constr "(:)", alpha :-> list alpha :-> list alpha)
             , (constr "True", boolean)
             , (constr "False", boolean)
             , (constr "0", nat)
             , (constr "succ", nat :-> nat) ]
  where
    alpha = TyVar (uniqueFromInt 1)
    list e = TyCon "L" [e]
    boolean = TyCon "Bool" []
    nat = TyCon "Nat" []

-- 


readProgram :: RunM (Program Symbol Variable)
readProgram = do
  eqs <- parseFile
  fs <- fromMaybe [last [ fst (definedSymbol eq) | eq <- eqs]] <$> reader startSymbols
  inferMLTypes fs eqs
    where
      inferMLTypes fs =  assertRight SimpleTypeError . inferTypes fs initialEnv
      parseFile = reader input >>= fromFile >>= assertRight ParseError
  

infer :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) => SzT.Signature f Ix.Term -> Program f v -> RunM (SzT.Signature f (SOCS.Polynomial Integer))
infer sig p = generateConstraints >>= solveConstraints where
  generateConstraints = do
    (res,l) <- lift (lift (I.generateConstraints sig p))
    putExecLog l
    assertRight SizeTypeError res
  solveConstraints cs = do
    pr <- reader constraintProcessor
    focs <- SOCS.toFOCS cs
    putExecLog [Node (PP.text "Generated FOCS") [Node (PP.pretty c) [] | c <- focs]]
    (msig,l) <- lift (lift (SOCS.solveConstraints pr sig focs))
    putExecLog l
    assertJust ConstraintUnsolvable msig  

putSolution :: (Eq f, PP.Pretty f, PP.Pretty v, PP.Pretty ix, IsSymbol f) =>
  Program f v -> Map.Map f (SizeType knd ix) -> RunM ()
putSolution p sig =
    status "Sized-type annotated program" (prettyProgram p (Map.map ren sig))
    where ren = runUnique . SzT.rename
    
timeAnalysis :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  Program f v -> RunM ()
timeAnalysis p = do
  w <- reader width
  let (ticked,aux) = tickProgram p
  status "Instrumented program" ticked
  status "Auxiliary equations" aux
  -- status "Abstract signature" (abstractSignature w)
  infer (abstractSignature w) ticked >>= putSolution ticked
  where
    abstractSignature w = Map.fromList ((Tick, tickSchema) : functionDecls w)
    tickSchema = SzQArr [1] (SzCon "#" [] (Ix.bvar 1)) (SzCon "#" [] (Ix.Succ (Ix.bvar 1)))
    functionDecls w = runUnique (decls w `concatMapM` (Map.toList (signature p)))
    decls w (f,tp) = do
      (t,v) <- abstractTimeType w f tp
      let constrDecl = (TConstr f, close (suite t ar))
          auxDecls = (TSymbol f 0, close (SzArr (clock v) (SzPair t (clock v))))
                     : [(TSymbol f (i + 1), close (suite t i)) | i <- [0 .. ar - 1]]
      return $ if isDefined f then auxDecls else ( constrDecl : auxDecls )
        where
          ar = arity p f
          clock = SzCon "#" [] . Ix.bvar
          suite t 0 = t
          suite (SzArr n (SzArr _ (SzPair p _))) i = SzArr n (suite p (i-1))

sizeAnalysis :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  Program f v -> RunM ()
sizeAnalysis p = do
  w <- reader width
  -- status "AbstractSignature" (abstractSignature w)
  infer (abstractSignature w) p >>= putSolution p
  where
    abstractSignature w = runUnique (Map.traverseWithKey (abstractSchema w) (signature p))
  
main :: IO ()
main = do
  cfg <- cmdArgs defaultConfig
  r <- runUniqueT $ flip runReaderT cfg $ runExceptT $ do
    abstr <- reader abstraction
    p <- readProgram
    status "Input program" (PP.pretty p)    
    let p' = withCallContexts abstr p
    status "Specialised program" (PP.pretty p')
    analysis <- reader analyse
    case analysis of
      Time -> timeAnalysis p'
      Size -> sizeAnalysis p'
  case r of
    Left e@SizeTypeError{} -> putDocLn e >> exitSuccess
    Left e -> putDocLn e >> exitWith (ExitFailure (-1))
    _ -> exitSuccess


