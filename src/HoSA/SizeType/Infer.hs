module HoSA.SizeType.Infer where

import           Control.Monad.Except
import           Control.Monad.Trace
import           Control.Monad.Writer
import           Data.List (nub, (\\))
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Either (rights)
import           Data.Tree
import qualified Constraints.Set.Solver as SetSolver
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.Rewriting.Applicative.Term as T
import           HoSA.Utils
import           HoSA.Data.Rewriting
import           HoSA.Data.SimpleType
import           HoSA.Data.CallSite hiding (lhs, rhs)
import qualified HoSA.Data.CallSite as C
import           HoSA.SizeType.Index (Constraint(..))
import qualified HoSA.SizeType.Index as Ix
import           HoSA.SizeType.Type



--------------------------------------------------------------------------------
-- common types
--------------------------------------------------------------------------------

type TypingContext = Map Variable (Schema Ix.Term)

type SizeTypedTerm = TypedTerm (Schema Ix.Term) ()

data Footprint = FP TypingContext (Type Ix.Term)

data Obligation = TypingContext :- (SizeTypedTerm ::: Type Ix.Term)
infixl 0 :-

--------------------------------------------------------------------------------
-- inference monad
--------------------------------------------------------------------------------

type ExecutionLog = Forest String

newtype InferM a =
  InferM { runInferM_ :: ExceptT SzTypingError (TraceT String (UniqueT IO)) a }
  deriving (Applicative, Functor, Monad
            , MonadTrace String
            , MonadError SzTypingError
            , MonadUnique
            , MonadIO)

runInferM :: InferM a -> IO (Either SzTypingError a, ExecutionLog)
runInferM = runUniqueT . runTraceT . runExceptT . runInferM_
  
newtype InferCG a = InferCG { runInferCG_ :: WriterT [Constraint] InferM a }
  deriving (Applicative, Functor, Monad
            , MonadError SzTypingError
            , MonadWriter [Constraint]
            , MonadUnique
            , MonadTrace String
            , MonadIO)

execInferCG ::InferCG a -> InferM [Constraint]
execInferCG = execWriterT . runInferCG_

liftInferM ::InferM a -> InferCG a
liftInferM = InferCG . lift
  
record :: Constraint -> InferCG ()
record cs = tell [cs] >> logMsg (PP.text "〈" PP.<+> PP.pretty cs PP.<+> PP.text "〉")

-- variable supply and logging
--------------------------------------------------------------------------------

uniqueSym :: MonadUnique m => m Ix.Sym
uniqueSym = Ix.Sym Nothing <$> unique

uniqueVar :: MonadUnique m => m Ix.VarId
uniqueVar = uniqueToInt <$> unique

logMsg :: MonadTrace String m => PP.Pretty e => e -> m ()
logMsg = trace . renderPretty

logBlk :: MonadTrace String m => PP.Pretty e => e -> m a -> m a
logBlk = scopeTrace . renderPretty


-- errors
--------------------------------------------------------------------------------

data SzTypingError where
  IllformedLhs :: SizeTypedTerm -> SzTypingError
  IllformedRhs :: SizeTypedTerm -> SzTypingError
  IlltypedTerm :: SizeTypedTerm -> String -> SizeType knd Ix.Term -> SzTypingError
  DeclarationMissing :: FunId -> SzTypingError

instance PP.Pretty SzTypingError where
  pretty (IllformedLhs t) =
    PP.hang 2 (PP.text "Illformed left-hand side encountered:"
               PP.</> PP.pretty (unType t))
  pretty (IllformedRhs t) =
    PP.hang 2 (PP.text "Illformed right-hand side encountered:"
               PP.</> PP.pretty (unType t))
  pretty (IlltypedTerm t s tp) =
    PP.hang 2
      (PP.text "Term" PP.<+> PP.squotes (PP.pretty (unType t)) PP.<> PP.text ""
       PP.</> PP.text "has type" PP.<+> PP.squotes (PP.pretty tp) PP.<> PP.text ","
       PP.</> PP.text "but expecting" PP.<+> PP.squotes (PP.text s) PP.<> PP.text ".")
  pretty (DeclarationMissing f) =
    PP.text "Type-declaration of symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "missing."

-- abstract signature
--------------------------------------------------------------------------------


abstractSchema :: Int -> SimpleType -> InferM (Schema Ix.Term)
abstractSchema width = runUniqueT . annotate
  where
    freshVarIds n = map uniqueToInt <$> uniques n
    freshFun vs = Ix.Fun <$> lift uniqueSym <*> return (Ix.bvar `map` Set.toList vs)

    annotate tp = close <$> annotateToplevel Set.empty tp
      where
        close :: (Set.Set Ix.VarId, Type Ix.Term) -> Schema Ix.Term
        close (_, SzBase bt ix) = SzBase bt ix
        close (fvs, SzArr n p) = SzQArr (Set.toList fvs) n p

    -- returns: free variables, type
    annotateToplevel vs (TyBase bt) = do
      t <- SzBase bt <$> freshFun vs
      return (Set.empty, t)
    annotateToplevel vs (TyPair tp1 tp2) = do
      (fvs1, t1) <- annotateToplevel vs tp1
      (fvs2, t2) <- annotateToplevel vs tp2
      return (fvs1 `Set.union` fvs2, SzPair t1 t2)
    annotateToplevel vs (n :-> p) = do
      (fvsn, n') <- annotateSchema vs n
      (fvsp, p') <- annotateToplevel (fvsn `Set.union` vs) p
      return (fvsn `Set.union` fvsp, SzArr n' p')

    -- returns: free variables, schema
    annotateSchema _ (TyBase bt) = do
      [i] <- freshVarIds 1
      return (Set.singleton i, SzBase bt (Ix.bvar i))
    -- annotateSchema vs (TyPair tp1 tp2) = do
    --   (fvs1,t1) <- annotateSchema vs tp1
    --   (fvs2,t2) <- annotateSchema vs tp2
    --   return (fvs1 `Set.union` fvs2, SzPair t1 t2)
    annotateSchema vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')

    -- returns: negative free variables, positive free variables, type
    annotateType vs (TyBase bt) = do
      is <- freshVarIds width
      let vs' = Set.fromList is `Set.union` vs
      ix <- freshFun vs'
      return (Set.empty, vs', SzBase bt ix)
    annotateType vs (TyPair tp1 tp2) = do
      (fvsn1, fvsp1, t1) <- annotateType vs tp1
      (fvsn2, fvsp2, t2) <- annotateType vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    annotateType vs (n :-> p) = annotateArr vs n p

    -- returns: negative free variables, positive free variables, type
    annotateArr vs n p = do
      (fvsn, n') <- annotateSchema vs n
      (nvsp, pvsp, p') <- annotateType (fvsn `Set.union` vs) p
      return (fvsn `Set.union` nvsp, pvsp, SzArr n' p')        


abstractSignature :: Map FunId SimpleType
                  -> CSAbstract
                  -> Int
                  -> [FunId]
                  -> [AnnotatedRule]
                  -> InferM (Signature Ix.Term)
abstractSignature ssig abstr width fs ars = logBlk "Abstract Signature" $ do 
    ccs <- callContexts abstr ars <$> sequence [ maybe (declMissing f) return (initialCC f <$> Map.lookup f ssig) | f <- fs]
    signatureFromList <$> sequence [ do s <- maybe (declMissing f) (abstractSchema width) (Map.lookup f ssig)
                                        logMsg (cc ::: s)
                                        return (cc,s)
                                   | cc <- ccs
                                   , let f = ctxSym cc ]
  where
    declMissing = throwError . DeclarationMissing


-- inference
--------------------------------------------------------------------------------

matrix :: MonadUnique m => Schema Ix.Term -> m ([Ix.VarId], Type Ix.Term)
matrix (SzBase bt ix) = return ([],SzBase bt ix)
-- matrix (SzPair s1 s2) = do
--   (vs1,tp1) <- matrix s1
--   (vs2,tp2) <- matrix s2
--   return (vs1 ++ vs2,SzPair tp1 tp2)
matrix (SzQArr ixs n p) = do
  ixs' <- sequence [uniqueVar | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', SzArr (Ix.inst subst n) (Ix.inst subst p))

returnTpe :: MonadUnique m => SizeType knd Ix.Term -> m (Type Ix.Term)
returnTpe (SzBase bt ix) = return (SzBase bt ix)
returnTpe (SzPair _ _) = return (SzPair undefined undefined)
returnTpe (SzArr _ p) = returnTpe p
returnTpe s@SzQArr{} = matrix s >>= returnTpe . snd


returnIndex :: MonadUnique m => SizeType knd Ix.Term -> m Ix.Term
returnIndex (SzBase _ ix) = return ix
returnIndex (SzArr _ p) = returnIndex p
returnIndex s@SzQArr{} = matrix s >>= returnIndex . snd
returnIndex SzPair{} = error "returnIndex on pairs not defined"

footprint :: SizeTypedTerm -> InferM Footprint
footprint l = logBlk "Footprint" $ fpInfer l
  where
    fpInfer t = do
      fp@(FP ctx tp) <- fpInfer_ t
      logMsg (PP.pretty ctx PP.<+> PP.text "⊦"
              PP.<+> PP.pretty (unType t)
              PP.<+> PP.text ":" PP.<+> PP.pretty tp)
      return fp
    fpInfer_ (tview -> TConst (_ ::: s)) =
      FP Map.empty . snd <$> matrix s
    fpInfer_ (tview -> TAppl t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      case tp1 of
        SzArr n p -> do
          (ctx2,s) <- fpCheck t2 n
          return (FP (ctx1 `Map.union` ctx2) (s `Ix.o` p))
        _ -> throwError (IlltypedTerm t1 "function type" tp1)
    fpInfer_ t = throwError (IllformedLhs l)

    fpCheck (tview -> TVar (v ::: _)) s =
      return (Map.singleton v s, Ix.idSubst)
    fpCheck t (SzBase _ (Ix.Var (Ix.FVar i))) = do
      FP ctx tp <- fpInfer t
      case tp of
        SzBase _ a -> return (ctx, Ix.substFromList [(i,a)])
        _ -> throwError (IlltypedTerm t "base type" tp)
    -- fpCheck (tview -> TPair t1 t2) (SzPair s1 s2) = do
    --   (ctx1, sub1) <- fpCheck t1 s1
    --   (ctx2, sub2) <- fpCheck t2 s2
    --   return (ctx1 `Map.union` ctx2, sub1 `Ix.after` sub2) -- substitution domains disjoint per construction
    fpCheck t tp = throwError (IlltypedTerm t "non-functional type" tp)
  
-- footprint (tview -> TAppl t (tview -> TVar (x ::: _))) = do
--   (ctx,tp) <- footprint t
--   case tp of
--     SzArr n p -> return (Map.insert x n ctx, p)
--     _ -> throwError (IlltypedTerm t "function type" tp)
-- footprint (tview -> TPair t1 t2) = do
--   (ctx1,tp1) <- footprint t1
--   (ctx2,tp2) <- footprint t2
--   return (ctx1 `Map.union` ctx2, SzPair tp1 tp2)
-- footprint (tview -> TAppl t1 t2) = do
--   (ctx1,tp1) <- footprint t1
--   (ctx2,tp2) <- footprint t2
--   case (tp1,tp2) of
--     (SzArr (SzBase _ (Ix.Var (Ix.FVar i))) tp, SzBase _ a) ->
--       return (ctx1 `Map.union` ctx2, Ix.substFromList [(i,a)] `Ix.o` tp)
--     (_,SzArr _ _) -> throwError (IlltypedTerm t2 "base type" tp2)
--     _ -> throwError (IlltypedTerm t1 "function on base type" tp1)
-- TODO    
-- footprint (tview -> TVar (x ::: s)) = do
--   tp <- snd <$> matrix s
--   return (Map.singleton x tp, tp)
              

obligations :: CSAbstract -> Signature Ix.Term -> [AnnotatedRule] -> InferM [Obligation]
obligations abstr sig ars = step `concatMapM` signatureToList sig where
  step (cc,s) =
    sequence [ do FP ctx tp <- footprint l
                  return (ctx :- annotatedRhs cc (arhs arl) ::: tp)
             | arl <- ars
             , headSymbol (C.lhs arl) == Just (Symbol (ctxSym cc))
             , l <- annotatedLhss s (C.lhs arl) ]

  -- TODO
  annotatedLhss _ (view -> Var _) = error "Infer.annotatedLhss :: LHS not head variable free"
  annotatedLhss s (view -> Const f) = [tfun f s]
  annotatedLhss s (view -> Appl l1 l2) = app <$> annotatedLhss s l1 <*> annotatedArgs l2 where
    annotatedArgs (view -> Var v) = [tvar v ()]
    annotatedArgs (view -> Const f) = [ tfun f s' | (_,s') <- lookupSchemas f sig ]
    annotatedArgs (view -> Appl t1 t2) = app <$> annotatedArgs t1 <*> annotatedArgs t2
    annotatedArgs (view -> Pair t1 t2) = tup <$> annotatedArgs t1 <*> annotatedArgs t2
      where tup a b = T.fun (Tuple ::: undefined) [a,b] -- todo

  annotatedRhs _ (T.aterm -> T.TVar v) = tvar v ()
  annotatedRhs cc (T.aterm -> T.TConst (Just cs@(CallSite (f ::: _) _))) = tfun f s where
    Just s = lookupSchema (abstr cs cc) sig
  annotatedRhs cc (T.aterm -> T.TFun Nothing [t1,t2]) = T.fun (Tuple ::: undefined) [annotatedRhs cc t1, annotatedRhs cc t2] -- todo
  annotatedRhs cc (T.aterm -> t1 T.:@ t2) = app (annotatedRhs cc t1) (annotatedRhs cc t2)


skolemTerm :: InferCG Ix.Term
skolemTerm = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG (Type Ix.Term)
instantiate (SzBase bt ix) = return (SzBase bt ix)
-- instantiate (SzPair s1 s2) = SzPair <$> instantiate s1 <*> instantiate s2
instantiate (SzQArr ixs n p) = do
  s <- Ix.substFromList <$> sequence [ (ix,) <$> skolemTerm | ix <- ixs]
  return (SzArr (Ix.inst s n) (Ix.inst s p))

subtypeOf :: SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG ()
t1 `subtypeOf` t2 = logBlk (PP.pretty t1 PP.</> PP.text "⊑" PP.<+> PP.pretty t2) $ t1 `subtypeOf_` t2

subtypeOf_ :: SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG ()
SzBase bt1 ix1 `subtypeOf_` SzBase bt2 ix2
  | bt1 == bt2 = record (ix2 :>=: ix1)
SzArr n p `subtypeOf_` SzArr m q = do
  m `subtypeOf_` n
  p `subtypeOf_` q
s1@SzQArr{} `subtypeOf_` s2@SzQArr{} = do 
  (_,t1) <- matrix s1
  t2 <- instantiate s2
  t1 `subtypeOf_` t2
SzPair t1 t2 `subtypeOf_` SzPair t1' t2' = do
  t1 `subtypeOf_` t1'
  t2 `subtypeOf_` t2'  
_ `subtypeOf_` _ = error "subtypeOf_: incompatible types"

inferSizeType :: TypingContext -> SizeTypedTerm -> InferCG (Type Ix.Term)
inferSizeType ctx t@(tview -> TVar (v ::: _)) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= instantiate
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty tp)    
  return tp
inferSizeType _ (tview -> TConst (f ::: s)) = do
  tp <- instantiate s
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty f PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
inferSizeType ctx t@(tview -> TPair t1 t2) =  do
  tp1 <- inferSizeType ctx t1
  tp2 <- inferSizeType ctx t2
  let tp = SzPair tp1 tp2
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t) PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
  
inferSizeType ctx t@(tview -> TAppl t1 t2) =
  logBlk (PP.text "infer" PP.<+> PP.pretty (unType t) PP.<+> PP.text "...") $ do
  tp1 <- inferSizeType ctx t1
  case tp1 of
    SzArr sArg tBdy -> do
      (_,tArg) <- matrix sArg
      tp2 <- inferSizeType ctx t2
      tp2 `subtypeOf` tArg
      logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t) PP.<+> PP.text ":" PP.<+> PP.pretty tBdy)
      return tBdy
    _ -> throwError (IlltypedTerm t1 "function type" tp1)
inferSizeType _ _ = error "HoSA.Infer.inferSizeType: illformed term given"    


obligationToConstraints :: Obligation -> InferM [Constraint]
obligationToConstraints o =  do { cs <- logBlk o (check o); instantiateMetaVars cs; return cs } where
  check (ctx :- t ::: tp) = execInferCG $ do
    tp' <- inferSizeType ctx t
    tp' `subtypeOf` tp
  instantiateMetaVars cs = do
    let (Just solved) = SetSolver.solveSystem (fromConstraint `concatMap` cs)
        mvars = rights (concatMap (\ (l :>=: r) -> vars l ++ vars r) cs)
    forM_ mvars $ \ mv@(Ix.MetaVar v _) -> do
      let (Just vs) = concatMap solutionToVars <$> SetSolver.leastSolution solved v
      f <- uniqueSym 
      Ix.substituteMetaVar mv (Ix.Fun f (Ix.fvar `map` vs))

  fromConstraint  (l :>=: r) = [ toExp vr SetSolver.<=! SetSolver.setVariable v
                              | (Right (Ix.MetaVar v _)) <- vars l, vr <- vars r]

  solutionToVars SetSolver.EmptySet = []
  solutionToVars (SetSolver.ConstructedTerm c _ []) = [c]
  solutionToVars a = error $ "solutionToVars: unexpected answer: " ++ show a

  toExp (Left v) = SetSolver.atom v
  toExp (Right (Ix.MetaVar v _)) = SetSolver.setVariable v
      
  vars Ix.Zero = []
  vars (Ix.Succ ix) = vars ix
  vars (Ix.Sum ixs) = concatMap vars ixs
  vars (Ix.Fun _ ixs) = concatMap vars ixs
  vars (Ix.Var (Ix.BVar _)) = error "HoSA.Infer.checkObligation: constraint contains bound variable"
  vars (Ix.Var (Ix.FVar v)) = [Left v]
  vars (Ix.MVar mv) = [Right mv]



generateConstraints :: CSAbstract -> Int -> Maybe [FunId] -> STAtrs
                    -> IO (Either SzTypingError (Signature Ix.Term, [Constraint])
                          , [AnnotatedRule]
                          , ExecutionLog)
generateConstraints abstr width startSymbols sttrs = fmap withARS $ runInferM $ do
    let rs = strRule `map` rules sttrs
        ds = nub [f | Symbol f <- (headSymbol . lhs) `mapMaybe` rs]
        cs = nub [f | Symbol f <- rulesFuns rs] \\ ds
        fs = fromMaybe ds startSymbols ++ cs
    sig <- abstractSignature (signature sttrs) abstr width fs ars
    let css = [ (ctxSym ctx, s) | (ctx,s) <- signatureToList sig, ctxSym ctx `elem` cs ]

    ocs <- logBlk "Orientation constraints" $ 
      obligations abstr sig ars >>= concatMapM obligationToConstraints
    ccs <- logBlk "Constructor constraints" $ execInferCG $ 
      forM_ css $ \ (c,s) -> do
        ix <- returnIndex s
        record (ix :=: Ix.ixSucc (Ix.ixSum [Ix.fvar v | v <- Ix.fvars ix]))
    return (sig,ocs ++ ccs)
  where 
    withARS (s,cs) = (s,ars,cs)
    ars = withCallSites sttrs

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty TypingContext where
  pretty m
    | Map.null m = PP.text "Ø"
    | otherwise = PP.hcat $ PP.punctuate (PP.text ", ")
      [ PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty s | (v,s) <- Map.toList m ]
  
instance PP.Pretty Obligation where
  pretty (ctx :- t ::: s) =
    PP.pretty ctx
    PP.<+> PP.text "⊦" PP.<+> PP.pretty (unType t)
    PP.<+> PP.text ":" PP.<+> PP.pretty s

instance PP.Pretty Footprint where
  pretty (FP ctx tp) =
    PP.parens (PP.pretty ctx PP.<> PP.comma PP.<+> PP.pretty tp)
