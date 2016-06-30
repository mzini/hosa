module HoSA.SizeType.Infer where

import           Control.Arrow ((|||))
import           Control.Monad.Except
import           Control.Monad.Trace
import           Control.Monad.Writer
import           Data.List (nub, (\\))
import           Data.Foldable
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Tree
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           HoSA.Utils
import           HoSA.Data.Rewriting
import           HoSA.Data.SimpleType hiding (unType, Signature)
import           HoSA.Data.CallSite hiding (lhs, rhs)
import qualified HoSA.Data.CallSite as C
import           HoSA.SizeType.Index (Constraint(..))
import qualified HoSA.SizeType.Index as Ix
import           HoSA.SizeType.Type
import           HoSA.SizeType.SOConstraint (SOCS (..))



--------------------------------------------------------------------------------
-- common types
--------------------------------------------------------------------------------

type TypingContext v = Map v (Either (Type Ix.Term) (Schema Ix.Term))

type SizeTypedTerm f v = Term (f ::: Schema Ix.Term) v

unType :: SizeTypedTerm f v -> Term f v 
unType = tmap (\ (f ::: _) -> f) id

data Footprint v = FP (TypingContext v) (Type Ix.Term)

data Obligation f v = TypingContext v :- (SizeTypedTerm f v ::: Type Ix.Term)
infixl 0 :-

--------------------------------------------------------------------------------
-- inference monad
--------------------------------------------------------------------------------

type ExecutionLog = Forest String

newtype InferM f v a =
  InferM { runInferM_ :: ExceptT (SzTypingError f v) (TraceT String (UniqueT IO)) a }
  deriving (Applicative, Functor, Monad
            , MonadTrace String
            , MonadError (SzTypingError f v)
            , MonadUnique
            , MonadIO)

runInferM :: InferM f v a -> UniqueT IO (Either (SzTypingError f v) a, ExecutionLog)
runInferM = runTraceT . runExceptT . runInferM_
  
newtype InferCG f v a = InferCG { runInferCG_ :: WriterT (SOCS) (InferM f v) a }
  deriving (Applicative, Functor, Monad
            , MonadError (SzTypingError f v)
            , MonadWriter SOCS
            , MonadUnique
            , MonadTrace String
            , MonadIO)

execInferCG ::InferCG f v a -> InferM f v SOCS
execInferCG = execWriterT . runInferCG_

liftInferM ::InferM f v a -> InferCG f v a
liftInferM = InferCG . lift

  -- notOccur vs `mapM` Ix.metaVars t2

notOccur :: [Ix.VarId] -> Ix.MetaVar -> InferCG f v ()
notOccur vs mv = do
  tell (SOCS [] [ Ix.NOccur v mv | v <- vs])
  logMsg (PP.text "〈"
           PP.<+> PP.pretty (Ix.FVar `map` vs)
           PP.<+> PP.text "notin" PP.<+> PP.pretty mv
           PP.<+> PP.text "〉")

require :: Constraint -> InferCG f v ()
require cs = do
  tell (SOCS [cs] [])
  logMsg (PP.text "〈" PP.<+> PP.pretty cs PP.<+> PP.text "〉")

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

data SzTypingError f v where
  IllformedLhs :: SizeTypedTerm f v -> SzTypingError f v
  IllformedRhs :: SizeTypedTerm f v -> SzTypingError f v
  IlltypedTerm :: SizeTypedTerm f v -> String -> SizeType knd Ix.Term -> SzTypingError f v
  DeclarationMissing :: f -> SzTypingError f v

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (SzTypingError f v) where
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


abstractSchema :: Int -> SimpleType -> InferM f v (Schema Ix.Term)
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
    annotateToplevel vs (tp1 :*: tp2) = do
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
    annotateType vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotateType vs tp1
      (fvsn2, fvsp2, t2) <- annotateType vs tp2
      return (fvsn1 `Set.union` fvsn2, fvsp1 `Set.union` fvsp2, SzPair t1 t2)
    annotateType vs (n :-> p) = annotateArr vs n p

    -- returns: negative free variables, positive free variables, type
    annotateArr vs n p = do
      (fvsn, n') <- annotateSchema vs n
      (nvsp, pvsp, p') <- annotateType (fvsn `Set.union` vs) p
      return (fvsn `Set.union` nvsp, pvsp, SzArr n' p')        


abstractSignature :: (Eq v, Ord f, PP.Pretty f) =>
  Map f SimpleType -> CSAbstract f -> Int -> [f] -> [AnnotatedRule f v] -> InferM f v (Signature f Ix.Term)
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
  ixs' <- sequence [ uniqueVar | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', SzArr (Ix.inst subst n) (Ix.inst subst p))

returnIndex :: MonadUnique m => SizeType knd Ix.Term -> m Ix.Term
returnIndex (SzBase _ ix) = return ix
returnIndex (SzArr _ p) = returnIndex p
returnIndex s@SzQArr{} = matrix s >>= returnIndex . snd
returnIndex SzPair{} = error "returnIndex on pairs not defined"

footprint :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => SizeTypedTerm f v -> InferM f v (Footprint v)
footprint l = logBlk "Footprint" $ fpInfer l
  where
    fpInfer t = do
      fp@(FP ctx tp) <- fpInfer_ t
      logMsg (PP.pretty ctx PP.<+> PP.text "⊦"
              PP.<+> PP.pretty (unType t)
              PP.<+> PP.text ":" PP.<+> PP.pretty tp)
      return fp
    fpInfer_ (Fun (_ ::: s)) =
      FP Map.empty . snd <$> matrix s
    fpInfer_ (Apply t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      case tp1 of
        SzArr n p -> do
          (ctx2,s) <- fpCheck t2 n
          return (FP (ctx1 `Map.union` ctx2) (s `Ix.o` p))
        _ -> throwError (IlltypedTerm t1 "function type" tp1)
    fpInfer_ t = throwError (IllformedLhs l)

    fpCheck (Var v) s =
      return (Map.singleton v (Right s), Ix.idSubst)
    fpCheck t (SzBase _ (Ix.Var (Ix.FVar i))) = do
      FP ctx tp <- fpInfer t
      case tp of
        SzBase _ a -> return (ctx, Ix.substFromList [(i,a)])
        _ -> throwError (IlltypedTerm t "base type" tp)
    fpCheck t tp = throwError (IlltypedTerm t "non-functional type" tp)

obligations :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => CSAbstract f -> Signature f Ix.Term -> [AnnotatedRule f v] -> InferM f v [Obligation f v]
obligations abstr sig ars = step `concatMapM` signatureToList sig where
  step (cc,s) =
    sequence [ do FP ctx tp <- footprint alhs
                  return (ctx :- annotateRhs cc (arlAnnotatedRhs arl) ::: tp)
             | arl <- ars
             , let l = lhs (C.arlUntypedRule arl)
             , headSymbol l == Just (ctxSym cc)
             , alhs <- annotateLhss s l ]

  -- TODO
  annotateLhss s (Fun f) = [Fun (f:::s)]
  annotateLhss s (Apply l1 l2) = Apply <$> annotateLhss s l1 <*> annotateArgs l2 where
    annotateArgs (Var v) = [Var v]
    annotateArgs (Fun f) = [ Fun (f:::s') | (_,s') <- lookupSchemas f sig ]
    annotateArgs (Apply t1 t2) = Apply <$> annotateArgs t1 <*> annotateArgs t2
    annotateArgs (Pair t1 t2) = Pair <$> annotateArgs t1 <*> annotateArgs t2
    annotateArgs Let {} = error "Infer.annotateLhss :: LHS contains let expression"
  annotateLhss _ _ = error "Infer.annotateLhss :: LHS not head variable free"

  annotateRhs _ (Var v) = Var v
  annotateRhs cc (Fun cs@(CallSite (f ::: _) _)) = Fun (f:::s) where
    Just s = lookupSchema (abstr cs cc) sig
  annotateRhs cc (Pair t1 t2) = Pair (annotateRhs cc t1) (annotateRhs cc t2)
  annotateRhs cc (Apply t1 t2) = Apply (annotateRhs cc t1) (annotateRhs cc t2)
  annotateRhs cc (Let t1 vs t2) = Let (annotateRhs cc t1) vs (annotateRhs cc t2)  


skolemVar :: InferCG f v Ix.Term
skolemVar = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG f v (Type Ix.Term)
instantiate (SzBase bt ix) = return (SzBase bt ix)
-- instantiate (SzPair s1 s2) = SzPair <$> instantiate s1 <*> instantiate s2
instantiate (SzQArr ixs n p) = do
  s <- Ix.substFromList <$> sequence [ (ix,) <$> skolemVar | ix <- ixs]
  return (SzArr (Ix.inst s n) (Ix.inst s p))

subtypeOf :: SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG f v ()
t1 `subtypeOf` t2 = logBlk (PP.pretty t1 PP.</> PP.text "⊑" PP.<+> PP.pretty t2) $ t1 `subtypeOf_` t2

subtypeOf_ :: SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG f v ()
SzBase bt1 ix1 `subtypeOf_` SzBase bt2 ix2
  | bt1 == bt2 = require (ix2 :>=: ix1)
SzArr n p `subtypeOf_` SzArr m q = do
  m `subtypeOf_` n
  p `subtypeOf_` q
s1@SzQArr{} `subtypeOf_` s2@SzQArr{} = do 
  (vs,t1) <- matrix s1
  (_, t2) <- matrix s2
  t2' <- instantiate s2
  logBlk (PP.text "occurs check") $ do 
    notOccur vs `mapM` (metaVars t1 ++ metaVars t2)
  t1 `subtypeOf_` t2'
SzPair t1 t2 `subtypeOf_` SzPair t1' t2' = do
  t1 `subtypeOf_` t1'
  t2 `subtypeOf_` t2'  
_ `subtypeOf_` _ = error "subtypeOf_: incompatible types"

inferSizeType :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => TypingContext v -> SizeTypedTerm f v -> InferCG f v (Type Ix.Term)
inferSizeType ctx t@(Var v) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= either return instantiate 
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty tp)    
  return tp
inferSizeType _ (Fun (f ::: s)) = do
  tp <- instantiate s
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty f PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
inferSizeType ctx t@(Pair t1 t2) =  do
  tp1 <- inferSizeType ctx t1
  tp2 <- inferSizeType ctx t2
  let tp = SzPair tp1 tp2
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t) PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
inferSizeType ctx t@(Apply t1 t2) =
  logBlk (PP.text "infer" PP.<+> PP.pretty (unType t) PP.<+> PP.text "...") $ do
  tp1 <- inferSizeType ctx t1
  case tp1 of
    SzArr sArg tBdy -> do
      (vs,tArg) <- matrix sArg
      -- TODO: use different contexts
      let ctxMetaVars = foldMap (metaVars ||| metaVars)
      notOccur vs `mapM` ctxMetaVars [ tp | (v,tp) <- Map.toList ctx,  v `elem` fvarsDL t2 [] ]
      tp2 <- inferSizeType ctx t2
      tp2 `subtypeOf` tArg
      logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t) PP.<+> PP.text ":" PP.<+> PP.pretty tBdy)
      return tBdy
    _ -> throwError (IlltypedTerm t1 "function type" tp1)
inferSizeType ctx t@(Let t1 (x,y) t2) =
  logBlk (PP.text "infer" PP.<+> PP.pretty (unType t) PP.<+> PP.text "...") $ do
  tp1 <- inferSizeType ctx t1
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t1) PP.<+> PP.text ":" PP.<+> PP.pretty tp1)
  case tp1 of
    SzPair tpx tpy -> do
      let ctx' = Map.insert x (Left tpx) (Map.insert y (Left tpy) ctx)
      tp <- inferSizeType ctx' t2
      logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty (unType t2) PP.<+> PP.text ":" PP.<+> PP.pretty tp)
      return tp
    _ -> throwError (IlltypedTerm t1 "pair type" tp1)

obligationToConstraints :: (PP.Pretty f, PP.Pretty v, Ord f, Ord v) => Obligation f v -> InferM f v SOCS
obligationToConstraints o@(ctx :- t ::: tp) =  logBlk o $ execInferCG $ do 
  tp' <- inferSizeType ctx t
  tp' `subtypeOf` tp

-- obligationToConstraints o =  do { cs <- logBlk o (check o); instantiateMetaVars cs; return cs } where
--   check (ctx :- t ::: tp) = execInferCG $ do
--     tp' <- inferSizeType ctx t
--     tp' `subtypeOf` tp
--   instantiateMetaVars cs = do
--     let (Just solved) = SetSolver.solveSystem (fromConstraint `concatMap` cs)
--         mvars = rights (concatMap (\ (l :>=: r) -> vars l ++ vars r) cs)
--     forM_ mvars $ \ mv@(Ix.MetaVar v _) -> do
--       let (Just vs) = oconcatMap solutionToVars <$> SetSolver.leastSolution solved v
--       f <- uniqueSym 
--       Ix.substituteMetaVar mv (Ix.Fun f (Ix.fvar `map` vs))

--   fromConstraint  (l :>=: r) = [ toExp vr SetSolver.<=! SetSolver.setVariable v
--                               | (Right (Ix.MetaVar v _)) <- vars l, vr <- vars r]

--   solutionToVars SetSolver.EmptySet = []
--   solutionToVars (SetSolver.ConstructedTerm c _ []) = [c]
--   solutionToVars a = error $ "solutionToVars: unexpected answer: " ++ show a

--   toExp (Left v) = SetSolver.atom v
--   toExp (Right (Ix.MetaVar v _)) = SetSolver.setVariable v
      
--   vars Ix.Zero = []
--   vars (Ix.Succ ix) = vars ix
--   vars (Ix.Sum ixs) = concatMap vars ixs
--   vars (Ix.Fun _ ixs) = concatMap vars ixs
--   vars (Ix.Var (Ix.BVar _)) = error "HoSA.Infer.checkObligation: constraint contains bound variable"
--   vars (Ix.Var (Ix.FVar v)) = [Left v]
--   vars (Ix.MVar mv) = [Right mv]



generateConstraints :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => CSAbstract f -> Int -> Maybe [f] -> STAtrs f v
                    -> UniqueT IO (Either (SzTypingError f v) (Signature f Ix.Term, SOCS)
                                  , [AnnotatedRule f v]
                                  , ExecutionLog)
generateConstraints abstr width startSymbols sttrs = fmap withARS $ runInferM $ do
  sig <- abstractSignature (statrsSignature sttrs) abstr width fs ars
    
  ocs <- logBlk "Orientation constraints" $ 
    obligations abstr sig ars >>= mapM obligationToConstraints
  ccs <- logBlk "Constructor constraints" $ execInferCG $ 
    forM_ (signatureToList sig) $ \ (ctx,s) -> 
        when (ctxSym ctx `elem` cs) $ do
           ix <- returnIndex s
           require (ix :=: Ix.ixSucc (Ix.ixSum [Ix.fvar v | v <- Ix.fvars ix]))
  return (sig, mconcat (ccs:ocs))
  where 
    withARS (s,cs) = (s,ars,cs)
    ars = withCallSites sttrs
    atrs = toATRS sttrs
    ds = nub $ (headSymbol . lhs) `mapMaybe` rules atrs
    cs = nub (funs atrs) \\ ds
    fs = fromMaybe ds startSymbols ++ cs
-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m
    | Map.null m = PP.text "Ø"
    | otherwise = PP.hcat $ PP.punctuate (PP.text ", ")
      [ PP.pretty v PP.<+> PP.text ":" PP.<+> either PP.pretty PP.pretty e | (v,e) <- Map.toList m ]
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Obligation f v) where
  pretty (ctx :- t ::: s) =
    PP.pretty ctx
    PP.<+> PP.text "⊦" PP.<+> PP.pretty (unType t)
    PP.<+> PP.text ":" PP.<+> PP.pretty s

instance PP.Pretty v => PP.Pretty (Footprint v) where
  pretty (FP ctx tp) =
    PP.parens (PP.pretty ctx PP.<> PP.comma PP.<+> PP.pretty tp)
