module HoSA.SizeType.Infer where

import           Data.List (transpose)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trace
import           Control.Monad.Writer
import qualified Data.Map as Map
import           Data.Tree
import           Data.List (nub)
import           Data.Maybe (fromMaybe)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Set as Set
import           Data.Foldable

import           HoSA.Utils
import           HoSA.Data.Program
import           HoSA.Data.MLTypes hiding (Signature,rename)
import           HoSA.Data.Index (Constraint(..))
import qualified HoSA.Data.Index as Ix
import           HoSA.Data.SizeType
import           HoSA.SizeType.SOConstraint (SOCS (..))

--------------------------------------------------------------------------------
-- common types
--------------------------------------------------------------------------------

type TypingContext v = Map.Map v (Either (Type Ix.Term) (Schema Ix.Term))

data Fun f = Lam | F f

instance IsSymbol f => IsSymbol (Fun f) where
  isDefined Lam = True
  isDefined (F f) = isDefined f
instance PP.Pretty f => PP.Pretty (Fun f ) where
  pretty Lam = PP.text "#Anon"
  pretty (F f) = PP.pretty f
  
type SizeTypedExpression f v = TypedExpression (Fun f, Schema Ix.Term) v 

data Footprint v = FP (TypingContext v) (Type Ix.Term)

--------------------------------------------------------------------------------
-- inference monad
--------------------------------------------------------------------------------

type ExecutionLog = Forest PP.Doc

newtype InferM f v a =
  InferM { runInferM_ :: ReaderT (Map.Map f SimpleType) (ExceptT (SzTypingError f v) (TraceT PP.Doc (UniqueT IO))) a }
  deriving (Applicative, Functor, Monad
            , MonadTrace PP.Doc
            , MonadError (SzTypingError f v)
            , MonadReader (Map.Map f SimpleType)
            , MonadUnique
            , MonadIO)

runInferM :: Map.Map f SimpleType -> InferM f v a -> UniqueT IO (Either (SzTypingError f v) a, ExecutionLog)
runInferM sig = runTraceT . runExceptT . flip runReaderT sig . runInferM_
  
newtype InferCG f v a = InferCG { runInferCG_ :: WriterT SOCS (InferM f v) a }
  deriving (Applicative, Functor, Monad
            , MonadError (SzTypingError f v)
            , MonadWriter SOCS
            , MonadUnique
            , MonadTrace PP.Doc
            , MonadIO)

execInferCG ::InferCG f v a -> InferM f v SOCS
execInferCG = execWriterT . runInferCG_

liftInferM ::InferM f v a -> InferCG f v a
liftInferM = InferCG . lift

simpleSignature :: InferCG f v (Map.Map f SimpleType)
simpleSignature = liftInferM ask

notOccur :: [Ix.VarId] -> Ix.MetaVar -> InferCG f v ()
notOccur [] _ = return ()
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

-- variable/symbol supply and logging
--------------------------------------------------------------------------------

uniqueVar :: MonadUnique m => m Ix.VarId
uniqueVar = uniqueToInt <$> unique

freshIxTerm :: MonadUnique m => [Ix.Term] -> m Ix.Term
freshIxTerm ts = do
  f <- Ix.Sym Nothing <$> unique
  return (Ix.Fun f ts)

logMsg :: MonadTrace PP.Doc m => PP.Pretty e => e -> m ()
logMsg = trace . PP.pretty

logBlk :: MonadTrace PP.Doc m => PP.Pretty e => e -> m a -> m a
logBlk = scopeTrace . PP.pretty

-- errors
--------------------------------------------------------------------------------

data SzTypingError f v where
  IllformedLhs :: SizeTypedExpression f v -> SzTypingError f v
  IllformedRhs :: SizeTypedExpression f v -> SzTypingError f v
  IlltypedTerm :: SizeTypedExpression f v -> String -> SizeType knd Ix.Term -> SzTypingError f v
  MatchFailure :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> SzTypingError f v
  UnsupportedDType :: Distribution (SizeType knd' Ix.Term) -> SzTypingError f v
  DeclarationMissing :: f -> SzTypingError f v

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (SzTypingError f v) where
  pretty (IllformedLhs t) =
    PP.hang 2 (PP.text "Illformed left-hand side encountered:"
               PP.</> PP.pretty t)
  pretty (IllformedRhs t) =
    PP.hang 2 (PP.text "Illformed right-hand side encountered:"
               PP.</> PP.pretty t)
  pretty (UnsupportedDType t) =
    PP.hang 2 (PP.text "Unsupported type in distribution encountered:"
               PP.</> PP.pretty t)    
  pretty (IlltypedTerm t s tp) =
    PP.hang 2
      (PP.text "Term" PP.<+> PP.squotes (PP.pretty t) PP.<> PP.text ""
       PP.</> PP.text "has type" PP.<+> PP.squotes (PP.pretty tp) PP.<> PP.text ","
       PP.</> PP.text "but expecting" PP.<+> PP.squotes (PP.text s) PP.<> PP.text ".")
  pretty (DeclarationMissing f) =
    PP.text "Type-declaration of symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "missing."

  pretty (MatchFailure s n) =
    PP.text "Error in matching schema" PP.<+> PP.squotes (PP.pretty s)
    PP.<+> PP.text "with" PP.<+> PP.squotes (PP.pretty n)
-- inference
--------------------------------------------------------------------------------


type TSubst = [(TypeVariable, Schema Ix.Term)]

idSubst :: TSubst
idSubst = []

after :: MonadUnique m => TSubst -> TSubst -> m TSubst
s1 `after` s2 = do
  s2' <- sequence [(v,) <$> substituteTyVars s1 s | (v,s) <- s2 ]
  return (s2' ++ s1)

class TSubstitute a where
  substituteTyVars :: MonadUnique m => TSubst -> a -> m a

instance TSubstitute (Type Ix.Term) where
  substituteTyVars subst t@(SzVar v)      =
    case lookup v subst of
      Nothing -> return t
      Just s -> snd <$> matrix s
  substituteTyVars subst (SzCon n ts ix)  =
    SzCon n <$> mapM (substituteTyVars subst) ts <*> return ix
  substituteTyVars subst (SzArr n p) =
    SzArr <$> substituteTyVars subst n <*> substituteTyVars subst p
  substituteTyVars subst (SzPair s1 s2)   = SzPair <$> substituteTyVars subst s1 <*> substituteTyVars subst s2

instance TSubstitute (Schema Ix.Term) where                                            
  substituteTyVars subst s@(SzVar v)      =
    case lookup v subst of
      Nothing -> return s
      Just s' -> return s'
  substituteTyVars subst (SzCon n ts ix)  = SzCon n <$> mapM (substituteTyVars subst) ts <*> return ix
  substituteTyVars subst (SzQArr ixs n p) = do
    ixs' <- sequence [ uniqueVar | _ <- ixs]
    let ixsubst = Ix.substFromList (zip ixs (Ix.bvar `map` ixs'))
    n' <- substituteTyVars subst (ixsubst `Ix.inst` n)
    p' <- substituteTyVars subst (ixsubst `Ix.inst` p)
    return (SzQArr ixs' n' p')
  substituteTyVars subst (SzPair s1 s2)   = SzPair <$> substituteTyVars subst s1 <*> substituteTyVars subst s2

instance TSubstitute (TypingContext v) where
  substituteTyVars subst = mapM f where
    f (Left t) = Left <$> substituteTyVars subst t
    f (Right t) = Right <$> substituteTyVars subst t


-- abstract schemas
                 
close :: Type Ix.Term -> Schema Ix.Term
close (SzVar v)       = SzVar v
close (SzCon n ts ix) = SzCon n ts ix
close (SzPair t1 t2)  = SzPair (close t1) (close t2)
close t@(SzArr n p)   = SzQArr (Set.toList (bvs t)) n p where
  bvs :: SizeType knd Ix.Term -> Set.Set Ix.VarId
  bvs (SzVar _) = Set.empty
  bvs (SzCon _ ts ix) = Set.fromList (Ix.bvars ix) `Set.union` Set.unions (bvs `map` ts)
  bvs (SzPair t1 t2) = bvs t1 `Set.union` bvs t2
  bvs (SzArr t1 t2) = bvs t1 `Set.union` bvs t2
  bvs (SzQArr ixs t1 t2) = (bvs t1 `Set.union` bvs t2) Set.\\ Set.fromList ixs

freshVarIds :: MonadUnique m => Int -> m [Ix.VarId]
freshVarIds n = map uniqueToInt <$> uniques n

freshVarId :: MonadUnique m => m Ix.VarId
freshVarId = uniqueToInt <$> unique

abstractSchema :: (MonadUnique m) => TypingContext v -> SimpleType -> m (Schema Ix.Term)
abstractSchema ctx tp = close <$> abstractType ctx 1 tp

abstractType :: (MonadUnique m) => TypingContext v -> Int -> SimpleType -> m (Type Ix.Term)
abstractType ctx width stp = thrd <$> runUniqueT (annotatePositive 0 Set.empty stp)
  where
    ctxtps = either toSchema id `map` toList ctx
    ctxvs = Ix.fvar `map` nub (fvarsIx `concatMap` ctxtps)
    thrd (_,_,c) = c
    -- returns: negative free variables, positive free variables, type
    annotatePositive _ _  (TyVar v) = return (Set.empty, Set.empty, SzVar v)    
    annotatePositive w vs (TyCon n ts) = do
      (fvsn,fvsp,as) <- foldM (\ (fvsn,fvsp,as) t -> do
                                  (fvsn', fvsp', a) <- annotatePositive w vs t
                                  return (fvsn' `Set.union` fvsn
                                         , fvsp' `Set.union` fvsp
                                         , as ++ [toSchema a]))
                              (Set.empty,Set.empty,[])
                              ts
      is <- freshVarIds w
      let vs' = Set.fromList is `Set.union` vs
      ix <- lift (freshIxTerm ([Ix.bvar v | v <- Set.toList vs'] ++ ctxvs))
      return (fvsn, vs' `Set.union` fvsp,SzCon n as ix)
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
      (fvs1,as) <- foldM (\ (fvs',as) t -> do
                            (fvs'', a) <- annotateNegative vs t
                            return (fvs'' `Set.union` fvs', as ++ [a]))
                        (Set.empty,[])
                        ts
      i <- freshVarId
      return (Set.insert i fvs1, SzCon n as (Ix.bvar i))
    annotateNegative vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr width vs n p
      return (pvs Set.\\ nvs, SzQArr (Set.toList nvs) n' p')
    
    -- returns: negative free variables, positive free variables, type
    annotateArr w vs n p = do
      (fvsn, n') <- annotateNegative Set.empty n
      (nvsp, pvsp, p') <- annotatePositive w (fvsn `Set.union` vs) p
      return (fvsn `Set.union` nvsp, pvsp, SzArr n' p')        

-- inference
  

szMatch :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> InferM f v ([(Ix.VarId, Ix.Term)], [(TypeVariable, Schema Ix.Term)])
szMatch (SzVar v1)                         tp             = return ([],[(v1,toSchema tp)])
szMatch tp                                 (SzVar v2)     = return ([],[(v2,toSchema tp)])    
szMatch (SzCon n ss1 (Ix.Var (Ix.FVar i))) (SzCon m ss2 a) | n == m = do
  (sis,sts) <- unzip <$> zipWithM szMatch ss1 ss2
  return ((i,a):concat sis, concat sts)
szMatch (SzPair s1 s2)                     (SzPair t1 t2) = do
  (si1,st1) <- szMatch s1 t1
  (si2,st2) <- szMatch s2 t2
  return (si1 ++ si2, st1 ++ st2)
szMatch s          n                     = throwError (MatchFailure s n)

footprint :: Ord v => SizeTypedExpression f v -> InferM f v (Footprint v)
footprint = fpInfer where
    fpInfer (Fun (_,s) _ _) = do
      (_, tp) <- rename s >>= matrix
      return (FP Map.empty tp)
    fpInfer (Apply _ t1 (Var v _)) = do
      FP ctx tp <- fpInfer t1
      case tp of
        SzArr n p -> return (FP (Map.insert v (Right n) ctx) p)
        _ -> throwError (IlltypedTerm t1 "function type" tp)
    fpInfer (Apply _ t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      FP ctx2 tp2 <- fpInfer t2
      case tp1 of
        SzArr n p -> do
          (si,st) <- szMatch n tp2
          ctx1' <- substituteTyVars st ctx1
          ctx2' <- substituteTyVars st ctx2
          tp <- Ix.o (Ix.substFromList si)  <$> substituteTyVars st p
          return (FP (ctx1' `Map.union` ctx2') tp) 
        _ -> throwError (IlltypedTerm t1 "function type" tp1)
    fpInfer (Pair _ t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      FP ctx2 tp2 <- fpInfer t2
      return (FP (ctx1 `Map.union` ctx2) (SzPair tp1 tp2))
    fpInfer t = throwError (IllformedLhs t)

-- -- typing obligations
-- obligation :: (PP.Pretty f, Ord f, Ord v) => TypingContext v -> (SizeTypedExpression f v, SizeTypedExpression f v) -> InferM f v (Obligation f v)
-- obligation ctx (l,r) = do
--   FP fpctx fptp <- footprint l
--   return (Map.map Right fpctx `Map.union` ctx :- (r, fptp))

-- obligationsFromProgram :: (PP.Pretty f, Ord f, Ord v) => Signature f Ix.Term -> Program f v -> InferM f v [Obligation f v]
-- obligationsFromProgram sig p = obligation Map.empty `mapM`  ((annotateEq . eqEqn) `map` equations p) where
--   annotateEq eq = (annotate (lhs eq), annotate (rhs eq))
--   annotate = mapExpression fun var
--   fun f tp _ = ((F f, fromMaybe err (Map.lookup f sig) ),tp) where
--     err = error $ "no sized type assigned to " ++ show (PP.pretty f)
--   var v tp = (v,tp)


-- probabilism
expectedType :: IsSymbol f => SimpleType -> Distribution (SizeType knd Ix.Term) -> InferCG f v (SizeType knd Ix.Term)
expectedType (a :*: b) (Distribution d ls) =
  SzPair <$> expectedType a da <*> expectedType b db
  where 
    da = Distribution d [ (p,t') | (p,SzPair t' _) <- ls]
    db = Distribution d [ (p, t') | (p,SzPair _ t') <- ls]
expectedType (TyCon n sts) dst@(Distribution d ls) = do
  sig <- Map.filterWithKey (\ f _ -> isConstructor f) <$> simpleSignature
  if null (contraVariant sig n sts)
    then SzCon n <$> zipWithM expectedType sts ds <*> pure ix 
    else throwError (UnsupportedDType dst)
  where
    ix = Ix.Sum [ Ix.Mult p ix' | (p, SzCon _ _ ix') <- ls]
    ds = [Distribution d d' | d' <- transpose [ [(p,t) | t <- ts] | (p,SzCon _ ts _) <- ls]]
expectedType _ dst = throwError (UnsupportedDType dst)

-- inference

skolemVar :: InferCG f v Ix.Term
skolemVar = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG f v (Type Ix.Term)
instantiate s = do
  (vs,tp) <- matrix s
  subst <- Ix.substFromList <$> sequence [ (v,) <$> skolemVar | v <- vs]
  return (subst `Ix.o` tp)

soSuperType,soSubType :: SizeType knd Ix.Term -> InferCG f v (SizeType knd Ix.Term)
soSuperType (SzVar v)       = return (SzVar v)
soSuperType (SzCon n as ix) = SzCon n <$> mapM soSuperType as <*> fresh
  where fresh = do {ix' <- skolemVar; require (ix' :>=: ix); return ix'}
soSuperType (SzPair t1 t2)   = SzPair <$> soSuperType t1 <*> soSuperType t2
soSuperType (SzArr n p)      = SzArr <$> soSubType n <*> soSuperType p
soSuperType (SzQArr vs n p)  = SzQArr vs <$> soSubType n <*> soSuperType p

soSubType (SzVar v)       = return (SzVar v)
soSubType (SzCon n as ix) = SzCon n <$> mapM soSubType as <*> fresh
  where fresh = do {ix' <- skolemVar; require (ix :>=: ix'); return ix'}
soSubType (SzPair t1 t2)   = SzPair <$> soSubType t1 <*> soSubType t2
soSubType (SzArr n p)      = SzArr <$> soSuperType n <*> soSubType p
soSubType (SzQArr vs n p)  = SzQArr vs <$> soSuperType n <*> soSubType p


-- subtypeOfD :: (TSubstitute (SizeType knd Ix.Term), IsSymbol f) => Distribution (SizeType knd Ix.Term) -> SizeType knd Ix.Term -> InferCG f v TSubst
-- Distribution _ [(_,tp1)] `subtypeOfD` tp2  = tp1 `subtypeOf_` tp2
-- distr `subtypeOfD` tp = distr `subtypeOfD_` tp
-- subtypeOfD_ :: (TSubstitute (SizeType knd Ix.Term), IsSymbol f) => Distribution (SizeType knd Ix.Term) -> SizeType knd Ix.Term -> InferCG f v TSubst
-- Distribution _ ls `subtypeOfD_` SzVar v2
--     | all (p . snd) ls = return [] where
--         p (SzVar v1) = v1 == v2
--         p _          = False
-- Distribution denom ls `subtypeOfD_` SzPair t1 t2 = do
--   let d1 = Distribution denom [ (p,t') | (p,SzPair t' _) <- ls]
--   let d2 = Distribution denom [ (p, t') | (p,SzPair _ t') <- ls]
--   subst1 <- d1 `subtypeOfD_` t1
--   t2' <- substituteTyVars subst1 t2
--   d2' <- substituteTyVars subst1 `traverse` d2
--   d2' `subtypeOfD_` t2'
-- d@(Distribution denom ls) `subtypeOfD_` SzCon n ts2 ix2 = do
--   sig <- Map.filterWithKey (\ f _ -> isConstructor f) <$> simpleSignature
--   if null (contraVariant sig n ts2) then do
--     require (Ix.Mult denom ix2 :>=: Ix.Sum [ Ix.Mult p ix | (p, SzCon _ _ ix) <- ls])
--     let ds = [Distribution denom d' | d' <- transpose [ [(p,t) | t <- ts] | (p,SzCon _ ts _) <- ls]]
--     foldM (\ subst (da,t) -> do
--               da' <- substituteTyVars subst `traverse` da
--               t' <- substituteTyVars subst t
--               subst' <- da' `subtypeOfD_` t'
--               subst' `after` subst) [] (zip ds ts2)
      
--   else throwError (UnsupportedDType d)
-- d `subtypeOfD_` _ = throwError (UnsupportedDType d)

subtypeOf :: (TSubstitute (SizeType knd Ix.Term), IsSymbol f) => SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG f v TSubst
SzVar v1 `subtypeOf` SzVar v2 | v1 == v2 = return []
SzVar v  `subtypeOf` t = do
  t' <- soSubType t
  return [ (v, toSchema t') ]
t `subtypeOf` SzVar v = do
  t' <- soSuperType t
  return [ (v, toSchema t') ]
SzCon n ts1 ix1 `subtypeOf` SzCon m ts2 ix2 | n == m = do
  require (ix2 :>=: ix1)
  sig <- Map.filterWithKey (\ f _ -> isConstructor f) <$> simpleSignature
  let l = zip (variant sig n ts1) (variant sig n ts2)
          ++ zip (contraVariant sig n ts2) (contraVariant sig n ts1)
  foldM (\ subst (s1,s2) -> do
            s1' <- substituteTyVars subst s1
            s2' <- substituteTyVars subst s2
            subst' <- s1' `subtypeOf` s2'
            subst' `after` subst) [] l
SzArr n p `subtypeOf` SzArr m q = do
  subst1 <- m `subtypeOf` n
  p' <- substituteTyVars subst1 p
  q' <- substituteTyVars subst1 q
  subst2 <- p' `subtypeOf` q'
  subst2 `after` subst1
s1@SzQArr{} `subtypeOf` s2@SzQArr{} = do
  t1 <- instantiate s1
  (vs,t2) <- matrix s2
  subst <- t1 `subtypeOf` t2
  mvs1 <- metaVars <$> substituteTyVars subst t1
  mvs2 <- metaVars <$> substituteTyVars subst t2
  void (logBlk (PP.text "occurs check") (notOccur vs `mapM` (mvs1 ++ mvs2)))
  return subst
SzPair s1 s2 `subtypeOf` SzPair t1 t2 = do
  subst1 <- s1 `subtypeOf` t1
  s2' <- substituteTyVars subst1 s2
  t2' <- substituteTyVars subst1 t2
  subst2 <- s2' `subtypeOf` t2'
  subst2 `after` subst1
s `subtypeOf` n = throwError (MatchFailure s n)


inferExpression,inferExpression_ :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  TypingContext v -> SizeTypedExpression f v -> InferCG f v (TypingContext v, TSubst, Type Ix.Term)
inferExpression = inferExpression_
inferExpression_ ctx t@(Var v _) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= either return instantiate 
  return (ctx,idSubst,tp)
inferExpression_ ctx (Fun (_,s) _ _) = do
  tp <- rename s >>= instantiate
  return (ctx,idSubst,tp)
inferExpression_ ctx (Pair _ t1 t2) =  do
  (ctx1, s1, tp1) <- inferExpression ctx t1
  (ctx2, s2, tp2) <- inferExpression ctx1 t2
  let tp = SzPair tp1 tp2
  s <- s2 `after` s1
  return (ctx2, s, tp)
inferExpression_ ctx (Apply _ t1 t2) = do
  (ctx1, s1, tp1) <- inferExpression ctx t1
  case tp1 of
    SzArr sArg tBdy -> do
      (vs,tArg) <- matrix sArg
      notOccur vs `mapM_` concatMap metaVars (sArg : [ tp | (v, Right tp) <- Map.toList ctx1,  v `elem` fvars t2 ])
      (ctx2,s2,tp2) <- inferExpression ctx1 t2
      s3 <- tp2 `subtypeOf` tArg
      ctx2' <- substituteTyVars s3 ctx2
      tBdy' <- substituteTyVars s3 tBdy
      s <- foldM after s3 [s2,s1]
      return (ctx2',s,tBdy')
    _ -> throwError (IlltypedTerm t1 "function type" tp1)
inferExpression_ ctx (If _ tg tt te) = do
  (ctx1, s1, _) <- inferExpression ctx tg
  (ctx2, s2, tpt) <- inferExpression ctx1 tt
  tp <- soSuperType tpt
  (ctx3, s3, tpe) <- inferExpression ctx2 te
  s4 <- tpe `subtypeOf` tp
  ctx' <- substituteTyVars s3 ctx3
  s <- foldM after s4 [s3,s2,s1]
  return (ctx', s, tp)
inferExpression_ ctx (Choice tp (Distribution r ds)) = do
  (ctx',s',tps) <- walk [] ctx idSubst cs
  (ctx',s',) <$> expectedType tp (Distribution r (zip rs tps))
    where
      (rs,cs) = unzip ds
      walk tps c s [] = return (c,s,tps)
      walk tps c s (d:ds') = do
        (c',s',tp') <- inferExpression c d
        tps' <- substituteTyVars s' `mapM` tps
        s'' <- s' `after` s
        walk (tp':tps') c' s'' ds'
inferExpression_ ctx (Case stp g cs) = do
  let stpa = typeOf g :-> stp
  ns <- abstractSchema ctx stpa
  let fn = Fun (Lam,ns) stpa emptyLoc
  logMsg $ PP.pretty fn PP.<+> PP.text "::" PP.<+> PP.pretty ns
  ctx1 <- checkEquations ctx [(Apply stp fn p, e) | (p,e) <- cs]
  inferExpression ctx1 (Apply stp fn g)
  
inferExpression_ ctx (LetP _ t1 ((x,_),(y,_)) t2) = do
  (ctx1,s1,tp1) <- inferExpression ctx t1
  case tp1 of
    SzPair tpx tpy -> do
      let ctx1' = Map.insert x (Left tpx) (Map.insert y (Left tpy) ctx1)
          adj v c = case Map.lookup v ctx1 of
                      Nothing -> Map.delete v c
                      Just tp -> Map.insert v tp c
      (ctx2,s2,tp) <- inferExpression ctx1' t2
      s <- s2 `after` s1
      return (adj x (adj y ctx2),s,tp)
    _ -> throwError (IlltypedTerm t1 "pair type" tp1)


checkEquation :: (IsSymbol f, PP.Pretty f, PP.Pretty v, Ord f, Ord v) =>
  TypingContext v -> (SizeTypedExpression f v, SizeTypedExpression f v) -> InferCG f v (TypingContext v, TSubst)
checkEquation initialctx (l,r) = do
  FP fpctx tpfp <- liftInferM (footprint l)
  logBlk (prettyObligation fpctx r tpfp) $ do 
    (ctx,s1,tpr) <- inferExpression (fpctx `Map.union` initialctx) r
    s2 <- tpr `subtypeOf` tpfp
    ctx' <- substituteTyVars s2 ctx
    s <- s2 `after` s1
    return (ctx', s)
      where
        prettyObligation ctx e t = PP.group $ PP.nest 2 $
          PP.pretty ctx PP.<+> PP.text "⊦" 
          PP.<$> PP.nest 2 (PP.group (PP.pretty e PP.<$> PP.text ":" PP.<+> PP.pretty t))
  
checkEquations :: (IsSymbol f, PP.Pretty f, PP.Pretty v, Ord f, Ord v) =>
  TypingContext v -> [(SizeTypedExpression f v, SizeTypedExpression f v)] -> InferCG f v (TypingContext v)
checkEquations ctx [] = return ctx
checkEquations ctx (eq:eqs) = do
  (ctx1,_) <- checkEquation ctx eq
  checkEquations ctx1 eqs

generateConstraints :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  Signature f Ix.Term -> Program f v -> UniqueT IO (Either (SzTypingError f v) SOCS, ExecutionLog)
generateConstraints sig p =
  runInferM (signature p) $ logBlk "Type Inference" $ concatMapM typeEquation (equations p)
  
  where
    typeEquation (eqEqn -> eq) = execInferCG $ 
      void (checkEquation Map.empty (annotateEq eq))
      
    annotateEq eq = (annotate (lhs eq), annotate (rhs eq))
    annotate = mapExpression fun var
    fun f tp _ = ((F f, fromMaybe err (Map.lookup f sig) ),tp) where
      err = error $ "no sized type assigned to " ++ show (PP.pretty f)
    var v tp = (v,tp)

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m 
    | Map.null m = PP.text "Ø"
    | otherwise = PP.encloseSep PP.empty PP.empty (PP.text ", ") bindings where
        bindings = [ PP.pretty v PP.<+> PP.text ":" PP.<+> either PP.pretty PP.pretty e | (v,e) <- Map.toList m ]

instance PP.Pretty a => PP.Pretty (Distribution a) where
  pretty (Distribution d ls) =
    PP.encloseSep (PP.text "{") (PP.text "}") (PP.text "; ")
    [ppRatio p PP.<+> PP.text ":" PP.<+> PP.pretty a | (p,a) <- ls ]
      where
        ppRatio p = PP.int p PP.<> PP.text "/" PP.<> PP.int d

instance {-# OVERLAPPING #-} PP.Pretty TSubst where
  pretty [] = PP.text "Ø"
  pretty l = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "↦" PP.<+> PP.pretty tp | (x,tp) <- l]
  
instance {-# OVERLAPPING #-} (PP.Pretty f) => PP.Pretty (f,Schema ix) where
  pretty (f,_) = PP.pretty f
  
instance PP.Pretty v => PP.Pretty (Footprint v) where
  pretty (FP ctx tp) = 
    PP.parens (PP.tupled [PP.pretty ctx,PP.pretty tp])
