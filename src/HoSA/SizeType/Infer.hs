module HoSA.SizeType.Infer where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.Trace
import           Control.Monad.Writer
import qualified Data.Map as Map
import           Data.Tree
import qualified Text.PrettyPrint.ANSI.Leijen as PP

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

type SizeTypedExpression f v = TypedExpression (f,Schema Ix.Term) v 

data Footprint v = FP (Map.Map v (Schema Ix.Term)) (Type Ix.Term)

data Obligation f v = TypingContext v :- (SizeTypedExpression f v,Type Ix.Term)
infixl 0 :-

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
  
newtype InferCG f v a = InferCG { runInferCG_ :: WriterT (SOCS) (InferM f v) a }
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

  -- notOccur vs `mapM` Ix.metaVars t2

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

-- variable supply and logging
--------------------------------------------------------------------------------

uniqueVar :: MonadUnique m => m Ix.VarId
uniqueVar = uniqueToInt <$> unique

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
  DeclarationMissing :: f -> SzTypingError f v

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (SzTypingError f v) where
  pretty (IllformedLhs t) =
    PP.hang 2 (PP.text "Illformed left-hand side encountered:"
               PP.</> PP.pretty t)
  pretty (IllformedRhs t) =
    PP.hang 2 (PP.text "Illformed right-hand side encountered:"
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


-- TODO
type TSubst = [(TypeVariable, Schema Ix.Term)]

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
  substituteTyVars subst (SzArr n p) = do
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
  substituteTyVars subst ctx = mapM f ctx where
    f (Left t) = Left <$> substituteTyVars subst t
    f (Right t) = Right <$> substituteTyVars subst t
  
logObligation :: MonadTrace PP.Doc m => (PP.Pretty f, PP.Pretty v) => Obligation f v -> m ()
logObligation = logMsg

footprint :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => SizeTypedExpression f v -> InferM f v (Footprint v)
footprint l = logBlk (PP.text "Footprint of" PP.<+> PP.squotes (PP.pretty l)) $ fpInfer l
  where
    fpInfer (Fun (_,s) _ _) = do
      (_, tp) <- rename s >>= matrix
      return (FP Map.empty tp)
    fpInfer (Apply _ t1 (Var v _)) = do
      FP ctx tp <- fpInfer t1
      case tp of
        SzArr n p -> return (FP (Map.insert v n ctx) p)
        _ -> throwError (IlltypedTerm t1 "function type" tp)
    fpInfer (Apply _ t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      FP ctx2 tp2 <- fpInfer t2
      case tp1 of
        SzArr n p -> do
          (si,st) <- fpMatch n tp2
          ctx1' <- mapM (substituteTyVars st) ctx1
          ctx2' <- mapM (substituteTyVars st) ctx2
          tp <- Ix.o (Ix.substFromList si)  <$> substituteTyVars st p
          return (FP (ctx1' `Map.union` ctx2') tp) 
        _ -> throwError (IlltypedTerm t1 "function type" tp1)
    fpInfer (Pair _ t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      FP ctx2 tp2 <- fpInfer t2
      return (FP (ctx1 `Map.union` ctx2) (SzPair tp1 tp2))
    fpInfer t = throwError (IllformedLhs t)

    fpMatch :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> InferM f v ([(Ix.VarId, Ix.Term)], [(TypeVariable, Schema Ix.Term)])
    fpMatch (SzVar v1)                         tp             = return ([],[(v1,toSchema tp)])
    fpMatch tp                                 (SzVar v2)     = return ([],[(v2,toSchema tp)])    
    fpMatch (SzCon n ss1 (Ix.Var (Ix.FVar i))) (SzCon m ss2 a) | n == m = do
          (sis,sts) <- unzip <$> zipWithM fpMatch ss1 ss2
          return ((i,a):concat sis, concat sts)
    fpMatch (SzPair s1 s2)                     (SzPair t1 t2) = do
      (si1,st1) <- fpMatch s1 t1
      (si2,st2) <- fpMatch s2 t2
      return (si1 ++ si2, st1 ++ st2)
    fpMatch s          n                     = throwError (MatchFailure s n)

obligations :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => Signature f Ix.Term -> Program f v -> InferM f v [Obligation f v]
obligations sig p = mapM obligationsFor (eqEqn `map` equations p) where
  obligationsFor eq = do
    FP ctx tp <- footprint (annotate (lhs eq))
    return (Map.map Right ctx :- (annotate (rhs eq), tp))
  annotate = mapExpression fun var
  fun f tp _ = ((f, sig Map.! f),tp)
  var v tp = (v,tp)

skolemVar :: InferCG f v Ix.Term
skolemVar = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG f v (Type Ix.Term)
instantiate s = do
  (vs,tp) <- matrix s
  subst <- Ix.substFromList <$> sequence [ (v,) <$> skolemVar | v <- vs]
  return (subst `Ix.o` tp)
-- instantiate (SzBase bt ix) = return (SzBase bt ix)
-- instantiate (SzList t ix) = SzList <$> (instantiate t) <*> return ix
-- instantiate (SzQArr ixs n p) = do
--   s <- Ix.substFromList <$> sequence [ (ix,) <$> skolemVar | ix <- ixs]
--   return (SzArr (Ix.inst s n) (Ix.inst s p))

subtypeOf :: (TSubstitute (SizeType knd Ix.Term), IsSymbol f) => SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG f v TSubst
t1 `subtypeOf` t2 = t1 `subtypeOf_` t2

subtypeOf_ :: (TSubstitute (SizeType knd Ix.Term), IsSymbol f) => SizeType knd Ix.Term -> SizeType knd Ix.Term -> InferCG f v TSubst
SzVar v1 `subtypeOf_` SzVar v2 | v1 == v2 = return []
SzVar v  `subtypeOf_` t = return [ (v, toSchema t) ]
t `subtypeOf_` SzVar v = return [ (v, toSchema t) ]
SzCon n ts1 ix1 `subtypeOf_` SzCon m ts2 ix2 | n == m = do
  require (ix2 :>=: ix1)
  sig <- Map.filterWithKey (\ f _ -> isConstructor f) <$> simpleSignature
  let l = zip (variant sig n ts1) (variant sig n ts2)
          ++ zip (contraVariant sig n ts2) (contraVariant sig n ts1)
  foldM (\ subst (s1,s2) -> do
            s1' <- substituteTyVars subst s1
            s2' <- substituteTyVars subst s2
            subst' <- s1' `subtypeOf` s2'
            subst' `after` subst) [] l
SzArr n p `subtypeOf_` SzArr m q = do
  subst1 <- m `subtypeOf` n
  p' <- substituteTyVars subst1 p
  q' <- substituteTyVars subst1 q
  subst2 <- p' `subtypeOf` q'
  subst2 `after` subst1
s1@SzQArr{} `subtypeOf_` s2@SzQArr{} = do 
  (vs,t1) <- matrix s1
  t2' <- instantiate s2
  subst <- t1 `subtypeOf` t2'
  mvs1 <- metaVars <$> substituteTyVars subst t1
  mvs2 <- metaVars <$> substituteTyVars subst t2'
  void (logBlk (PP.text "occurs check") (notOccur vs `mapM` (mvs1 ++ mvs2)))
  return subst
SzPair s1 s2 `subtypeOf_` SzPair t1 t2 = do
  subst1 <- s1 `subtypeOf` t1
  s2' <- substituteTyVars subst1 s2
  t2' <- substituteTyVars subst1 t2
  subst2 <- s2' `subtypeOf` t2'
  subst2 `after` subst1
s `subtypeOf_` n = throwError (MatchFailure s n)

inferSizeType :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) => TypingContext v -> SizeTypedExpression f v -> InferCG f v (TypingContext v, Type Ix.Term)
inferSizeType ctx t@(Var v _) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= either return instantiate 
  return (ctx,tp)
inferSizeType ctx t@(Fun (_,s) _ _) = do
  tp <- rename s >>= instantiate
  return (ctx,tp)
inferSizeType ctx t@(Pair _ t1 t2) =  do
  (ctx1, tp1) <- inferSizeType ctx t1
  (ctx2, tp2) <- inferSizeType ctx1 t2
  let tp = SzPair tp1 tp2
  return (ctx2,tp)
inferSizeType ctx t@(Apply _ t1 t2) = do
  (ctx1,tp1) <- inferSizeType ctx t1
  case tp1 of
    SzArr sArg tBdy -> do
      (vs,tArg) <- matrix sArg
      notOccur vs `mapM_` concatMap metaVars (sArg : [ tp | (v, Right tp) <- Map.toList ctx1,  v `elem` fvars t2 ])
      (ctx2,tp2) <- inferSizeType ctx1 t2
      subst <- tp2 `subtypeOf` tArg
      ctx2' <- substituteTyVars subst ctx2
      tBdy' <- substituteTyVars subst tBdy
      return (ctx2',tBdy')
    _ -> throwError (IlltypedTerm t1 "function type" tp1)
inferSizeType ctx t@(LetP _ t1 ((x,_),(y,_)) t2) = do
  (ctx1,tp1) <- inferSizeType ctx t1
  case tp1 of
    SzPair tpx tpy -> do
      let ctx1' = Map.insert x (Left tpx) (Map.insert y (Left tpy) ctx1)
          adj v c = case Map.lookup v ctx1 of
                      Nothing -> Map.delete v c
                      Just tp -> Map.insert v tp c
      (ctx2,tp) <- inferSizeType ctx1' t2
      return (adj x (adj y ctx2),tp)
    _ -> throwError (IlltypedTerm t1 "pair type" tp1)

obligationToConstraints :: (IsSymbol f, PP.Pretty f, PP.Pretty v, Ord f, Ord v) => Obligation f v -> InferM f v SOCS
obligationToConstraints ob@(ctx :- (t, tp)) =  logBlk ob $ execInferCG $ do 
  (_,tp') <- inferSizeType ctx t
  void (tp' `subtypeOf` tp)

generateConstraints :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  Signature f Ix.Term -> Program f v -> UniqueT IO (Either (SzTypingError f v) SOCS, ExecutionLog)
generateConstraints sig p = runInferM (signature p) $ do
  logBlk "Orientation constraints"
    (obligations sig p >>= concatMapM obligationToConstraints)

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m 
    | Map.null m = PP.text "Ø"
    | otherwise = PP.encloseSep PP.empty PP.empty (PP.text ", ") bindings where
        bindings = [ PP.pretty v PP.<+> PP.text ":" PP.<+> either PP.pretty PP.pretty e | (v,e) <- Map.toList m ]
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Obligation f v) where
  pretty (ctx :- (t, s)) = 
    PP.group (PP.nest 2 (PP.pretty ctx PP.<+> PP.text "⊦" 
                         PP.<$> PP.nest 2 (PP.group (PP.pretty t PP.<+> PP.text ":"
                                                     PP.<$> PP.pretty s))))

instance {-# OVERLAPPING #-} PP.Pretty TSubst where
  pretty [] = PP.text "Ø"
  pretty l = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "↦" PP.<+> PP.pretty tp | (x,tp) <- l]
  
instance {-# OVERLAPPING #-} (PP.Pretty f) => PP.Pretty (f,Schema ix) where
  pretty (f,_) = PP.pretty f
  
instance PP.Pretty v => PP.Pretty (Footprint v) where
  pretty (FP ctx tp) = 
    PP.parens (PP.tupled [PP.pretty ctx,PP.pretty tp])
