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
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram hiding (Signature)
import           HoSA.Data.CallSite hiding (lhs, rhs)
import qualified HoSA.Data.CallSite as C
import           HoSA.Data.Index (Constraint(..))
import qualified HoSA.Data.Index as Ix
import           HoSA.Data.SizeType
import           HoSA.SizeType.SOConstraint (SOCS (..))



--------------------------------------------------------------------------------
-- common types
--------------------------------------------------------------------------------

type TypingContext v = Map v (Either (Type Ix.Term) (Schema Ix.Term))

type SizeTypedExpression f v = Expression f v (Schema Ix.Term)

data Footprint v = FP (TypingContext v) (Type Ix.Term)

data Obligation f v = TypingContext v :- (SizeTypedExpression f v,Type Ix.Term)
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
  IllformedLhs :: SizeTypedExpression f v -> SzTypingError f v
  IllformedRhs :: SizeTypedExpression f v -> SzTypingError f v
  IlltypedTerm :: SizeTypedExpression f v -> String -> SizeType knd Ix.Term -> SzTypingError f v
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

-- abstract signature
--------------------------------------------------------------------------------


abstractSchema :: MonadUnique m => Int -> SimpleType -> m (Schema Ix.Term)
abstractSchema width = runUniqueT . annotate
  where
    freshVarIds n = map uniqueToInt <$> uniques n

    empty = (Set.empty,Set.empty)
    
    toList (s1,s2) = Set.toList s1 ++ Set.toList s2
    
    (s1,s2) `union` (t1,t2) = (s1 `Set.union` t1, s2 `Set.union` t2)
    
    (s1,s2) \\ (t1,t2) = (s1 Set.\\ t1, s2 Set.\\ t2)

    add Clock vs (vsb,vsc) = (vsb, Set.fromList vs `Set.union` vsc)
    add BT{}  vs (vsb,vsc) = (Set.fromList vs `Set.union` vsb, vsc)
    
    select Clock (vsb,vsc) = vsb `Set.union` vsc
    select BT{}  (vsb,_) = vsb


    annotateBaseTerm vs bt = SzBase bt <$> ixTerm where
      ixTerm = Ix.Fun <$> lift uniqueSym <*> return (Ix.bvar `map` ixVars)
      ixVars = Set.toList (select bt vs)

    annotate tp = close <$> annotateToplevel empty tp
      where
        close :: ((Set.Set Ix.VarId,Set.Set Ix.VarId), Type Ix.Term) -> Schema Ix.Term
        close (_, SzBase bt ix) = SzBase bt ix
        close (vs, SzArr n p) = SzQArr (toList vs) n p
    
    -- returns: free variables (normal, settype), type
    annotateToplevel vs (TyBase bt) =
      (empty,) <$> annotateBaseTerm vs bt
    annotateToplevel vs (tp1 :*: tp2) = do
      (fvs1, t1) <- annotateToplevel vs tp1
      (fvs2, t2) <- annotateToplevel vs tp2
      return (fvs1 `union` fvs2, SzPair t1 t2)
    annotateToplevel vs (n :-> p) = do
      (fvsn, n') <- annotateSchema vs n
      (fvsp, p') <- annotateToplevel (fvsn `union` vs) p
      return (fvsn `union` fvsp, SzArr n' p')

    -- returns: free variables, schema
    annotateSchema _ (TyBase bt) = do
      [i] <- freshVarIds 1
      return (add bt [i] empty, SzBase bt (Ix.bvar i))
    annotateSchema vs (n :-> p) = do
      (nvs, pvs, SzArr n' p') <- annotateArr vs n p
      return (pvs \\ nvs, SzQArr (toList nvs) n' p')
    
    -- returns: negative free variables, positive free variables, type
    annotateType vs (TyBase bt) = do
      is <- freshVarIds width
      let vs' = add bt is vs
      (empty, vs',) <$> annotateBaseTerm vs' bt
    annotateType vs (tp1 :*: tp2) = do
      (fvsn1, fvsp1, t1) <- annotateType vs tp1
      (fvsn2, fvsp2, t2) <- annotateType vs tp2
      return (fvsn1 `union` fvsn2, fvsp1 `union` fvsp2, SzPair t1 t2)
    annotateType vs (n :-> p) = annotateArr vs n p

    -- returns: negative free variables, positive free variables, type
    annotateArr vs n p = do
      (fvsn, n') <- annotateSchema vs n
      (nvsp, pvsp, p') <- annotateType (fvsn `union` vs) p
      return (fvsn `union` nvsp, pvsp, SzArr n' p')        


  
-- abstractSignature :: (Eq v, Ord f, PP.Pretty f) =>
--   Map f SimpleType -> CSAbstract f -> Int -> [f] -> [AnnotatedRule f v] -> InferM f v (Signature f Ix.Term)
-- abstractSignature ssig abstr width fs ars = logBlk "Abstract Signature" $ do 
--     ccs <- callContexts abstr ars <$> sequence [ maybe (declMissing f) return (initialCC f <$> Map.lookup f ssig) | f <- fs]
--     signatureFromList <$> sequence [ do s <- maybe (declMissing f) (abstractSchema width) (Map.lookup f ssig)
--                                         logMsg (cc ::: s)
--                                         return (cc,s)
--                                    | cc <- ccs
--                                    , let f = ctxSym cc ]
--   where
--     declMissing = throwError . DeclarationMissing


-- inference
--------------------------------------------------------------------------------

matrix :: MonadUnique m => Schema Ix.Term -> m ([Ix.VarId], Type Ix.Term)
matrix (SzBase bt ix) = return ([],SzBase bt ix)
matrix (SzQArr ixs n p) = do
  ixs' <- sequence [ uniqueVar | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', SzArr (Ix.inst subst n) (Ix.inst subst p))

returnIndex :: MonadUnique m => SizeType knd Ix.Term -> m Ix.Term
returnIndex (SzBase _ ix) = return ix
returnIndex (SzArr _ p) = returnIndex p
returnIndex s@SzQArr{} = matrix s >>= returnIndex . snd
returnIndex SzPair{} = error "returnIndex on pairs not defined"

footprint :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => SizeTypedExpression f v -> InferM f v (Footprint v)
footprint l = logBlk "Footprint" $ fpInfer l
  where
    fpInfer t = do
      fp@(FP ctx tp) <- fpInfer_ t
      logMsg (PP.pretty ctx PP.<+> PP.text "⊦"
              PP.<+> PP.pretty t
              PP.<+> PP.text ":" PP.<+> PP.pretty tp)
      return fp
    fpInfer_ (Fun _ s _) =
      FP Map.empty . snd <$> matrix s
    fpInfer_ (Apply t1 t2) = do
      FP ctx1 tp1 <- fpInfer t1
      case tp1 of
        SzArr n p -> do
          (ctx2,s) <- fpCheck t2 n
          return (FP (ctx1 `Map.union` ctx2) (s `Ix.o` p))
        _ -> throwError (IlltypedTerm t1 "function type" tp1)
    fpInfer_ t = throwError (IllformedLhs l)

    fpCheck (Var v _) s =
      return (Map.singleton v (Right s), Ix.idSubst)
    fpCheck t (SzBase _ (Ix.Var (Ix.FVar i))) = do
      FP ctx tp <- fpInfer t
      case tp of
        SzBase _ a -> return (ctx, Ix.substFromList [(i,a)])
        _ -> throwError (IlltypedTerm t "base type" tp)
    fpCheck t tp = throwError (IlltypedTerm t "non-functional type" tp)

obligations :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => Signature f Ix.Term -> TypedProgram f v -> InferM f v [Obligation f v]
obligations sig p = mapM obligationsFor (eqEqn `map` equations p) where
  obligationsFor eq = do
    FP ctx tp <- footprint (toTypedExp (lhs eq))
    return (ctx :- (toTypedExp (rhs eq), tp))
  toTypedExp = mapExpression fun var
  fun f _ _ = (f, sig Map.! f)
  var v _ = (v,undefined)

skolemVar :: InferCG f v Ix.Term
skolemVar = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG f v (Type Ix.Term)
instantiate (SzBase bt ix) = return (SzBase bt ix)
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

inferSizeType :: (Ord f, Ord v, PP.Pretty f, PP.Pretty v) => TypingContext v -> SizeTypedExpression f v -> InferCG f v (Type Ix.Term)
inferSizeType ctx t@(Var v _) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= either return instantiate 
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty tp)    
  return tp
inferSizeType _ (Fun f s _) = do
  tp <- instantiate s
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty f PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
inferSizeType ctx t@(Pair t1 t2) =  do
  tp1 <- inferSizeType ctx t1
  tp2 <- inferSizeType ctx t2
  let tp = SzPair tp1 tp2
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty t PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
inferSizeType ctx t@(Apply t1 t2) =
  logBlk (PP.text "infer" PP.<+> PP.pretty t PP.<+> PP.text "...") $ do
  tp1 <- inferSizeType ctx t1
  case tp1 of
    SzArr sArg tBdy -> do
      (vs,tArg) <- matrix sArg
      notOccur vs `mapM` concatMap metaVars (sArg : [ tp | (v, Right tp) <- Map.toList ctx,  v `elem` fvarsDL t2 [] ])
      tp2 <- inferSizeType ctx t2
      tp2 `subtypeOf` tArg
      logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty t PP.<+> PP.text ":" PP.<+> PP.pretty tBdy)
      return tBdy
    _ -> throwError (IlltypedTerm t1 "function type" tp1)
inferSizeType ctx t@(LetP t1 ((x,_),(y,_)) t2) =
  logBlk (PP.text "infer" PP.<+> PP.pretty t PP.<+> PP.text "...") $ do
  tp1 <- inferSizeType ctx t1
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty t1 PP.<+> PP.text ":" PP.<+> PP.pretty tp1)
  case tp1 of
    SzPair tpx tpy -> do
      let ctx' = Map.insert x (Left tpx) (Map.insert y (Left tpy) ctx)
      tp <- inferSizeType ctx' t2
      logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty t2 PP.<+> PP.text ":" PP.<+> PP.pretty tp)
      return tp
    _ -> throwError (IlltypedTerm t1 "pair type" tp1)

obligationToConstraints :: (PP.Pretty f, PP.Pretty v, Ord f, Ord v) => Obligation f v -> InferM f v SOCS
obligationToConstraints o@(ctx :- (t, tp)) =  logBlk o $ execInferCG $ do 
  tp' <- inferSizeType ctx t
  tp' `subtypeOf` tp


generateConstraints :: (IsSymbol f, Ord f, Ord v, PP.Pretty f, PP.Pretty v) =>
  Signature f Ix.Term -> TypedProgram f v -> UniqueT IO (Either (SzTypingError f v) SOCS, ExecutionLog)
generateConstraints sig p = runInferM $ do
  ocs <- logBlk "Orientation constraints" $ 
    obligations sig p >>= mapM obligationToConstraints
  ccs <- logBlk "Constructor constraints" $ execInferCG $ 
    forM_ (Map.toList sig) $ \ (f,s) -> 
        unless (isDefined f) $ do
           ix <- returnIndex s
           require (ix :=: Ix.ixSucc (Ix.ixSum [Ix.fvar v | v <- Ix.fvars ix]))
  return (mconcat (ccs:ocs))

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m
    | Map.null m = PP.text "Ø"
    | otherwise = PP.hcat $ PP.punctuate (PP.text ", ")
      [ PP.pretty v PP.<+> PP.text ":" PP.<+> either PP.pretty PP.pretty e | (v,e) <- Map.toList m ]
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Obligation f v) where
  pretty (ctx :- (t, s)) =
    PP.pretty ctx
    PP.<+> PP.text "⊦" PP.<+> PP.pretty t
    PP.<+> PP.text ":" PP.<+> PP.pretty s

instance PP.Pretty v => PP.Pretty (Footprint v) where
  pretty (FP ctx tp) =
    PP.parens (PP.pretty ctx PP.<> PP.comma PP.<+> PP.pretty tp)
