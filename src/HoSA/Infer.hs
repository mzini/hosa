module HoSA.Infer where

import           Control.Monad.Except
import           Control.Monad.Trace
import           Control.Monad.Writer
import           Data.List (nub, (\\))
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Rewriting.Applicative.Rule as R
import qualified Data.Rewriting.Applicative.Rules as RS
import Data.Rewriting.Applicative.SimpleTypes ((:::)(..))
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import           Data.Rewriting.Applicative.Term
import           HoSA.CallSite
import HoSA.Index (Constraint(..))
import qualified HoSA.Index as Ix
import           HoSA.SizeType
import HoSA.Utils
import Data.Either (rights)
import qualified Constraints.Set.Solver as SetSolver
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Data.Tree

--------------------------------------------------------------------------------
-- common types
--------------------------------------------------------------------------------

type TypingContext v = Map v (Schema Ix.Term)

type Footprint f v = (TypingContext v, Type Ix.Term)

data Obligation f v = TypingContext v :- (TypedTerm f v ::: Type Ix.Term)
infixl 0 :-

type TypedTerm f v = ATerm (f ::: Schema Ix.Term) v

unType :: TypedTerm f v -> ATerm f v
unType = amap drp id where drp (f ::: _) = f


--------------------------------------------------------------------------------
-- inference monad
--------------------------------------------------------------------------------

type ExecutionLog = Forest String

newtype InferM f v a =
  InferM { runInferM_ :: ExceptT (TypingError f v) (TraceT String (UniqueT IO)) a }
  deriving (Applicative, Functor, Monad
            , MonadTrace String
            , MonadError (TypingError f v)
            , MonadUnique
            , MonadIO)

runInferM :: InferM f v a -> IO (Either (TypingError f v) a, ExecutionLog)
runInferM = runUniqueT . runTraceT . runExceptT . runInferM_
  
newtype InferCG f v a = InferCG { runInferCG_ :: WriterT [Constraint] (InferM f v) a }
  deriving (Applicative, Functor, Monad
            , MonadError (TypingError f v)
            , MonadWriter [Constraint]
            , MonadUnique
            , MonadTrace String
            , MonadIO)

execInferCG ::InferCG f v a -> InferM f v [Constraint]
execInferCG = execWriterT . runInferCG_

liftInferM ::InferM f v a -> InferCG f v a
liftInferM = InferCG . lift
  
record :: Constraint -> InferCG f v ()
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

data TypingError f v = 
  IllformedLhs (ATerm f v)
  | IllformedRhs (TypedTerm f v)
  | IlltypedTerm (TypedTerm f v) String
  | DeclarationMissing f

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
  pretty err = PP.text "Error in inference of size types. "
               PP.<$$> pp err
    where
      pp (IllformedLhs t) =
        PP.hang 2 (PP.text "Illformed left-hand side encountered:"
                   PP.</> PP.pretty t)
      pp (IllformedRhs t) =
        PP.hang 2 (PP.text "Illformed right-hand side encountered:"
                   PP.</> PP.pretty (unType t))
      pp (IlltypedTerm t s) =
        PP.hang 2 (PP.text "Ill-typed term:"
                   PP.</> PP.pretty (unType t)
                   PP.</> PP.text "Expecting:" PP.<+> PP.text s)
      pp (DeclarationMissing f) =
        PP.text "Type-declaration of symbol" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "missing."

-- abstract signature
--------------------------------------------------------------------------------


declToType td = foldr (ST.:~>) (ST.outputType td) (ST.inputTypes td)

abstractSchema :: Int -> ST.TypeDecl -> InferM f v (Schema Ix.Term)
abstractSchema width = runUniqueT . annotate . declToType
    where
      freshVarIds n = map uniqueToInt <$> uniques n 
      freshFun vs = Ix.Fun <$> lift uniqueSym <*> return (Ix.bvar `map` Set.toList vs)
      
      annotate tp = close <$> annotateToplevel Set.empty tp where
        close :: (Set.Set Ix.VarId,Type Ix.Term) -> Schema Ix.Term
        close (_, TyBase bt ix) = TyBase bt ix
        close (fvs,TyArr n p) = TyQArr (Set.toList fvs) n p

      -- returns: free variables, type
      annotateToplevel vs (ST.BT bt) = do
        t <- TyBase (BT bt) <$> freshFun vs
        return (Set.empty,t)
      annotateToplevel vs (n ST.:~> p) = do
        (fvsn, n') <- annotateSchema vs n
        (fvsp, p') <- annotateToplevel (fvsn `Set.union` vs) p
        return (fvsn `Set.union` fvsp, TyArr n' p')        
      
      -- returns: free variables, schema
      annotateSchema _ (ST.BT bt) = do
        [i] <- freshVarIds 1
        return (Set.singleton i,TyBase (BT bt) (Ix.bvar i))
      annotateSchema vs (n ST.:~> p) = do
        (nvs, pvs, TyArr n' p') <- annotateArr vs n p
        return (pvs Set.\\ nvs, TyQArr (Set.toList nvs) n' p')
        
      -- returns: negative free variables, positive free variables, type
      annotateType vs (ST.BT bt) = do
        is <- freshVarIds width
        let vs' = Set.fromList is `Set.union` vs
        ix <- freshFun vs'
        return (Set.empty, vs', TyBase (BT bt) ix)
      annotateType vs (n ST.:~> p) = annotateArr vs n p

       -- returns: negative free variables, positive free variables, type
      annotateArr vs n p = do
        (fvsn, n') <- annotateSchema vs n
        (nvsp, pvsp, p') <- annotateType (fvsn `Set.union` vs) p
        return (fvsn `Set.union` nvsp,pvsp, TyArr n' p')        


abstractSignature :: (PP.Pretty f, Ord f) => ST.Signature f -> CSAbstract f -> Int -> [f] -> [AnnotatedRule f v]
                     -> InferM f v (Signature f Ix.Term)
abstractSignature ssig abstr width fs ars = logBlk "Abstract Signature" $ do 
    ccs <- callContexts abstr ars <$> sequence [ maybe (declMissing f) return (initialCC f <$> declToType <$> Map.lookup f ssig) | f <- fs]
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
matrix (TyBase bt ix) = return ([],TyBase bt ix)
matrix (TyQArr ixs n p) = do
  ixs' <- sequence [uniqueVar | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', TyArr (Ix.inst subst n) (Ix.inst subst p))

returnIndex :: MonadUnique m => SizeType knd Ix.Term -> m Ix.Term
returnIndex (TyBase _ ix) = return ix
returnIndex (TyArr _ p) = returnIndex p
returnIndex s@TyQArr{} = matrix s >>= returnIndex . snd


footprint :: Ord v => TypedTerm f v -> InferM f v (Footprint f v)
footprint = walk where
  walk (aterm -> TConst (f ::: s)) = do
    let ctx = Map.empty
    tp <- snd <$> matrix s
    return (ctx, tp)
  walk (aterm -> t :@ Var x) = do
    (ctx,tp) <- walk t
    case tp of
      TyArr n p -> return (Map.insert x n ctx, p)
      _ -> throwError (IlltypedTerm t "arrow type")
  walk (aterm -> t1 :@ t2) = do
    (ctx1,tp1) <- walk t1
    (ctx2,tp2) <- walk t2
    case (tp1,tp2) of
      (TyArr (TyBase _ (Ix.Var (Ix.FVar i))) tp, TyBase _ a) ->
        let s = Ix.substFromList [(i,a)] in
        return (ctx1 `Map.union` ctx2, s `Ix.o` tp)
      (_,TyArr _ _) -> throwError (IlltypedTerm t2 "base type")
      _ -> throwError (IlltypedTerm t1 "function on base type")


obligations :: (Ord f, Ord v)  => CSAbstract f -> Signature f Ix.Term -> [AnnotatedRule f v] -> InferM f v [Obligation f v]
obligations abstr sig ars = step `concatMapM` signatureToList sig where
  step (cc,s) =
    sequence [ do (ctx,tp) <- footprint l
                  return (ctx :- annotatedRhs cc (arhs arl) ::: tp)
             | arl <- ars
             , headSymbol (lhs arl) == Just (ctxSym cc)
             , l <- annotatedLhss s (lhs arl) ]
    
  annotatedLhss _ (aterm -> TVar v) = [var v]
  annotatedLhss s (aterm -> TConst f) = [fun (f ::: s) []]
  annotatedLhss s (aterm -> l1 :@ l2) = app <$> annotatedLhss s l1 <*> annotatedArgs l2 where
    annotatedArgs (aterm -> TVar v) = [var v]
    annotatedArgs (aterm -> TConst f) = [ fun (f ::: s') [] | (_,s') <- lookupSchemas f sig ]
    annotatedArgs (aterm -> t1 :@ t2) = app <$> annotatedArgs t1 <*> annotatedArgs t2

  annotatedRhs _ (aterm -> TVar v) = var v
  annotatedRhs cc (aterm -> TConst cs@(CallSite (f ::: _) _)) = fun (f ::: s) [] where
    Just s = lookupSchema (abstr cs cc) sig
  annotatedRhs cc (aterm -> t1 :@ t2) = app (annotatedRhs cc t1) (annotatedRhs cc t2)


skolemTerm :: InferCG f v Ix.Term
skolemTerm = Ix.metaVar <$> (unique >>= Ix.freshMetaVar)

instantiate :: Schema Ix.Term -> InferCG f v (Type Ix.Term)
instantiate (TyBase bt ix) = return (TyBase bt ix)
instantiate (TyQArr ixs n p) = do
  s <- Ix.substFromList <$> sequence [ (ix,) <$> skolemTerm | ix <- ixs]
  return (TyArr (Ix.inst s n) (Ix.inst s p))

subtypeOf :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> InferCG f v ()
t1 `subtypeOf` t2 = logBlk (PP.pretty t1 PP.</> PP.text "⊑" PP.<+> PP.pretty t2) $ t1 `subtypeOf_` t2

subtypeOf_ :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> InferCG f v ()
TyBase bt1 ix1 `subtypeOf_` TyBase bt2 ix2
  | bt1 == bt2 = record (ix2 :>=: ix1)
TyArr n p `subtypeOf_` TyArr m q = do
  m `subtypeOf_` n
  p `subtypeOf_` q
s@TyQArr{} `subtypeOf_` t@TyArr{} = do
  (_, t') <- matrix s
  t' `subtypeOf_` t
t@TyArr{} `subtypeOf_` s@TyQArr{} = do
  t' <- instantiate s
  t `subtypeOf_` t'
_ `subtypeOf_` _ = error "subtypeOf_: incompatible types"

infer :: (PP.Pretty f, PP.Pretty v, Ord v) => TypingContext v -> TypedTerm f v -> InferCG f v (Type Ix.Term)
infer ctx t@(aterm -> TVar v) = do
  tp <- assertJust (IllformedRhs t) (Map.lookup v ctx) >>= instantiate
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty tp)    
  return tp
infer _ (aterm -> TConst (f ::: s)) = do
  tp <- instantiate s
  logMsg (PP.text "Γ ⊦" PP.<+> PP.pretty f PP.<+> PP.text ":" PP.<+> PP.pretty tp)
  return tp
infer ctx t@(aterm -> t1 :@ t2) =
  logBlk (PP.text "infer" PP.<+> prettyATerm (unType t) PP.<+> PP.text "...") $ do
  tp1 <- infer ctx t1
  case tp1 of
    TyArr sArg tBdy -> do
      tp2 <- infer ctx t2
      tp2 `subtypeOf` sArg
      logMsg (PP.text "Γ ⊦" PP.<+> prettyATerm (unType t) PP.<+> PP.text ":" PP.<+> PP.pretty tBdy)
      return tBdy
    _ -> throwError (IlltypedTerm t1 "function type expected")
infer _ _ = error "HoSA.Infer.infer: illformed term given"    


obligationToConstraints :: (PP.Pretty v, PP.Pretty f, Ord v) => Obligation f v -> InferM f v [Constraint]
obligationToConstraints o =  do { cs <- logBlk o (check o); instantiateMetaVars cs; return cs } where
  check (ctx :- t ::: tp) = execInferCG $ do
    tp' <- infer ctx t
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



generateConstraints :: (PP.Pretty f, PP.Pretty v, Ord f, Ord v) => CSAbstract f -> Int -> Maybe [f] -> ST.STAtrs f v 
                    -> IO (Either (TypingError f v) (Signature f Ix.Term, [Constraint])
                          , [AnnotatedRule f v]
                          , ExecutionLog)
generateConstraints abstr width startSymbols sttrs = liftM withARS $ runInferM $ do
    let rs = ST.untypedRule `map` ST.rules sttrs
        ds = nub $ (headSymbol . R.lhs) `mapMaybe` rs
        cs = nub $ RS.funs rs \\ ds
        fs = fromMaybe ds startSymbols ++ cs
    sig <- abstractSignature (ST.signature sttrs) abstr width fs ars
    let css = [ s | (ctx,s) <- signatureToList sig, ctxSym ctx `elem` cs ]

    ocs <- logBlk "Orientation constraints" $ 
      obligations abstr sig ars >>= concatMapM obligationToConstraints
    ccs <- logBlk "Constructor constraints" $ execInferCG $ 
      forM_ css $ \ s -> do
        ix <- returnIndex s
        record (ix :>=: Ix.ixSucc (Ix.ixSum [Ix.fvar v | v <- Ix.fvars ix]))
    return (sig,ocs ++ ccs)
  where 
    withARS (s,cs) = (s,ars,cs)
    ars = withCallSites sttrs

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m
    | Map.null m = PP.text "Ø"
    | otherwise = PP.hcat $ PP.punctuate (PP.text ", ")
      [ PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty s | (v,s) <- Map.toList m ]
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Obligation f v) where
  pretty (ctx :- t ::: s) =
    PP.pretty ctx
    PP.<+> PP.text "⊦" PP.<+> prettyATerm (unType t)
    PP.<+> PP.text ":" PP.<+> PP.pretty s
