module HoSA.Infer where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.Supply
import           Control.Monad.Trans (lift)
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
import qualified Text.PrettyPrint.ANSI.Leijen as PP


--------------------------------------------------------------------------------
-- inference monad
--------------------------------------------------------------------------------

type TypingContext v = Map v (Schema Ix.Term)

type Footprint f v = (TypingContext v, Type Ix.Term)

data Obligation f v = TypingContext v :- (TypedTerm f v ::: Type Ix.Term)
infixl 0 :-


type TypedTerm f v = ATerm (f ::: Schema Ix.Term) v

unType :: TypedTerm f v -> ATerm f v
unType = amap drp id where drp (f ::: _) = f


newtype InferM f v a =
  InferM { runInferM_ :: LogT (WriterT [Ix.Constraint] (ExceptT (TypingError f v) (UniqueT IO))) a }
  deriving (Applicative, Functor, Monad
            , MonadWriter [Ix.Constraint]
            , MonadError (TypingError f v)
            , MonadIO)

runInferM :: InferM f v a -> IO (Either (TypingError f v) (a,[Constraint]))
runInferM = runUniqueT . runExceptT . runWriterT . runLogT . runInferM_

uniqueID :: InferM f v Unique
uniqueID = InferM (lift (lift (lift unique)))

uniqueSym :: InferM f v Ix.Sym
uniqueSym = Ix.Sym Nothing <$> uniqueID

uniqueVar :: InferM f v Ix.VarId
uniqueVar = uniqueToInt <$> uniqueID

logMsg :: (PP.Pretty e) => e -> InferM f v ()
logMsg e = InferM (logMessage e)

logBlk :: (PP.Pretty e) => e -> InferM f v a -> InferM f v a
logBlk e (InferM m) = InferM (logBlock e m)

record :: Constraint -> InferM f v ()
record cs = tell [cs] >> logMsg cs

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

abstractSchema :: Int -> ST.TypeDecl -> InferM f v (Schema Ix.Term)
abstractSchema width = runUniqueT . annotate . declToType
    where
      freshVarIds n = map uniqueToInt <$> uniques n 
      freshFun vs = Ix.Fun <$> lift uniqueSym <*> return (Ix.bvar `map` Set.toList vs)
      declToType td = foldr (ST.:~>) (ST.outputType td) (ST.inputTypes td)
      
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
      annotateSchema vs (ST.BT bt) = do
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


abstractSignature :: (Ord f) => ST.Signature f -> CSAbstract f -> Int -> [f] -> [AnnotatedRule f v]
                     -> InferM f v (Signature f Ix.Term)
abstractSignature ssig abstr width fs ars =
  signatureFromList <$> sequence [ (cc,) <$> maybe (declMissing f) (abstractSchema width) (Map.lookup f ssig)
                                 | cc@(CallCtx f _ _) <- ccs ]
  where
    ccs = callContexts abstr ars [initialCC f | f <- fs]
    declMissing = throwError . DeclarationMissing

  
-- inference
--------------------------------------------------------------------------------

matrix :: Schema Ix.Term -> InferM f v ([Ix.VarId], Type Ix.Term)
matrix (TyBase bt ix) = return ([],TyBase bt ix)
matrix (TyQArr ixs n p) = do
  ixs' <- sequence [uniqueVar | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', TyArr (Ix.inst subst n) (Ix.inst subst p))

returnIndex :: SizeType knd Ix.Term -> InferM f v Ix.Term
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
  step (cc@(CallCtx f i cs),s) =
    sequence [ do (ctx,tp) <- footprint l
                  return (ctx :- annotatedRhs cc (arhs arl) ::: tp)
             | arl <- ars
             , headSymbol (lhs arl) == Just f
             , l <- annotatedLhss s (lhs arl) ]
    
  annotatedLhss _ (aterm -> TVar v) = [var v]
  annotatedLhss s (aterm -> TConst f) = [fun (f ::: s) []]
  annotatedLhss s (aterm -> l1 :@ l2) = app <$> annotatedLhss s l1 <*> annotatedArgs l2 where
    annotatedArgs (aterm -> TVar v) = [var v]
    annotatedArgs (aterm -> TConst f) = [ fun (f ::: s) [] | (_,s) <- lookupSchemas f sig ]
    annotatedArgs (aterm -> t1 :@ t2) = app <$> annotatedArgs t1 <*> annotatedArgs t2

  annotatedRhs cc (aterm -> TVar v) = var v
  annotatedRhs cc (aterm -> TConst cs@(CallSite f _)) = fun (f ::: s) [] where
    Just s = lookupSchema (abstr cs cc) sig
  annotatedRhs cc (aterm -> t1 :@ t2) = app (annotatedRhs cc t1) (annotatedRhs cc t2)


skolemTerm :: [Ix.VarId] -> InferM f v (Ix.Term)
skolemTerm vs = Ix.Fun <$> uniqueSym <*> return (Ix.fvar `map` vs)

instantiate :: [Ix.VarId] -> Schema Ix.Term -> InferM f v (Type Ix.Term)
instantiate _ (TyBase bt ix) = return (TyBase bt ix)
instantiate fvs (TyQArr ixs n p) = do
  s <- Ix.substFromList <$> sequence [ (ix,) <$> skolemTerm fvs | ix <- ixs]
  return (TyArr (Ix.inst s n) (Ix.inst s p))

  
subtypeOf :: SizeType knd Ix.Term -> SizeType knd' Ix.Term -> InferM f v ()
TyBase bt1 ix1 `subtypeOf` TyBase bt2 ix2
  | bt1 == bt2 = record (ix2 :>=: ix1)
TyArr n p `subtypeOf` TyArr m q = do
  m `subtypeOf` n
  p `subtypeOf` q
s@TyQArr{} `subtypeOf` t@TyArr{} = do
  (_, t') <- matrix s
  t' `subtypeOf` t
t@TyArr{} `subtypeOf` s@TyQArr{} = do
  t' <- instantiate (fvars t) s
  t `subtypeOf` t'
_ `subtypeOf` _ = error "subtypeOf: incompatible types"

infer :: Ord v => TypingContext v -> TypedTerm f v -> InferM f v (Type Ix.Term)
infer ctx t@(aform -> (h,rest)) = do
  (ixs,hType) <- tpeOf h >>= matrix
  argInferred <- infer ctx `mapM` rest
  (argRequired,retType) <- assertJust (IlltypedTerm t "too many arguments supplied")
    (uncurryUpto hType (length rest))
  subst <- toSkolemSubst (estimateInstVars ixs argRequired argInferred)
  zipWithM subtypeOf (subst `Ix.o` argRequired) argInferred
  return (subst `Ix.o` retType)
    where
      tpeOf (Var v) = assertJust (IllformedRhs t) (Map.lookup v ctx)
      tpeOf (aterm -> TConst (_ ::: s)) = return s

      toSkolemSubst m =
        Ix.substFromList <$> sequence [(ix,) <$> skolemTerm (nub fvs) | (ix,fvs) <- Map.toList m]
      
      estimateInstVars ixs = walk (Map.fromList [(ix,[]) | ix <- ixs])  where
        walk m [] [] = m
        walk m (s:ss) (t:ts) = walk (extendFor s t m) ss ts
        extendFor s t = Map.unionWith (++) m' 
          where 
            m' = Map.fromList [ (ix,fvs) | ix <- fvars s, ix `elem` ixs]
            fvs = fvars t

generateConstraints :: (PP.Pretty f, PP.Pretty v, Ord f, Ord v) => CSAbstract f -> Int -> Maybe [f] -> ST.STAtrs f v ->
                       IO (Either (TypingError f v) (Signature f Ix.Term, [AnnotatedRule f v], [Constraint]))
generateConstraints abstr width startSymbols sttrs = do
  let ars = withCallSites sttrs
  res <- runInferM $ do
    let rs = ST.untypedRule `map` ST.rules sttrs
        ds = nub $ (headSymbol . R.lhs) `mapMaybe` rs
        cs = nub $ RS.funs rs \\ ds
        fs = fromMaybe ds startSymbols ++ cs
    sig <- abstractSignature (ST.signature sttrs) abstr width fs ars
    -- orientation constraints
    os <- obligations abstr sig ars
    forM os $ \ o@(ctx :- t ::: tp) -> do
      logBlk o $ do
        tp' <- infer ctx t
        tp' `subtypeOf` tp
    -- size constraints on constructors
    let css = [ s | (CallCtx c _ _,s) <- signatureToList sig, c `elem` cs ]
    forM css $ \ s -> do
      ix <- returnIndex s
      let fvars = [Ix.fvar v | v <- Ix.fvars ix]
      record (ix :>=: Ix.ixSum (Ix.ixSucc Ix.ixZero : fvars))
    return sig
  case res of
    Left e -> return (Left e)
    Right (s,cs) -> return (Right (s,ars,cs))

-- pretty printers
--------------------------------------------------------------------------------

instance PP.Pretty v => PP.Pretty (TypingContext v) where
  pretty m
    | Map.null m = PP.empty
    | otherwise = PP.hcat $ PP.punctuate (PP.text ", ")
      [ PP.pretty v PP.<+> PP.text ":" PP.<+> PP.pretty s | (v,s) <- Map.toList m ]
  
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Obligation f v) where
  pretty (ctx :- t ::: s) =
    PP.pretty ctx
    PP.<+> PP.text ":-" PP.<+> prettyATerm (unType t)
    PP.<+> PP.text ":" PP.<+> PP.pretty s
