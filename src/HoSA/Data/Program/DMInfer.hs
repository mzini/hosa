module HoSA.Data.Program.DMInfer
  (
    -- * Inference
    inferTypes
  )
where

import           Control.Arrow (second)
import           Control.Monad.State
import           Control.Monad.Except
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Graph (stronglyConnComp, flattenSCC)

import           HoSA.Data.MLTypes
import           HoSA.Data.Program.Types
import           HoSA.Data.Program.Expression
import           HoSA.Data.Program.Equation
import           HoSA.Utils


newtype InferM f v a =
  InferM (StateT (Set.Set f, Signature f) (ExceptT (TypingError f v) UniqueM) a)
  deriving (  Applicative, Functor, Monad
            , MonadError (TypingError f v)
            , MonadState (Set.Set f, Signature f)
            , MonadUnique)

runInfer :: Signature f -> InferM f v a -> Either (TypingError f v) (a, Signature f)
runInfer sig (InferM m) = second snd <$> runUniqueWithout vs (runExceptT (runStateT m (Map.keysSet sig, sig)))
  where
    vs = foldl (flip fvsDL) [] (Map.elems sig)

    -- TODO
  -- subst <- fromMap <$> setConstructors [ (c,substitute s1 d) | (c,d) <- M.toList sig, isConstructor c ]
  --   setConstructors tps = fst <$> execStateT (setConstructor `mapM` tps) (M.empty,0 :: Int)
  --   setConstructor (c,returnType -> TyVar v)   = modify f where
  --     f (m,i) = case M.lookup v m of
  --                 Nothing -> (M.insert v (TyBase (BT (i + 1))) m, i+1)
  --                 Just {} -> (m,i)
  --   setConstructor (c,returnType -> TyBase {}) = return ()
  --   setConstructor (c,returnType -> TyCon {})  = return ()    
  --   setConstructor (c,tp)                      = throwError (IllformedConstructorType c tp)
      

freshTyExp :: MonadUnique m => m SimpleType
freshTyExp = TyVar <$> unique

lookupFunTpe :: (Ord f, IsSymbol f) => f -> InferM f v SimpleType
lookupFunTpe f = do
  (_,env) <- get
  maybe create return (Map.lookup f env) >>= inst
  where
    create | isDefined f = do
               tp <- freshTyExp
               modify (second (Map.insert f tp))
               return tp
           | otherwise = throwError (ConstructorMissingSignature f)
    inst tp = do
       final <- Set.member f <$> fst <$> get
       if final
         then do 
         s <- substFromList <$> sequence [ (v,) <$> freshTyExp | v <- fvs tp ]
         return (substitute s tp)
         else return tp
  
unifyM :: UntypedEquation f v -> UntypedExpression f v -> SimpleType -> SimpleType -> InferM f v TypeSubstitution
unifyM rl a tp1 tp2 = 
  case unifyType [(tp1,tp2)] of
    Left (tp1',tp2') -> throwError (IncompatibleType rl a tp1' tp2')
    Right s -> modify (second (substitute s)) >> return s

-- TODO 
inferEquation :: (Ord v, Ord f, IsSymbol f) => UntypedEquation f v -> InferM f v (TypedEquation f v, TypeSubstitution)
inferEquation rl = do
  (lhs', env1, subst1) <- infer Map.empty (lhs rl)
  (rhs', env2, subst2) <- check env1 (rhs rl) (typeOf lhs')
  return (TypedEquation env2 (Equation (substitute subst2 lhs') rhs') (typeOf rhs')
         , subst2 `o` subst1)
  where
    fromEnv env v = 
      case Map.lookup v env of
        Nothing -> do
          tp <- freshTyExp
          return (Map.insert v tp env, tp)
        Just tp -> return (env, tp)

    check env t tp = do
      (t',env',subst') <- infer env t
      substr <- unifyM rl t (typeOf t') (substitute subst' tp)
      return (substitute substr t', substitute substr env', substr `o` subst')


    infer env (Var v _) = do
      (env1,tp) <- fromEnv env v
      return (Var v tp, env1, identSubst)
    infer env (Fun f _ l) = do
      tp <- lookupFunTpe f
      return (Fun f tp l, env, identSubst)
    infer env (Pair _ s1 s2) = do
      (t1, env1, subst1) <- infer env s1
      (t2, env2, subst2) <- infer env1 s2
      return (pair (substitute subst2 t1) t2, env2, subst2 `o` subst1)
    infer env (Apply _ s1 s2) = do
      v1 <- freshTyExp
      v2 <- freshTyExp
      (t1, env1, subst1) <- check env s1 (v1 :-> v2)
      (t2, env2, subst2) <- check env1 s2 (substitute subst1 v1)
      return (apply (substitute subst2 t1) t2, env2, subst2 `o` subst1)
    infer env (LetP _ s1 ((x,_),(y,_)) s2) = do
      v1 <- freshTyExp
      v2 <- freshTyExp
      (t1, env1, subst1) <- check env s1 (v1 :*: v2)
      let tpx = substitute subst1 v1
          tpy = substitute subst1 v2
          adj v s e = case Map.lookup v env1 of
                        Nothing -> Map.delete v e
                        Just tp -> Map.insert v (substitute s tp) e
          env1' = Map.insert x tpx (Map.insert y tpy env1)
      (t2, env2, subst2) <- infer env1' s2
      return (letp (substitute subst2 t1) (x, y) t2
             , adj x subst2 (adj y subst2 env2)
             , subst2 `o` subst1)

inferSCC :: (Ord v, Ord f, IsSymbol f) => Signature f -> [UntypedEquation f v] -> Either (TypingError f v) ([TypedEquation f v],Signature f)
inferSCC startSig eqns = runInfer startSig (walk [] eqns) where
  walk teqs [] = return teqs
  walk teqs (eq:eqs) = do
    (teq,subst) <- inferEquation eq
    walk (teq : substitute subst `map` teqs) eqs


callSCCs :: Eq f => [UntypedEquation f v] -> [[UntypedEquation f v]]
callSCCs eqs = map flattenSCC sccs'
  where
    sccs' = stronglyConnComp [ (eq, i, succs eq) | (i, eq) <- eeqs ]
    eeqs = zip [ 0::Int ..] eqs
    succs eq = [ j | (j, eq') <- eeqs
                   , dsym eq' `elem` dsym eq : funs (rhs eq) ]
      where dsym = fst . definedSymbol

inferTypes :: (Ord v, Eq f, Ord f, IsSymbol f) => [f] -> Signature f -> [UntypedEquation f v] -> Either (TypingError f v) (Program f v)    
inferTypes mainFns initialSig eqns = walk (callSCCs eqns) [] initialSig where
  walk []         teqs sig = return (Program teqs mainFns sig)
  walk (scc:sccs) teqs sig = do
    (teqs', sig') <- inferSCC sig scc
    walk sccs (teqs' ++ teqs) sig'
