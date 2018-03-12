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
       final <- Set.member f . fst <$> get
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
    checkL = walk [] identSubst where
      walk tts subst env [] _ = return (tts,env,subst)
      walk tts subst env (t:ts) tp = do
        (t',env',subst') <- check env t tp
        walk (t' : substitute subst' `map` tts) (subst' `o` subst) env' ts (substitute subst' tp)
        
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
    infer env (If _ g t e) = do
      (tg, env1, subst1) <- check env g tyBool
      (tt, env2, subst2) <- infer env1 t
      (te, env3, subst3) <- infer env2 e
      return (ite (substitute (subst3 `o` subst2) tg) (substitute subst3 tt) te, env3, subst3 `o` subst2 `o` subst1)
    infer env (Choice _ (Distribution d ps)) = do
      let (rs,ts) = unzip ps
      v <- freshTyExp
      (tts, env', subst) <- checkL env ts v
      return (choice (Distribution d (zip rs tts)), env',subst)
    infer env (Case _ g cs) = do
      (tg, env1, subst1) <- infer env g
      v <- freshTyExp
      (tcs,env2,subst2) <- walk [] env1 subst1 cs (typeOf tg) v
      return (caseE (substitute subst2 tg) tcs, env2,subst2)
      where
        walk tcs e s [] _ _           = return (tcs,e,s)
        walk tcs e s ((c,t):cs') tg tp = do
          (tc,e1,s1) <- check Map.empty c tg
          (tt,_,s2) <- check (e1 `Map.union` substitute s1 e) t (substitute s1 tp)
          let s21 = s2 `o` s1
          walk ((substitute s2 tc,tt) : substitute s21 `map` tcs) (substitute s2 e1) (s21 `o` s) cs' (substitute s21 tg) (substitute s21 tp)
      
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

inferTypes :: (Ord v, Ord f, IsSymbol f) => [f] -> Signature f -> [UntypedEquation f v] -> Either (TypingError f v) (Program f v)    
inferTypes mainFns initialSig eqns = walk (callSCCs eqns) [] initialSig where
  walk []         teqs sig = return (Program teqs mainFns sig)
  walk (scc:sccs) teqs sig = do
    (teqs', sig') <- inferSCC sig scc
    walk sccs (teqs' ++ teqs) sig'
