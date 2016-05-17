module HoSA.Data.SimpleType
  ( 
    BaseType (..)
  , SimpleType
  , ST (..)
  , Env
  , STRule (..)
  , STAtrs (..)
  , inferSimpleType
  , TypingError (..))
where

import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Arrow ((***), second)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Rewriting.Applicative.Term as T
import           HoSA.Data.Rewriting
import           HoSA.Utils
----------------------------------------------------------------------
-- Type
----------------------------------------------------------------------

newtype BaseType = BT Int deriving (Eq, Ord)

type TypeVariable = Unique
data V = NG | G

data ST g where
  TyBase :: BaseType -> ST g
  TyVar  :: TypeVariable -> TyExp
  TyPair :: ST g -> ST g -> ST g
  (:->)  :: ST g -> ST g -> ST g

deriving instance Eq (ST g)

type SimpleType = ST G
type TyExp = ST NG
  
type Env x = M.Map x TyExp

fvs :: TyExp -> [TypeVariable]
fvs TyBase{} = []
fvs (TyVar v) = [v]
fvs (TyPair tp1 tp2) = fvs tp1 ++ fvs tp2
fvs (tp1 :-> tp2) = fvs tp1 ++ fvs tp2

----------------------------------------------------------------------
-- Simply Typed ATRS
----------------------------------------------------------------------

type STTerm = TypedTerm SimpleType SimpleType


data STRule = STRule { strEnv       :: M.Map Variable SimpleType
                     , strRule      :: Rule
                     , strTypedRule :: TypedRule SimpleType SimpleType
                     , strType      :: SimpleType }
                  
data STAtrs = STAtrs { rules :: [STRule]
                     , signature :: M.Map FunId SimpleType} 


typeOf :: STTerm -> SimpleType
typeOf (T.Fun (Sym (Tuple ::: tp)) _) = tp
typeOf (T.Fun (Sym (Symbol _ ::: tp)) []) = tp
typeOf (T.Fun App [t1,t2]) =
  case typeOf t1 of
    _ :-> tp -> tp
    _ -> error "SimpleType.typeOf: ill-typed applicant"

withType :: M.Map Variable SimpleType -> M.Map FunId SimpleType -> Term -> STTerm
withType env _   (view -> Var v) = tvar v (env M.! v)
withType _   sig (view -> Const f) = tfun f (sig M.! f)
withType env sig (view -> Pair t1 t2) = ttuple tt1 tt2 tp where
      tt1 = withType env sig t1
      tt2 = withType env sig t2
      tp = TyPair (typeOf tt1) (typeOf tt2)
withType env sig (view -> Appl t1 t2) = withType env sig t1 `app` withType env sig t2


----------------------------------------------------------------------
-- Type Substitution
----------------------------------------------------------------------

type Substitution = TypeVariable -> TyExp

class Substitutable a where
  substitute :: Substitution -> a -> a


instance Substitutable TyExp where
  substitute _ tp@TyBase{} = tp
  substitute s (TyVar v) = s v
  substitute s (TyPair tp1 tp2) = TyPair (substitute s tp1) (substitute s tp2)
  substitute s (tp1 :-> tp2) = substitute s tp1 :-> substitute s tp2
  
instance Substitutable (Env x) where
  substitute s env = M.map (substitute s) env

instance (Substitutable a, Substitutable b) => Substitutable (a,b) where
  substitute s = substitute s *** substitute s

instance (Substitutable Substitution) where
  substitute s1 s2 = substitute s1 . s2
  
o :: Substitution -> Substitution -> Substitution
o = substitute

ident :: Substitution
ident = TyVar

singleton :: TypeVariable -> TyExp -> Substitution
singleton v tp = \ w -> if v == w then tp else TyVar w
  
unify :: [(a, (TyExp, TyExp))] -> Either (a, TyExp,TyExp) Substitution
unify = go ident where
  go s [] = return s
  go s ((a,(tp1,tp2)):ups) = do 
    (s',ups') <- step a tp1 tp2
    go (s' `o` s) (ups' ++ [(a',substitute s' up) | (a',up) <- ups])

  step _ tp1 tp2 | tp1 == tp2 = return (ident, [])
  step _ (TyVar v) tp2 | v `notElem` fvs tp2 = return (singleton v tp2, [])
  step a t v@(TyVar _) = step a v t
  step _ (TyBase bt1) (TyBase bt2) | bt1 == bt2 = return (ident, [])
  step a (tp1 :-> tp1') (tp2 :-> tp2') = return (ident, [(a,(tp1,tp2)),(a,(tp1',tp2'))])
  step a (TyPair tp1 tp1') (TyPair tp2 tp2') = return (ident, [(a,(tp1,tp2)),(a,(tp1',tp2'))])
  step a tp1 tp2 = Left (a,tp1,tp2)

unifyEnv :: Ord v => Env v -> Env v -> Either (v, TyExp, TyExp) Substitution
unifyEnv env1 env2 = unify (M.toList (M.intersectionWith (,) env1 env2))

----------------------------------------------------------------------
-- Inference
----------------------------------------------------------------------

data TypingError =
  IncompatibleVarType Rule (Variable,TyExp,TyExp)
  | IncompatibleType Rule (Term, TyExp, TyExp)
  | VariableCondition Rule Variable
    
newtype InferM a =
  InferM { runInferM_ :: StateT (Env FunId, Substitution) (ExceptT TypingError UniqueM) a }
  deriving (Applicative, Functor, Monad
            , MonadError TypingError
            , MonadState (Env FunId, Substitution)
            , MonadUnique)

runInfer :: InferM a -> Either TypingError a
runInfer = runUnique . runExceptT . flip evalStateT (M.empty,ident) . runInferM_

freshTy :: InferM TyExp
freshTy = TyVar <$> unique

lookupType :: FunId -> InferM TyExp
lookupType f = do
  (env,s) <- get
  case M.lookup f env of
    Nothing -> do
      tp <- freshTy
      put (M.insert f tp env,s)
      return tp
    Just tp -> return tp

inferRule :: Rule -> InferM (Env Variable, TyExp, Substitution)
inferRule rl = do
  (env,tp) <- footprint (lhs rl)
  s <- check env (rhs rl) tp
  modify (substitute s)
  return (substitute s env, substitute s tp, s)
    where
      footprint (view -> Var v) = do
        tp <- freshTy
        return (M.singleton v tp, tp)
      footprint (view -> Const f) = do
        tp <- lookupType f
        return (M.empty, tp)
      footprint (view -> Appl t1 t2) = do
        v1 <- freshTy
        v2 <- freshTy
        (env,u) <- mergeFP (t1,v1 :-> v2) (t2,v1)
        return (env, substitute u v2)
      footprint (view -> Pair t1 t2) = do
        v1 <- freshTy
        v2 <- freshTy
        (env,u) <- mergeFP (t1,v1) (t2,v2)
        return (env, substitute u (TyPair v1 v2))

      mergeFP (t1,rtp1) (t2,rtp2) = do
        (env1,tp1) <- footprint t1
        (env2,tp2) <- footprint t2
        uenv <- assertRight (IncompatibleVarType rl) (unifyEnv env1 env2)
        let tp1' = substitute uenv tp1
            tp2' = substitute uenv tp2
        utpe <- assertRight (IncompatibleType rl) (unify [(t1,(tp1',rtp1)), (t2, (tp2',rtp2))])
        let u = utpe `o` uenv
        modify (substitute u)
        return (substitute u (env1 `M.union` env2), u)
        
      check env t@(view -> Var v) tp = do
        tp' <- assertJust (VariableCondition rl v) (M.lookup v env)
        assertRight (IncompatibleType rl) (unify [(t,(tp,tp'))])
      check _ t@(view -> Const f) tp = do
        tp' <- lookupType f
        assertRight (IncompatibleType rl) (unify [(t,(tp,tp'))])
      check env t@(view -> Pair t1 t2) tp = do
        v1 <- freshTy
        v2 <- freshTy
        u <- assertRight (IncompatibleType rl) (unify [(t,(tp,TyPair v1 v2))])        
        s1 <- check (substitute u env) t1 (substitute u v1)
        s2 <- check (substitute u env) t2 (substitute u v2)
        return (s2 `o` s1 `o` u)
      check env (view -> Appl t1 t2) tp = do
        v <- freshTy
        s <- check env t2 v
        s' <- check (substitute s env) t1 (substitute s v :-> tp)
        return (s' `o` s)

inferSimpleType :: [Rule] -> Either TypingError STAtrs
inferSimpleType rs = toSTAtrs <$> runInfer (walk [] rs) where
  walk ls [] = do
    sig <- fst <$> get
    return (sig, ls)
  walk ls (rl:rls) = do
    (env,tp,s) <- inferRule rl
    walk ((rl, (env,tp)) : second (substitute s) `map` ls) rls

  toSTAtrs (sig, ls) = flip evalState (M.empty,0 :: Int) $ do
    gsig <- toGroundEnv sig
    strs <- toGroundSTRule gsig `mapM` ls 
    return STAtrs { rules = strs, signature = gsig }


  toGroundSTRule gsig (rl,(env,tp)) = do
    genv <- toGroundEnv env
    gtp <- toGroundTpe tp
    return STRule { strEnv = genv
                  , strRule = rl
                  , strTypedRule = rule (withType genv gsig (lhs rl)) (withType genv gsig (rhs rl))
                  , strType = gtp }

  toGroundEnv env = traverse toGroundTpe env

  toGroundTpe :: TyExp -> State (M.Map TypeVariable Int, Int) SimpleType 
  toGroundTpe (TyVar v) = TyBase <$> btForVar v
  toGroundTpe (TyBase bt) = return (TyBase bt)
  toGroundTpe (TyPair tp1 tp2) = TyPair <$> toGroundTpe tp1 <*> toGroundTpe tp2
  toGroundTpe (tp1 :-> tp2) = (:->) <$> toGroundTpe tp1 <*> toGroundTpe tp2
  
  btForVar v = do
    (m,i) <- get
    case M.lookup v m of
      Nothing -> do {put (M.insert v (i+1) m, i+1); return (BT (i + 1));}
      Just j -> return (BT j)
      
-- pretty printing

instance PP.Pretty BaseType where
  pretty (BT i) = PP.text (names !! i) where
    names = [ [c] | c <- ['A'..'Z'] ] ++ [ 'B' : show j | j <- [(1 :: Int)..] ]

instance PP.Pretty TypeVariable where
  pretty i = PP.text (names !! uniqueToInt i) where
    names = [ [c] | c <- ['a'..'z'] ] ++ [ 'a' : show j | j <- [(1 :: Int)..] ]

instance PP.Pretty (ST g) where
  pretty = pp id
    where
      pp _ (TyBase bt) = PP.pretty bt
      pp _ (TyVar v) = PP.pretty v
      pp _ (TyPair tp1 tp2) = PP.tupled [pp id tp1, pp id tp2]
      pp paren (tp1 :-> tp2) = paren (pp PP.parens tp1 PP.<+> PP.text "->" PP.<+> pp id tp2)      

instance (PP.Pretty x) => PP.Pretty (M.Map x (ST g)) where
  pretty env = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "::" PP.<+> PP.pretty tp | (x,tp) <- M.toList env]


ppRuleErr :: Rule -> PP.Doc -> PP.Doc
ppRuleErr rl doc =
  PP.text "Typing error in rule:"
  PP.<$> PP.indent 2 (PP.pretty rl)
  PP.<$> doc
  
instance PP.Pretty TypingError where
  pretty (IncompatibleVarType rl (v,tp1,tp2)) =
    ppRuleErr rl $ 
    PP.text "The variable" PP.<+> PP.squotes (PP.pretty v)
    PP.<+> PP.text "is used with two incompatible types, namely"
    PP.<+> PP.squotes (PP.pretty tp1) PP.<+> PP.text "and" PP.<+> PP.squotes (PP.pretty tp2) PP.<> PP.text "."
  pretty (IncompatibleType rl (t,tp1,tp2)) =
    ppRuleErr rl $           
    PP.text "The term" PP.<+> PP.pretty t
    PP.<+> PP.text "has type"
    PP.<+> PP.squotes (PP.pretty tp1)
    PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty tp2) PP.<+> PP.text "is expected."
  pretty (VariableCondition rl v) =
    ppRuleErr rl $
    PP.text "The variable" PP.<+> PP.squotes (PP.pretty v)
    PP.<+> PP.text "does not occur in the left-hand side."    
    

