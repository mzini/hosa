module HoSA.Data.SimplyTypedProgram
  ( 
    BaseType (..)
  , SimpleType
  , ST (..)
  , Environment
  , Signature
  , TypedExpression
  , TypedEquation (..)
  , TypedProgram (..)
  , typeOf
  , tarity
  , progUnion
  , inferSimpleType
  , TypingError (..))
where

import           Data.Maybe (fromJust)
import qualified Data.Set as S
import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Arrow ((***), second)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           HoSA.Data.Expression
import           HoSA.Utils
----------------------------------------------------------------------
-- Type
----------------------------------------------------------------------

data BaseType = BT Int | Clock deriving (Eq, Ord)

type TypeVariable = Unique
data V = NG | G

data ST g where
  TyBase :: BaseType -> ST g
  TyVar  :: TypeVariable -> TyExp
  (:*:) :: ST g -> ST g -> ST g
  (:->)  :: ST g -> ST g -> ST g

infixr 5 :->
infixr 6 :*:

deriving instance Eq (ST g)
deriving instance Ord (ST g)

type SimpleType = ST G
type TyExp = ST NG
  
type Env x = M.Map x TyExp

fvs :: TyExp -> [TypeVariable]
fvs TyBase{} = []
fvs (TyVar v) = [v]
fvs (tp1 :*: tp2) = fvs tp1 ++ fvs tp2
fvs (tp1 :-> tp2) = fvs tp1 ++ fvs tp2

----------------------------------------------------------------------
-- Simply Typed ATRS
----------------------------------------------------------------------



type Environment v = M.Map v SimpleType
type Signature f = M.Map f SimpleType

type TypedExpression f v = Expression f v SimpleType

data TypedEquation f v = TypedEquation { eqEnv :: Environment v
                                       , eqEqn :: Equation f v SimpleType
                                       , eqTpe :: SimpleType }
                  
data TypedProgram f v = TypedProgram { equations :: [TypedEquation f v]
                                     , signature :: Signature f }
                                     -- , arity :: f -> Int } 

progUnion :: Ord f => TypedProgram f v -> TypedProgram f v -> TypedProgram f v
progUnion tp1 tp2 = TypedProgram { equations = equations tp1 ++ equations tp2
                             , signature = signature tp1 `M.union` signature tp2}
                  
symbols :: TypedProgram f v -> S.Set f 
symbols = M.keysSet . signature

tarity :: SimpleType -> Int
tarity TyBase{} = 0
tarity (_ :*: _) = 0
tarity (_ :-> tp) = 1 + tarity tp

typeOf :: TypedExpression f v -> SimpleType
typeOf (Var _ tp) = tp
typeOf (Fun _ tp _) = tp
typeOf (Pair t1 t2) = typeOf t1 :*: typeOf t2
typeOf (Apply t1 t2) =
  case typeOf t1 of
    _ :-> tp -> tp
    _ -> error "SimpleType.typeOf: ill-typed applicant"
typeOf (LetP _ _ t2) = typeOf t2


-- withType :: (Ord v, Ord f) => Environment -> Signature -> UntypedExpression -> TypedExpression ()

-- envFromDecls :: Ord f => [(f ::: SimpleType)] -> Environment f
-- envFromDecls l = M.fromList [(f,tp) | (f ::: tp) <- l]

-- signatureFromDecls :: Ord f => [(f ::: SimpleType)] -> Signature f
-- signatureFromDecls l = M.fromList [(f,tp) | (f ::: tp) <- l]

-- signatureToDecls :: Signature f -> [(f ::: SimpleType)]
-- signatureToDecls sig = [(f ::: tp) | (f, tp) <- M.toList sig]

----------------------------------------------------------------------
-- Type Substitution
----------------------------------------------------------------------

type Substitution = TypeVariable -> TyExp

class Substitutable a where
  substitute :: Substitution -> a -> a


instance Substitutable TyExp where
  substitute _ tp@TyBase{} = tp
  substitute s (TyVar v) = s v
  substitute s (tp1 :*: tp2) = substitute s tp1 :*: substitute s tp2
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

data UP f v = UP (UntypedEquation f v) (UntypedExpression f v) TyExp TyExp

instance Substitutable (UP f v) where
  substitute s (UP rl t tp1 tp2) = UP rl t (substitute s tp1) (substitute s tp2)

unify :: MonadError (TypingError f v) m => [UP f v] -> m Substitution
unify = go ident where
  go s [] = return s
  go s (UP rl a tp1 tp2:ups) = do 
    (s',ups') <- step rl a tp1 tp2
    go (s' `o` s) (ups' ++ (substitute s' `map` ups))

  step _  _ tp1 tp2 | tp1 == tp2 = return (ident, [])
  step _  _ (TyVar v) tp2 | v `notElem` fvs tp2 = return (singleton v tp2, [])
  step rl a t v@(TyVar _) = step rl a v t
  step _  _ (TyBase bt1) (TyBase bt2) | bt1 == bt2 = return (ident, [])
  step rl a (tp1 :-> tp1') (tp2 :-> tp2') = return (ident, [UP rl a tp1 tp2, UP rl a tp1' tp2'])
  step rl a (tp1 :*: tp1') (tp2 :*: tp2') = return (ident, [UP rl a tp1 tp2, UP rl a tp1' tp2'])
  step rl a tp1 tp2 = throwError (IncompatibleType rl a tp1 tp2)

----------------------------------------------------------------------
-- Inference
----------------------------------------------------------------------

data TypingError f v =
  IncompatibleType (UntypedEquation f v) (UntypedExpression f v) TyExp TyExp
  | LetPInLHS (UntypedEquation f v)
  | VariableUndefined (UntypedEquation f v) v
    
newtype InferM f v a =
  InferM (RWST () [UP f v] (Env f) (ExceptT (TypingError f v) UniqueM) a)
  deriving (  Applicative, Functor, Monad
            , MonadError (TypingError f v)
            , MonadState (Env f)
            , MonadWriter [UP f v]
            , MonadUnique)

runInfer :: InferM f v a -> Either (TypingError f v) (a, Env f, Substitution)
runInfer (InferM m) = do
  (a,sig, up) <- runUnique (runExceptT (runRWST m () M.empty))
  subst <- unify up
  return (a, substitute subst sig, subst)

freshTyExp :: InferM f v TyExp
freshTyExp = TyVar <$> unique

lookupFunTpe :: Ord f => f -> InferM f v TyExp
lookupFunTpe f = do
  env <- get
  case M.lookup f env of
    Nothing -> do
      tp <- freshTyExp
      put (M.insert f tp env)
      return tp
    Just tp -> return tp

require :: UntypedEquation f v -> UntypedExpression f v -> TyExp -> TyExp -> InferM f v ()
require rl a tp1 tp2 = tell [UP rl a tp1 tp2]

inferRule :: (Ord v, Ord f) => UntypedEquation f v -> InferM f v (Env v, UntypedEquation f v, TyExp)
inferRule rl = do
  (tp, env) <- flip runStateT M.empty $ inferL (lhs rl)
  _ <- flip runReaderT env $ checkR (rhs rl) tp
  return (env, rl, tp)
  where
    inferL (Var v _) = do
      env <- get
      case M.lookup v env of
        Nothing -> do
          tp <- lift freshTyExp
          put (M.insert v tp env)
          return tp
        Just tp -> return tp
    inferL (Fun f _ _) = lift (lookupFunTpe f)
    inferL (Pair t1 t2) = (:*:) <$> inferL t1 <*> inferL t2
    inferL (Apply t1 t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkL t1 (v1 :-> v2)
      checkL t2 v1
      return v2
    inferL (LetP {}) = throwError (LetPInLHS rl)      
    checkL t tp = do
      tp' <- inferL t
      lift (require rl t tp' tp)
      
    inferR (Var v _) = do
      env <- ask
      case M.lookup v env of
        Nothing -> throwError (VariableUndefined rl v)
        Just tp -> return tp
    inferR (Fun f _ _) = lift (lookupFunTpe f)
    inferR (Pair t1 t2) = 
      (:*:) <$> inferR t1 <*> inferR t2
    inferR (Apply t1 t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkR t1 (v1 :-> v2)
      checkR t2 v1
      return v2
    inferR (LetP t1 ((x,_),(y,_)) t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkR t1 (v1 :*: v2)
      local (M.insert x v1 . M.insert y v2) (inferR t2)
    checkR t tp = do
      tp' <- inferR t
      lift (require rl t tp' tp)

  -- ar _ eqns f | defined f =
  --   maximum $ 0 : [ length args
  --                 | eqn <- eqns
  --                 , let (Fun g _ _, args) = sexpr (lhs eqn)
  --                 , f == g ]
  -- ar sig _ c = tarity (sig M.! c)

inferSimpleType :: (Ord v, Ord f) => [UntypedEquation f v] -> Either (TypingError f v) (TypedProgram f v)
inferSimpleType eqns = toProg <$> runInfer (inferRule `mapM` eqns) where
  toProg (rs, sig, subst) = flip evalState (M.empty,0 :: Int) $ do
    gsig <- toGroundEnv sig
    teqns <- toEqn subst gsig `mapM` rs
    return TypedProgram { equations = teqns
                        , signature = gsig }
    
  toEqn subst gsig (env, rl, tp) = do
    genv <- toGroundEnv (substitute subst env)
    gtp <- toGroundTpe (substitute subst tp)
    return TypedEquation { eqEnv = genv
                         , eqEqn = Equation (withType genv gsig (lhs rl)) (withType genv gsig (rhs rl))
                         , eqTpe = gtp }

  withType env sig = mapExpression fun var where
    fun f _ _  = (f,sig M.! f)
    var v _  = (v,env M.! v)

  toGroundEnv env = traverse toGroundTpe env
  
  toGroundTpe :: TyExp -> State (M.Map TypeVariable Int, Int) SimpleType 
  toGroundTpe (TyVar v) = TyBase <$> btForVar v
  toGroundTpe (TyBase bt) = return (TyBase bt)
  toGroundTpe (tp1 :*: tp2) = (:*:) <$> toGroundTpe tp1 <*> toGroundTpe tp2
  toGroundTpe (tp1 :-> tp2) = (:->) <$> toGroundTpe tp1 <*> toGroundTpe tp2
  
  btForVar v = do
    (m,i) <- get
    case M.lookup v m of
      Nothing -> do {put (M.insert v (i+1) m, i+1); return (BT (i + 1));}
      Just j -> return (BT j)
      
-- pretty printing

instance PP.Pretty BaseType where
  pretty Clock = PP.text "Clock"
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
      pp _ (tp1 :*: tp2) = PP.tupled [pp id tp1, pp id tp2]
      pp paren (tp1 :-> tp2) = paren (pp PP.parens tp1 PP.<+> PP.text "->" PP.<+> pp id tp2)      

instance (PP.Pretty x) => PP.Pretty (M.Map x (ST g)) where
  pretty env = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "::" PP.<+> PP.pretty tp | (x,tp) <- M.toList env]

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
  pretty (IncompatibleType rl t has expected) =
          PP.text "Typing error in rule:"
          PP.<$> PP.indent 2 (PP.pretty rl)
          PP.<$> PP.text "The term" PP.<+> PP.pretty t
          PP.<+> PP.text "has type"
          PP.<+> PP.squotes (PP.pretty has)
          PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty expected) PP.<+> PP.text "is expected."
  pretty (LetPInLHS rl) =
    PP.text "LetP in lhs encountered:"
    PP.<$> PP.indent 2 (PP.pretty rl)    
  pretty (VariableUndefined rl v) =
    PP.text "Variable" PP.<+> PP.squotes (PP.pretty v) PP.<+> PP.text "undefined:"
    PP.<$> PP.indent 2 (PP.pretty rl)  
    
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypedEquation f v) where
  pretty TypedEquation{..} =
    PP.group (PP.pretty eqEnv)
    PP.<+> PP.text "⊦"
    PP.</> PP.group (prettyEquation PP.pretty PP.pretty eqEqn
                     PP.<+> PP.text ":"
                     PP.</> PP.pretty eqTpe)

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypedProgram f v) where
  pretty TypedProgram{..} =
    PP.vcat (PP.pretty `map` equations)
    PP.<$> PP.indent 2 (PP.text "where")
    PP.<$> PP.indent 4 (PP.pretty signature)
