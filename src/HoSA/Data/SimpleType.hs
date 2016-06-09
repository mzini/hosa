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

import           Data.Maybe (fromJust)
import qualified Data.Map as M
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Arrow ((***), second)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
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

type STTerm = Term (Symbol ::: SimpleType) (Variable ::: SimpleType)

data STRule = STRule { strlEnv         :: M.Map Variable SimpleType
                     , strlUntypedRule :: Rule Symbol Variable
                     , strlTypedRule   :: Rule (Symbol ::: SimpleType) (Variable ::: SimpleType)
                     , strlType        :: SimpleType }
                  
data STAtrs = STAtrs { statrsRules :: [STRule]
                     , statrsSignature :: M.Map Symbol SimpleType} 


typeOf :: STTerm -> SimpleType
typeOf (Var (_ ::: tp)) = tp
typeOf (Fun (_ ::: tp)) = tp
typeOf (Pair t1 t2) = TyPair (typeOf t1) (typeOf t2)
typeOf (Apply t1 t2) =
  case typeOf t1 of
    _ :-> tp -> tp
    _ -> error "SimpleType.typeOf: ill-typed applicant"
typeOf (Let _ _ t2) = typeOf t2    

withType :: M.Map Variable SimpleType -> M.Map Symbol SimpleType -> Term Symbol Variable -> STTerm
withType env sig = tmap (\ f -> f ::: sig M.! f) (\ v -> v ::: env M.! v)
--   (Var v) = Var (v ::: env M.! v)
-- withType _   sig (Fun f) = Fun (f ::: sig M.! f)
-- withType env sig (Pair t1 t2) = Pair (withType env sig t1) (withType env sig t2)
-- withType env sig (Apply t1 t2) = Apply (withType env sig t1) (withType env sig t2)


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

data UP = UP (Rule Symbol Variable) (Term Symbol Variable) TyExp TyExp

instance Substitutable UP where
  substitute s (UP rl t tp1 tp2) = UP rl t (substitute s tp1) (substitute s tp2)

unify :: MonadError TypingError m => [UP] -> m Substitution
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
  step rl a (TyPair tp1 tp1') (TyPair tp2 tp2') = return (ident, [UP rl a tp1 tp2, UP rl a tp1' tp2'])
  step rl a tp1 tp2 = throwError (IncompatibleType rl a tp1 tp2)

----------------------------------------------------------------------
-- Inference
----------------------------------------------------------------------

data TypingError =
  IncompatibleType (Rule Symbol Variable) (Term Symbol Variable) TyExp TyExp
  | LetInLHS (Rule Symbol Variable)
  | VariableUndefined (Rule Symbol Variable) Variable
    
newtype InferM a =
  InferM (RWST () [UP] (Env Symbol) (ExceptT TypingError UniqueM) a)
  deriving (  Applicative, Functor, Monad
            , MonadError TypingError
            -- , MonadReader (Env Variable)
            , MonadState (Env Symbol)
            , MonadWriter [UP]
            , MonadUnique)

runInfer :: InferM a -> Either TypingError (a, Env Symbol, Substitution)
runInfer (InferM m) = do
  (a,sig, up) <- runUnique (runExceptT (runRWST m () M.empty))
  subst <- unify up
  return (a, substitute subst sig, subst)

freshTyExp :: InferM TyExp
freshTyExp = TyVar <$> unique

lookupFunTpe :: Symbol -> InferM TyExp
lookupFunTpe f = do
  env <- get
  case M.lookup f env of
    Nothing -> do
      tp <- freshTyExp
      put (M.insert f tp env)
      return tp
    Just tp -> return tp

-- lookupVarTpe :: Variable -> InferM TyExp
-- lookupVarTpe v = do
--   (env, Just ctx)  <- get
--   case M.lookup v ctx of
--     Nothing -> do
--       tp <- freshTyExp
--       put (env, Just (M.insert v tp ctx))
--       return tp
--     Just tp -> return tp

require :: Rule Symbol Variable -> Term  Symbol Variable -> TyExp -> TyExp -> InferM ()
require rl a tp1 tp2 = tell [UP rl a tp1 tp2]

inferRule :: Rule Symbol Variable -> InferM (Env Variable, Rule Symbol Variable, TyExp)
inferRule rl = do
  (tp, env) <- flip runStateT M.empty $ inferL (lhs rl)
  _ <- flip runReaderT env $ checkR (rhs rl) tp
  return (env, rl, tp)
  where
    inferL (Var v) = do
      env <- get
      case M.lookup v env of
        Nothing -> do
          tp <- lift freshTyExp
          put (M.insert v tp env)
          return tp
        Just tp -> return tp
    inferL (Fun f) = lift (lookupFunTpe f)
    inferL (Pair t1 t2) = TyPair <$> inferL t1 <*> inferL t2
    inferL (Apply t1 t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkL t1 (v1 :-> v2)
      checkL t2 v1
      return v2
    inferL (Let {}) = throwError (LetInLHS rl)      
    checkL t tp = do
      tp' <- inferL t
      lift (require rl t tp' tp)
      
    inferR (Var v) = do
      env <- ask
      case M.lookup v env of
        Nothing -> throwError (VariableUndefined rl v)
        Just tp -> return tp
    inferR (Fun f) = lift (lookupFunTpe f)
    inferR (Pair t1 t2) = 
      TyPair <$> inferR t1 <*> inferR t2
    inferR (Apply t1 t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkR t1 (v1 :-> v2)
      checkR t2 v1
      return v2
    inferR (Let t1 (x,y) t2) = do
      v1 <- lift freshTyExp
      v2 <- lift freshTyExp
      checkR t1 (TyPair v1 v2)
      local (M.insert x v1 . M.insert y v2) (inferR t2)
    checkR t tp = do
      tp' <- inferR t
      lift (require rl t tp' tp)

inferSimpleType :: ATRS Symbol Variable -> Either TypingError STAtrs
inferSimpleType atrs = toSTAtrs <$> runInfer (mapM inferRule (rules atrs)) where
  toSTAtrs (rs, sig, subst) = flip evalState (M.empty,0 :: Int) $ do
    gsig <- toGroundEnv sig
    strs <- toGroundSTRule subst gsig `mapM` rs
    return STAtrs { statrsRules = strs, statrsSignature = gsig }
    
  toGroundSTRule subst gsig (env, rl, tp) = do
    genv <- toGroundEnv (substitute subst env)
    gtp <- toGroundTpe (substitute subst tp)
    return STRule { strlEnv = genv
                  , strlUntypedRule = rl
                  , strlTypedRule = Rule (withType genv gsig (lhs rl)) (withType genv gsig (rhs rl))
                  , strlType = gtp }

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

instance PP.Pretty TypingError where
  pretty (IncompatibleType rl t has expected) =
          PP.text "Typing error in rule:"
          PP.<$> PP.indent 2 (PP.pretty rl)
          PP.<$> PP.text "The term" PP.<+> PP.pretty t
          PP.<+> PP.text "has type"
          PP.<+> PP.squotes (PP.pretty has)
          PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty expected) PP.<+> PP.text "is expected."
  pretty (LetInLHS rl) =
    PP.text "Let in lhs encountered:"
    PP.<$> PP.indent 2 (PP.pretty rl)    
  pretty (VariableUndefined rl v) =
    PP.text "Variable" PP.<+> PP.squotes (PP.pretty v) PP.<+> PP.text "undefined:"
    PP.<$> PP.indent 2 (PP.pretty rl)  
    
