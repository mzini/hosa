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
import           Control.Monad.State
import           Control.Monad.Writer
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

data UP = UP Rule Term TyExp TyExp

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

data TypingError = IncompatibleType Rule Term TyExp TyExp
    
newtype InferM a =
  InferM (WriterT [UP] (StateT (Env FunId, Maybe (Env Variable)) (ExceptT TypingError UniqueM)) a)
  deriving (Applicative, Functor, Monad
            , MonadError TypingError
            , MonadState (Env FunId, Maybe (Env Variable))
            , MonadWriter [UP]
            , MonadUnique)

runInfer :: InferM a -> Either TypingError (a, Env FunId, Substitution)
runInfer (InferM m) = do
  ((a,up), (sig,_)) <- run m
  subst <- unify up
  return (a, substitute subst sig, subst)
  where
    run = runUnique . runExceptT . flip runStateT (M.empty, Nothing) . runWriterT

freshTyExp :: InferM TyExp
freshTyExp = TyVar <$> unique

lookupFunTpe :: FunId -> InferM TyExp
lookupFunTpe f = do
  (env, ctx)  <- get
  case M.lookup f env of
    Nothing -> do
      tp <- freshTyExp
      put (M.insert f tp env, ctx)
      return tp
    Just tp -> return tp

lookupVarTpe :: Variable -> InferM TyExp
lookupVarTpe v = do
  (env, Just ctx)  <- get
  case M.lookup v ctx of
    Nothing -> do
      tp <- freshTyExp
      put (env, Just (M.insert v tp ctx))
      return tp
    Just tp -> return tp

require :: Rule -> Term -> TyExp -> TyExp -> InferM ()
require rl a tp1 tp2 = tell [UP rl a tp1 tp2]

withContext :: InferM a -> InferM a
withContext m = modify init *> m <* modify reset
  where
    init (env,_) = (env, Just M.empty)
    reset (env,_) = (env, Nothing)    

getContext :: InferM (Env Variable)
getContext = fromJust <$> snd <$> get
                       
inferRule :: Rule -> InferM (Env Variable, Rule, TyExp)
inferRule rl = withContext $ do
  tp <- infer (lhs rl)
  check (rhs rl) tp
  (,rl, tp) <$> getContext
  where 
    infer (view -> Var v) = lookupVarTpe v
    infer (view -> Const f) = lookupFunTpe f
    infer (view -> Pair t1 t2) = 
      TyPair <$> infer t1 <*> infer t2
    infer (view -> Appl t1 t2) = do
      v1 <- freshTyExp
      v2 <- freshTyExp
      check t1 (v1 :-> v2)
      check t2 v1
      return v2
    infer _ = error "explode"
    check t tp = do
      tp' <- infer t
      require rl t tp' tp

inferSimpleType :: [Rule] -> Either TypingError STAtrs
inferSimpleType rs = toSTAtrs <$> runInfer (mapM inferRule rs) where
  toSTAtrs (rs', sig, subst) = flip evalState (M.empty,0 :: Int) $ do
    gsig <- toGroundEnv sig
    strs <- toGroundSTRule subst gsig `mapM` rs'
    return STAtrs { rules = strs, signature = gsig }
    
  toGroundSTRule subst gsig (env, rl, tp) = do
    genv <- toGroundEnv (substitute subst env)
    gtp <- toGroundTpe (substitute subst tp)
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

instance PP.Pretty TypingError where
  pretty (IncompatibleType rl t has expected) =
          PP.text "Typing error in rule:"
          PP.<$> PP.indent 2 (PP.pretty rl)
          PP.<$> PP.text "The term" PP.<+> PP.pretty t
          PP.<+> PP.text "has type"
          PP.<+> PP.squotes (PP.pretty has)
          PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty expected) PP.<+> PP.text "is expected."
    

