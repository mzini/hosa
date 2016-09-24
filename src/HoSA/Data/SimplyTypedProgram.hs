module HoSA.Data.SimplyTypedProgram
  ( 
    TypeVariable
  , TypeName
  , SimpleType (..)
  , Environment
  , Signature
  , TypedExpression
  , TypedEquation (..)
  , TypedProgram (..)
  -- * constructors
  , pair
  , apply
  , letp
  , mapExpressionM
  , mapExpression
  , mapType
  -- * substitutions
  , substitute
  , singleton
  , ident
  , substFromList
  , o
  , antiUnifyType
  , unifyType
  , matchType
  -- * operations
  , fvs
  , equalModulo
  , compareModulo
  , typeOf
  , tarity
  , progUnion
  , inferSimpleType
  , variant
  , contraVariant
  , TypingError (..))
where

import           Data.Maybe (fromMaybe)
import           Data.List (partition)
import qualified Data.Map as M
import           Data.List (nub)
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.State
import           Control.Arrow ((***))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           HoSA.Data.Expression
import           HoSA.Utils
import Data.Functor.Identity (runIdentity)


----------------------------------------------------------------------
-- Type
----------------------------------------------------------------------

type TypeVariable = Unique
type TypeName = String

data SimpleType where
  TyVar  :: TypeVariable -> SimpleType
  TyCon  :: TypeName -> [SimpleType] -> SimpleType
  (:*:)  :: SimpleType -> SimpleType -> SimpleType
  (:->)  :: SimpleType -> SimpleType -> SimpleType
  deriving (Eq, Ord, Show)

infixr 5 :->
infixr 6 :*:

equalModulo :: SimpleType -> SimpleType -> Bool
tp1 `equalModulo` tp2 = tp1 `compare` tp2 == EQ

compareModulo :: SimpleType -> SimpleType -> Ordering
tp1 `compareModulo` tp2 = ren tp1 `compare` ren tp2
  where ren tp = rename (fvs tp) tp

fvsDL :: SimpleType -> [TypeVariable] -> [TypeVariable]
fvsDL (TyVar v)     = (:) v
fvsDL (TyCon _ as)  = \ vs -> foldl (flip fvsDL) vs as
fvsDL (tp1 :*: tp2) = fvsDL tp2 . fvsDL tp1
fvsDL (tp1 :-> tp2) = fvsDL tp2 . fvsDL tp1

fvs :: SimpleType -> [TypeVariable]
fvs = flip fvsDL []

pfvsDL :: SimpleType -> [TypeVariable] -> [TypeVariable]
pfvsDL (TyVar v)     = (:) v
pfvsDL (TyCon _ as)  = \ vs -> foldl (flip pfvsDL) vs as
pfvsDL (tp1 :*: tp2) = pfvsDL tp2 . pfvsDL tp1
pfvsDL (tp1 :-> tp2) = pfvsDL tp2 . nfvsDL tp1

nfvsDL :: SimpleType -> [TypeVariable] -> [TypeVariable]
nfvsDL (TyVar _)     = id
nfvsDL (TyCon _ as)  = \ vs -> foldl (flip nfvsDL) vs as
nfvsDL (tp1 :*: tp2) = nfvsDL tp2 . nfvsDL tp1
nfvsDL (tp1 :-> tp2) = nfvsDL tp2 . pfvsDL tp1

variance :: IsSymbol f => (SimpleType -> [TypeVariable] -> [TypeVariable]) -> Signature f -> TypeName -> [a] -> [a]
variance vsDL sig n tps = [ tp | (i,tp) <- zip [(0::Int)..] tps, i `elem` poss ] where
  poss = [ i
         | (f,decl) <- M.toList sig
         , isConstructor f
         , let (TyCon m tps') = returnType decl
         , n == m
         , let vs = zip [0..] [ v | TyVar v <- tps']
         , (i,v) <- vs
         , v `elem` foldl (flip vsDL) [] (argTypes decl) ] 

variant  :: IsSymbol f => Signature f -> TypeName -> [a] -> [a]
variant = variance pfvsDL

contraVariant :: IsSymbol f => Signature f -> TypeName -> [a] -> [a]
contraVariant = variance nfvsDL

returnType :: SimpleType -> SimpleType
returnType (_ :-> t) = returnType t
returnType t         = t

argTypes :: SimpleType -> [SimpleType]
argTypes (t1 :-> t2) = t1 : argTypes t2
argTypes _           = []

tarity :: SimpleType -> Int
tarity (_ :-> tp) = 1 + tarity tp
tarity _          = 0

----------------------------------------------------------------------
-- Simply Typed Expression
----------------------------------------------------------------------


typeOf :: TypedExpression f v -> SimpleType
typeOf (Var _ tp)           = tp
typeOf (Fun _ tp _)         = tp
typeOf (Pair (tp1,tp2) _ _) = tp1 :*: tp2
typeOf (Apply tp _ _)       = tp
typeOf (LetP tp _ _ _)      = tp

pair :: TypedExpression f v -> TypedExpression f v -> TypedExpression f v
pair a b = Pair (typeOf a, typeOf b) a b

apply :: Eq v => TypedExpression f v -> TypedExpression f v -> TypedExpression f v
apply f a =
  case typeOf f of
    (t1 :-> t2) -> Apply (substitute subst t2) (substitute subst f) (substitute subst a)
      where subst = either err id (unifyType [(t1,typeOf a)]) where
              err _ = error $ renderPretty (typeOf a) ++ " does not unify with " ++ renderPretty t1
    _ -> error $ "SimplyTypedProgram.apply: application to non-functional type: "
                 ++ renderPretty (typeOf f)
            

letp :: Eq v => TypedExpression f v -> (v,v) -> TypedExpression f v -> TypedExpression f v
letp t1 (x,y) t2 =
  case typeOf t1 of
    (tpx :*: tpy) -> LetP (typeOf t2') t1 ((x,tpx),(y,tpy)) t2'
      where
        t2' = mapExpression fun var t2
        fun f tp _ = (f,tp)
        var v tp | v == x    = (x,tpx)
                 | v == y    = (y,tpy)
                 | otherwise = (v,tp)
    _ -> error $ "SimplyTypedProgram.letp: let-bound expression of non-pair type: "
                 ++ renderPretty (typeOf t1)


mapType :: Eq v => (tp -> SimpleType) -> Expression f v tp -> Expression f v SimpleType
mapType f = mapExpression (\ g tp _ -> (g,f tp)) (\ v tp -> (v,f tp))

mapExpression :: Eq v' =>
  (f -> tp -> Location -> (f',SimpleType))
  -> (v -> tp -> (v',SimpleType))
  -> Expression f v tp
  -> TypedExpression f' v'
mapExpression f g = runIdentity . mapExpressionM f' g' where
  f' s tp l = pure (f s tp l)
  g' v tp   = pure (g v tp)

mapExpressionM :: (Eq v', Applicative m) =>
  (f -> tp -> Location -> m (f',SimpleType))
  -> (v -> tp -> m (v',SimpleType))
  -> Expression f v tp
  -> m (TypedExpression f' v')
mapExpressionM _ g (Var v tp)           = uncurry Var <$> g v tp
mapExpressionM f _ (Fun s tp l)         = uncurry Fun <$> f s tp l <*> pure l
mapExpressionM f g (Pair _ t1 t2)       = pair <$> mapExpressionM f g t1 <*> mapExpressionM f g t2
mapExpressionM f g (Apply _ t1 t2)      = apply <$> mapExpressionM f g t1 <*> mapExpressionM f g t2
mapExpressionM f g (LetP _ t1 (x,y) t2) =
  letp <$> mapExpressionM f g t1 <*> ((,) <$> g' x <*> g' y) <*> mapExpressionM f g t2
  where
    g' (v,tp) = fst <$> g v tp 


----------------------------------------------------------------------
-- Simply Typed Programs
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
                  

----------------------------------------------------------------------
-- Type Substitution
----------------------------------------------------------------------

type Substitution = TypeVariable -> SimpleType

class Substitutable a where
  substitute :: Substitution -> a -> a


instance Substitutable SimpleType where
  substitute s (TyVar v)     = s v
  substitute s (TyCon n tps) = TyCon n (substitute s `map` tps)
  substitute s (tp1 :*: tp2) = substitute s tp1 :*: substitute s tp2
  substitute s (tp1 :-> tp2) = substitute s tp1 :-> substitute s tp2
  
instance Substitutable (Environment x) where
  substitute s env = M.map (substitute s) env

instance (Substitutable a, Substitutable b) => Substitutable (a,b) where
  substitute s = substitute s *** substitute s

instance (Substitutable Substitution) where
  substitute s1 s2 = substitute s1 . s2

instance Eq v => Substitutable (TypedExpression f v) where
  substitute s = mapType (substitute s)

instance Eq v => Substitutable (Equation f v SimpleType) where
  substitute s (Equation lhs rhs) = Equation  (substitute s lhs) (substitute s rhs)

instance Eq v => Substitutable (TypedEquation f v) where
  substitute s (TypedEquation env eq tpe) = TypedEquation (substitute s env) (substitute s eq) (substitute s tpe)
  
o :: Substitution -> Substitution -> Substitution
o = substitute

ident :: Substitution
ident = TyVar

singleton :: TypeVariable -> SimpleType -> Substitution
singleton v tp = \ w -> if v == w then tp else TyVar w

substFromList :: [(TypeVariable,SimpleType)] -> Substitution
substFromList m v = fromMaybe (TyVar v) (lookup v m)

rename :: Substitutable tp => [TypeVariable] -> tp -> tp
rename vs = substitute ren where
  ren = substFromList (runUnique (sequence [ (v,) <$> freshTyExp | v <- nub vs]))


unifyType :: [(SimpleType,SimpleType)] -> Either (SimpleType,SimpleType) Substitution
unifyType = go ident where
  go s [] = return s
  go s ((tp1,tp2):ups) = do 
    (s',ups') <- step tp1 tp2
    go (s' `o` s) (ups' ++ (substitute s' `map` ups))

  step tp1            tp2           | tp1 == tp2           = return (ident, [])
  step (TyVar v)      tp2           | v `notElem` fvs tp2  = return (singleton v tp2, [])
  step t              v@(TyVar _)                          = step v t
  step (tp1 :-> tp1') (tp2 :-> tp2')                       = return (ident, [(tp1,tp2), (tp1',tp2')])
  step (tp1 :*: tp1') (tp2 :*: tp2')                       = return (ident, [(tp1,tp2), (tp1',tp2')])
  step (TyCon n tps1) (TyCon m tps2) | n == m              = return (ident, zip tps1 tps2) 
  step tp1            tp2                                  = throwError (tp1,tp2)

antiUnifyType :: SimpleType -> SimpleType -> SimpleType
antiUnifyType a b = evalState (runUniqueT (step a b)) M.empty where
  step tpa tpb
    | tpa == tpb = return tpa
  step (TyCon n tpsa) (TyCon m tpsb)
    | n == m = TyCon n <$> zipWithM step tpsa tpsb
  step (tpa1 :-> tpa2) (tpb1 :-> tpb2) = do
    (:->) <$> step tpa1 tpb1 <*> step tpa2 tpb2
  step (tpa1 :*: tpa2) (tpb1 :*: tpb2) = do
    (:*:) <$> step tpa1 tpb1 <*> step tpa2 tpb2
  step tpa tpb = do
    m <- lift get
    case M.lookup (tpa,tpb) m of
      Nothing -> do
        v <- unique
        lift (put (M.insert (tpa,tpb) v m))
        return (TyVar v)
      Just v -> return (TyVar v)

matchType :: SimpleType -> SimpleType -> Maybe Substitution
matchType a b = walk a b ident
  where 
    walk (TyVar v)      tp               subst
      | img == TyVar v = return (\ v' -> if v' == v then tp else subst v')
      | img == tp      = Just subst
      | otherwise      = Nothing
      where img = subst v
    walk (TyCon n tpsa) (TyCon m tpsb)   subst
      | n == m    = composeM (zipWith walk tpsa tpsb) subst
    walk (tpa1 :*: tpa2) (tpb1 :*: tpb2) subst = do
      walk tpa1 tpb1 subst >>= walk tpa2 tpb2
    walk (tpa1 :-> tpa2) (tpb1 :-> tpb2) subst = do
      walk tpa1 tpb1 subst >>= walk tpa2 tpb2
    walk _               _               _     = Nothing
----------------------------------------------------------------------
-- Inference
----------------------------------------------------------------------

data TypingError f v =
  IncompatibleType (UntypedEquation f v) (UntypedExpression f v) SimpleType SimpleType
  | LetPInLHS (UntypedEquation f v)
  | IllformedConstructorType f SimpleType
  | VariableUndefined (UntypedEquation f v) v
    
newtype InferM f v a =
  InferM (StateT (Environment f) (ExceptT (TypingError f v) UniqueM) a)
  deriving (  Applicative, Functor, Monad
            , MonadError (TypingError f v)
            , MonadState (Environment f)
            , MonadUnique)

runInfer :: IsSymbol f => Environment f -> InferM f v a -> Either (TypingError f v) (a, Environment f)
runInfer sig (InferM m) = runUniqueWithout vs (runExceptT (runStateT m sig))
  where
    vs = foldl (flip fvsDL) [] (M.elems sig)

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

lookupFunTpe :: Ord f => f -> InferM f v SimpleType
lookupFunTpe f = do
  env <- get
  let create = do
        tp <- freshTyExp
        put (M.insert f tp env)
        return tp
  maybe create return (M.lookup f env)
        
  
unifyM :: UntypedEquation f v -> UntypedExpression f v -> SimpleType -> SimpleType -> InferM f v Substitution
unifyM rl a tp1 tp2 = 
  case unifyType [(tp1,tp2)] of
    Left (tp1',tp2') -> throwError (IncompatibleType rl a tp1' tp2')
    Right s -> modify (substitute s) >> return s

-- TODO 
inferEquation :: (Ord v, Ord f, IsSymbol f) => UntypedEquation f v -> InferM f v (TypedEquation f v, Substitution)
inferEquation rl = do
  (lhs', env1, subst1) <- infer M.empty (lhs rl)
  (rhs', env2, subst2) <- check env1 (rhs rl) (typeOf lhs')
  return (TypedEquation env2 (Equation (substitute subst2 lhs') rhs') (typeOf rhs')
         , subst2 `o` subst1)
  where

    headSym = fst (definedSymbol rl)
    
    fromEnv env v = 
      case M.lookup v env of
        Nothing -> do
          tp <- freshTyExp
          return (M.insert v tp env, tp)
        Just tp -> return (env, tp)

    instantiate tp = do
      s <- substFromList <$> sequence [ (v,) <$> freshTyExp | v <- fvs tp ]
      return (substitute s tp)

    check env t tp = do
      (t',env',subst') <- infer env t
      substr <- unifyM rl t (typeOf t') (substitute subst' tp)
      return (substitute substr t', substitute substr env', substr `o` subst')


    infer env (Var v _) = do
      (env1,tp) <- fromEnv env v
      return (Var v tp, env1, ident)
    infer env (Fun f _ l) = do
      tp <- lookupFunTpe f >>= (if f == headSym then return else instantiate)
      return (Fun f tp l, env, ident)
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
          adj v s e = case M.lookup v env1 of
                        Nothing -> M.delete v e
                        Just tp -> M.insert v (substitute s tp) e
          env1' = M.insert x tpx (M.insert y tpy env1)
      (t2, env2, subst2) <- infer env1' s2
      return (letp (substitute subst2 t1) (x, y) t2
             , adj x subst2 (adj y subst2 env2)
             , subst2 `o` subst1)

inferSimpleType :: (Ord v, Ord f, IsSymbol f) => Environment f -> [UntypedEquation f v] -> Either (TypingError f v) (TypedProgram f v)
inferSimpleType initialEnv eqns = uncurry TypedProgram <$> runInfer initialEnv (walk [] eqns) where
  walk teqs [] = return teqs
  walk teqs (eq:eqs) = do
    (teq,subst) <- inferEquation eq
    walk (teq : substitute subst `map` teqs) eqs

  -- typedProgram (eqs,sig) = TypedProgram { equations = [ rename vs eq
  --                                                     | eq <- eqs
  --                                                     , let vs = fvs (eqTpe eq) ++ concatMap fvs (M.elems (eqEnv eq)) ] 
  --                                       , signature = M.map (\ tp -> rename (fvs tp) tp) sig }
    -- vs = foldl (flip fvsDL) [] (M.elems sig)
    -- renameType tp = substitute (fromList ren) tp where
    --   ren = runUnique (sequence [ (v,) <$> freshTyExp | v <- nub (fvs tp)])
  

-- pretty printing

-- instance PP.Pretty BaseType where
--   pretty Clock = PP.text "Clock"
--   pretty (BT i) = PP.text (names !! i) where
    -- names = [ [c] | c <- ['A'..'Z'] ] ++ [ 'B' : show j | j <- [(1 :: Int)..] ]

instance PP.Pretty TypeVariable where
  pretty i = PP.text (names !! (uniqueToInt i - 1)) where
    names = [ [c] | c <- take 5 ['α'..] ++ ['a'..'z'] ] ++ [ 'a' : show j | j <- [(1 :: Int)..] ]

instance PP.Pretty SimpleType where
  pretty = pp id
    where
      pp _     (TyVar v)     = PP.pretty v
      pp _     (tp1 :*: tp2) = PP.tupled [pp id tp1, pp id tp2]
      pp _     (TyCon n [])  = PP.text n
      pp _     (TyCon n tps) = PP.text n PP.<> PP.tupled [pp id tp | tp <- tps ]
      pp paren (tp1 :-> tp2) = paren (pp PP.parens tp1 PP.<+> PP.text "->" PP.<+> pp id tp2)      

instance (PP.Pretty x) => PP.Pretty (M.Map x SimpleType) where
  pretty env = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "::" PP.<+> PP.pretty tp | (x,tp) <- M.toList env]

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
  pretty (IncompatibleType rl t has expected) =
          PP.text "Typing error in rule:"
          PP.<$> PP.indent 2 (PP.pretty rl)
          PP.<$> PP.text "The term" PP.<+> PP.pretty t
          PP.<+> PP.text "has type"
          PP.<+> PP.squotes (PP.pretty has)
          PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty expected) PP.<+> PP.text "is expected."
  pretty (IllformedConstructorType c tp) =
    PP.text "Illformed Constructor type for constructor" PP.<+> PP.squotes (PP.pretty c)
    PP.<$> PP.indent 2 (PP.pretty tp)      
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

instance (IsSymbol f, Eq f, PP.Pretty f, PP.Pretty v) => PP.Pretty (TypedProgram f v) where
  pretty TypedProgram{..} =
    PP.vcat [ ppDecl d tp
              PP.<$> PP.vcat (PP.pretty `map` eqs)
              PP.<$> PP.empty
            | (d,tp) <- ds
            , let eqs = [eq | eq <- eqEqn `map` equations, fst (definedSymbol eq) == d]
            , not (null eqs)]
    PP.<$> PP.text "where"
    PP.<$> PP.indent 2 (PP.vcat [ppDecl c tp | (c,tp) <- cs])
    where
      ppDecl f tp = PP.pretty f PP.<+> PP.text "::" PP.<+> PP.pretty (rename (fvs tp) tp)
      (ds,cs) = partition (isDefined . fst) (M.toList signature)
    -- PP.vcat [ PP.pretty eq | eq <- equations]
    -- PP.<$> PP.text "where"
    -- PP.<$> PP.indent 2 (PP.vcat [ppDecl c tp | (c,tp) <- M.toList signature])
    -- where
    --   ppDecl f tp = PP.pretty f PP.<+> PP.text "::" PP.<+> PP.pretty tp
