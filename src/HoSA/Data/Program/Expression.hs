module HoSA.Data.Program.Expression (
  -- * Constructors
  pair
  , apply
  , letp
  , sexpr
  , emptyLoc
  -- * Symbols
  , funs
  , fvars
  , tfuns
  , tfvars
  , tfunsDL
  , tfvarsDL
  -- * Operations
  , typeOf
  , headSymbol
  , mapType
  , mapExpression
  , mapExpressionM
  ) where

import Control.Monad.Identity (runIdentity)
import HoSA.Data.Program.Types
import HoSA.Data.MLTypes
import HoSA.Utils (uniqueFromInt)

----------------------------------------------------------------------
-- constructors
----------------------------------------------------------------------

pair :: TypedExpression f v -> TypedExpression f v -> TypedExpression f v
pair a b = Pair (typeOf a, typeOf b) a b

apply :: Eq v => TypedExpression f v -> TypedExpression f v -> TypedExpression f v
apply f a =
  case typeOf f of
    (t1 :-> t2) -> Apply (substitute subst t2) (substitute subst f) (substitute subst a)
      where Right subst = unifyType [(t1,typeOf a)] where
    _ -> error "application to non-functional expression"

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
    _ -> error "pair-let binding to non-pair expression"

emptyLoc :: Location
emptyLoc = uniqueFromInt 0

----------------------------------------------------------------------
-- symbols
----------------------------------------------------------------------

tfunsDL :: Expression f v tp -> [(f,tp,Location)] -> [(f,tp,Location)]
tfunsDL (Var _ _)        = id
tfunsDL (Fun f tp l)     = (:) (f,tp,l)
tfunsDL (Pair _ t1 t2)   = tfunsDL t2 . tfunsDL t1
tfunsDL (Apply _ t1 t2)  = tfunsDL t2 . tfunsDL t1
tfunsDL (LetP _ t1 _ t2) = tfunsDL t2 . tfunsDL t1

tfvarsDL :: Eq v => Expression f v tp -> [(v,tp)] -> [(v,tp)]
tfvarsDL (Var v tp)                   = (:) (v,tp)
tfvarsDL (Fun _ _ _)                  = id
tfvarsDL (Pair _ t1 t2)               = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (Apply _ t1 t2)              = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (LetP _ t1 ((x,_),(y,_)) t2) =
  (++) (filter (\ (z,_) -> z == x || z == y) (tfvarsDL t2 [])) . tfvarsDL t1

tfuns :: Expression f v tp -> [(f,tp,Location)]
tfuns = flip tfunsDL []

tfvars :: Eq v => Expression f v tp -> [(v,tp)]
tfvars = flip tfvarsDL []

funs :: Expression f v tp -> [f]
funs e = [ f | (f,_,_) <- tfunsDL e []]

fvars :: Eq v => Expression f v tp -> [v]
fvars = map fst . flip tfvarsDL []


sexpr :: Expression f v tp -> (Expression f v tp, [Expression f v tp])
sexpr (Apply _ t1 t2) = (h, rest ++ [t2]) where (h,rest) = sexpr t1
sexpr t = (t,[])

-- fromSexpr :: UntypedExpression f v -> [UntypedExpression f v] -> UntypedExpression f v
-- fromSexpr = foldl (Apply ())

headSymbol :: Expression f v tp -> Maybe (f,tp)
headSymbol (Fun f tp _)   = Just (f,tp)
headSymbol (Apply _ t1 _) = headSymbol t1
headSymbol _              = Nothing

----------------------------------------------------------------------
-- ops
----------------------------------------------------------------------

typeOf :: TypedExpression f v -> SimpleType
typeOf (Var _ tp)           = tp
typeOf (Fun _ tp _)         = tp
typeOf (Pair (tp1,tp2) _ _) = tp1 :*: tp2
typeOf (Apply tp _ _)       = tp
typeOf (LetP tp _ _ _)      = tp

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
-- substitutions
----------------------------------------------------------------------

instance Eq v => TSubstitutable (TypedExpression f v) where
  substitute s = mapType (substitute s)
