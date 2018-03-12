module HoSA.Data.Program.Expression (
  -- * Constructors
  pair
  , apply
  , letp
  , ite
  , sexpr
  , choice
  , caseE
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

import Data.Foldable

----------------------------------------------------------------------
-- constructors
----------------------------------------------------------------------

pair :: TypedExpression f v -> TypedExpression f v -> TypedExpression f v
pair a b = Pair (typeOf a, typeOf b) a b

apply :: Eq v => TypedExpression f v -> TypedExpression f v -> TypedExpression f v
apply f a =
  case typeOf f of
    (t1 :-> t2) -> Apply (substitute subst t2) (substitute subst f) (substitute subst a) where
      Right subst = unifyType [(t1,typeOf a)]
    _ -> error "application to non-functional expression"

ite :: Eq v => TypedExpression f v -> TypedExpression f v -> TypedExpression f v -> TypedExpression f v
ite g t e = If (substitute subst (typeOf t)) (substitute subst g) (substitute subst t) (substitute subst e) where
  Right subst = unifyType [(typeOf g, tyBool), (typeOf t, typeOf e)]

choice :: Eq v => Distribution (TypedExpression f v) -> TypedExpression f v
choice d = Choice (substitute subst (head tps)) (substitute subst `fmap` d) where
  Right subst = unifyTypes tps
  tps = typeOf `map` toList d

caseE :: Eq v => TypedExpression f v -> [(TypedExpression f v,TypedExpression f v)] -> TypedExpression f v
caseE g cs = Case (substitute subst (head tps)) (substitute subst g) [(substitute subst p,substitute subst e) | (p,e) <- cs] where
  Right subst = unifyTypes tps
  tps = [typeOf e | (_,e) <- cs]

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
tfunsDL Var{}            = id
tfunsDL (Fun f tp l)     = (:) (f,tp,l)
tfunsDL (Pair _ t1 t2)   = tfunsDL t2 . tfunsDL t1
tfunsDL (Apply _ t1 t2)  = tfunsDL t2 . tfunsDL t1
tfunsDL (LetP _ t1 _ t2) = tfunsDL t2 . tfunsDL t1
tfunsDL (Case _ g cs)    = foldr (.) (tfunsDL g) [tfunsDL p . tfunsDL e | (p,e) <- cs]
tfunsDL (Choice _ ds)    = foldr ((.) . tfunsDL) id (toList ds)
tfunsDL (If _ g t e)     = tfunsDL g . tfunsDL t . tfunsDL e

tfvarsDL :: Eq v => Expression f v tp -> [(v,tp)] -> [(v,tp)]
tfvarsDL (Var v tp)                   = (:) (v,tp)
tfvarsDL Fun{}                        = id
tfvarsDL (Pair _ t1 t2)               = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (Apply _ t1 t2)              = tfvarsDL t2 . tfvarsDL t1
tfvarsDL (If _ g t e)                 = tfvarsDL g . tfvarsDL t . tfvarsDL e
tfvarsDL (Case _ g cs)                = foldr ((.) . f) (tfvarsDL g) cs where
  f (p,e) = (++) (filter (\ (z,_) -> z `elem` fvars p) (tfvarsDL e []))
tfvarsDL (Choice _ ds)                = foldr ((.) . tfvarsDL) id (toList ds)
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
typeOf (Case tp _ _)        = tp
typeOf (Choice tp _)        = tp
typeOf (If  tp _ _ _)       = tp

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
mapExpressionM f g (If _ tg tt te)      = ite <$> mapExpressionM f g tg <*> mapExpressionM f g tt <*> mapExpressionM f g te
mapExpressionM f g (Case _ tg cs)       =
  caseE <$> mapExpressionM f g tg <*> sequenceA [ (,) <$> mapExpressionM f g p <*> mapExpressionM f g e | (p,e) <- cs]
mapExpressionM f g (Choice _ d)         = choice <$> sequenceA (mapExpressionM f g `fmap` d)
mapExpressionM f g (LetP _ t1 (x,y) t2) =
  letp <$> mapExpressionM f g t1 <*> ((,) <$> g' x <*> g' y) <*> mapExpressionM f g t2
  where
    g' (v,tp) = fst <$> g v tp 

----------------------------------------------------------------------
-- substitutions
----------------------------------------------------------------------

instance Eq v => TSubstitutable (TypedExpression f v) where
  substitute s = mapType (substitute s)
