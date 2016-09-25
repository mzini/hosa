module HoSA.Data.MLTypes
  (
    -- * Datatypes
    TypeVariable
  , TypeName
  , SimpleType (..)
  , TypeSubstitution
  , Environment
  , Signature
    -- * Alpha conversion etc.
  , equalModulo
  , compareModulo
  , rename
    -- * Variables
  , fvs
  , fvsDL
  , pfvsDL
  , nfvsDL
    -- * Operations
  , variant
  , contraVariant
  , returnType
  , argTypes
  , tarity
    -- * Type Substitutions
  , identSubst
  , singletonSubst
  , substFromList
  , o
  , TSubstitutable (..)
    -- * Unification and Matching
  , unifyType
  , antiUnifyType
  , matchType
    -- * Unification and Matching
  ) where
  
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.List (nub)
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Arrow ((***))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           HoSA.Utils

----------------------------------------------------------------------
-- data types 
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

type Environment v = Map.Map v SimpleType
type Signature f = Map.Map f SimpleType
type TypeSubstitution = TypeVariable -> SimpleType


----------------------------------------------------------------------
-- alpha conversion etc.
----------------------------------------------------------------------

equalModulo :: SimpleType -> SimpleType -> Bool
tp1 `equalModulo` tp2 = tp1 `compare` tp2 == EQ

compareModulo :: SimpleType -> SimpleType -> Ordering
tp1 `compareModulo` tp2 = ren tp1 `compare` ren tp2
  where ren tp = rename (fvs tp) tp

rename :: TSubstitutable tp => [TypeVariable] -> tp -> tp
rename vs = substitute ren where
  ren = substFromList (runUnique (sequence [ unique >>= \ u -> return (v,TyVar u) | v <- nub vs]))

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

variance :: (SimpleType -> [TypeVariable] -> [TypeVariable]) -> Signature f -> TypeName -> [a] -> [a]
variance vsDL sig n tps = [ tp | (i,tp) <- zip [(0::Int)..] tps, i `elem` poss ] where
  poss = [ i
         | decl <- Map.elems sig
         , let (TyCon m tps') = returnType decl
         , n == m
         , let vs = zip [0..] [ v | TyVar v <- tps']
         , (i,v) <- vs
         , v `elem` foldl (flip vsDL) [] (argTypes decl) ] 

variant  :: Signature f -> TypeName -> [a] -> [a]
variant = variance pfvsDL

contraVariant :: Signature f -> TypeName -> [a] -> [a]
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
-- substitutions
----------------------------------------------------------------------

o :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
o = substitute

identSubst :: TypeSubstitution
identSubst = TyVar

singletonSubst :: TypeVariable -> SimpleType -> TypeSubstitution
singletonSubst v tp = \ w -> if v == w then tp else TyVar w

substFromList :: [(TypeVariable,SimpleType)] -> TypeSubstitution
substFromList m v = fromMaybe (TyVar v) (lookup v m)

class TSubstitutable a where
  substitute :: TypeSubstitution -> a -> a

instance TSubstitutable SimpleType where
  substitute s (TyVar v)     = s v
  substitute s (TyCon n tps) = TyCon n (substitute s `map` tps)
  substitute s (tp1 :*: tp2) = substitute s tp1 :*: substitute s tp2
  substitute s (tp1 :-> tp2) = substitute s tp1 :-> substitute s tp2
  
instance TSubstitutable (Environment x) where
  substitute s env = Map.map (substitute s) env

instance (TSubstitutable a, TSubstitutable b) => TSubstitutable (a,b) where
  substitute s = substitute s *** substitute s

instance (TSubstitutable TypeSubstitution) where
  substitute s1 s2 = substitute s1 . s2



----------------------------------------------------------------------
-- variables
----------------------------------------------------------------------

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

----------------------------------------------------------------------
-- substitutions
----------------------------------------------------------------------

unifyType :: [(SimpleType,SimpleType)] -> Either (SimpleType,SimpleType) TypeSubstitution
unifyType = go identSubst where
  go s [] = return s
  go s ((tp1,tp2):ups) = do 
    (s',ups') <- step tp1 tp2
    go (s' `o` s) (ups' ++ (substitute s' `map` ups))

  step tp1            tp2           | tp1 == tp2           = return (identSubst, [])
  step (TyVar v)      tp2           | v `notElem` fvs tp2  = return (singletonSubst v tp2, [])
  step t              v@(TyVar _)                          = step v t
  step (tp1 :-> tp1') (tp2 :-> tp2')                       = return (identSubst, [(tp1,tp2), (tp1',tp2')])
  step (tp1 :*: tp1') (tp2 :*: tp2')                       = return (identSubst, [(tp1,tp2), (tp1',tp2')])
  step (TyCon n tps1) (TyCon m tps2) | n == m              = return (identSubst, zip tps1 tps2) 
  step tp1            tp2                                  = throwError (tp1,tp2)

antiUnifyType :: SimpleType -> SimpleType -> SimpleType
antiUnifyType a b = evalState (runUniqueT (step a b)) Map.empty where
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
    case Map.lookup (tpa,tpb) m of
      Nothing -> do
        v <- unique
        lift (put (Map.insert (tpa,tpb) v m))
        return (TyVar v)
      Just v -> return (TyVar v)

matchType :: SimpleType -> SimpleType -> Maybe TypeSubstitution
matchType a b = walk a b identSubst
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
-- pretty printers
----------------------------------------------------------------------

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

instance (PP.Pretty x) => PP.Pretty (Map.Map x SimpleType) where
  pretty env = PP.vcat $ PP.punctuate (PP.text ", ") [ PP.pretty x PP.<+> PP.text "::" PP.<+> PP.pretty tp | (x,tp) <- Map.toList env]
