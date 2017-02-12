module HoSA.Data.SizeType where

import           Data.List (nub)
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Maybe (fromJust)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified HoSA.Data.Index as Ix
import           HoSA.Data.MLTypes hiding (Signature,rename)
import           HoSA.Utils


----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

data Kind = T | S

data SizeType (knd :: Kind) ix where
  SzVar  :: TypeVariable -> SizeType knd ix
  SzCon :: TypeName -> [Schema ix] -> ix -> SizeType knd ix    
  SzPair :: SizeType knd ix -> SizeType knd ix -> SizeType knd ix
  SzArr  :: Schema ix -> Type ix -> Type ix
  SzQArr :: [Ix.VarId] -> Schema ix -> Type ix -> Schema ix

instance Foldable (SizeType knd) where
  foldr _ z SzVar{}       = z
  foldr f z (SzCon _ ts ix) = foldr (flip (foldr f)) (f ix z) ts
  foldr f z (SzPair t1 t2) = foldr f (foldr f z t2) t1
  foldr f z (SzArr p n) = foldr f (foldr f z n) p
  foldr f z (SzQArr _ p n) = foldr f (foldr f z n) p  


type Type = SizeType 'T
type Schema = SizeType 'S

type Signature f ix = Map.Map f (Schema ix)

skeleton :: SizeType knd ix -> SimpleType
skeleton (SzVar v)      = TyVar v
skeleton (SzCon n ts _) = TyCon n (skeleton `map` ts)
skeleton (SzPair t1 t2) = skeleton t1 :*: skeleton t2
skeleton (SzArr n p)    = skeleton n :-> skeleton p
skeleton (SzQArr _ n p) = skeleton n :-> skeleton p

toSchema :: SizeType knd ix -> Schema ix
toSchema (SzVar v)       = SzVar v
toSchema (SzCon n ts ix) = SzCon n ts ix
toSchema (SzPair t1 t2)  = SzPair (toSchema t1) (toSchema t2)
toSchema (SzArr n p)     = SzQArr [] n p
toSchema (SzQArr vs n p) = SzQArr vs n p

rename :: MonadUnique m => SizeType knd ix -> m (SizeType knd ix)
rename tp = do
  s <- sequence [ (v,) <$> unique | v <- nub (tvars tp)]
  return (ren s tp)
    where
      ren :: [(TypeVariable, Unique)] -> SizeType knd ix -> SizeType knd ix
      ren s (SzVar v)       = SzVar (fromJust (lookup v s))
      ren s (SzCon n ts ix) = SzCon n (ren s `map` ts) ix
      ren s (SzPair t1 t2)  = SzPair (ren s t1) (ren s t2)
      ren s (SzArr n p)     = SzArr (ren s n) (ren s p)
      ren s (SzQArr vs n p) = SzQArr vs (ren s n) (ren s p)

matrix :: MonadUnique m => Schema Ix.Term -> m ([Ix.VarId], Type Ix.Term)
matrix (SzVar v) = return ([], SzVar v)
matrix (SzPair s1 s2) = do
  (vs1,t1) <- matrix s1
  (vs2,t2) <- matrix s2
  return (vs1 ++ vs2, SzPair t1 t2)
matrix (SzCon n ss ix) = return ([], SzCon n ss ix)
matrix (SzQArr ixs n p) = do
  ixs' <- sequence [ uniqueToInt <$> unique | _ <- ixs]
  let subst = Ix.substFromList (zip ixs (Ix.fvar `map` ixs'))
  return (ixs', SzArr (Ix.inst subst n) (Ix.inst subst p))

returnIndex :: MonadUnique m => SizeType knd Ix.Term -> m Ix.Term
returnIndex (SzCon _ _ ix) = return ix
returnIndex (SzArr _ p)    = returnIndex p
returnIndex s@SzQArr{}     = matrix s >>= returnIndex . snd
returnIndex _              = error "returnIndex not defined on given sized-type"

traverseB :: Applicative f => ([Ix.VarId] -> ix -> f ix') -> SizeType knd ix -> f (SizeType knd ix')
traverseB = walk [] where
  walk :: Applicative f => [Ix.VarId] -> ([Ix.VarId] -> ix -> f ix') -> SizeType knd ix -> f (SizeType knd ix')
  walk _ _  (SzVar v)        = pure (SzVar v)
  walk bv f (SzCon n as ix)  = SzCon n <$> traverse (walk bv f) as <*> f bv ix
  walk bv f (SzPair t1 t2)   = SzPair <$> walk bv f t1 <*> walk bv f t2
  walk bv f (SzArr n p)      = SzArr <$> walk bv f n <*> walk bv f p
  walk bv f (SzQArr vs n p)  = SzQArr vs <$> walk bv' f n <*> walk bv' f p
    where bv' = vs ++ bv


type TypeOrSchema ix = Either (Type ix) (Schema ix)

instance Ix.Substitutable (SizeType knd Ix.Term) where
  type Image (SizeType knd Ix.Term) = Ix.Term
  subst_ _ (SzVar v)       = SzVar v
  subst_ s (SzCon n ts ix) = SzCon n (Ix.subst_ s `map` ts) (Ix.subst_ s ix)  
  subst_ s (SzArr n p)     = SzArr (Ix.subst_ s n) (Ix.subst_ s p)
  subst_ s (SzPair t1 t2)  = SzPair (Ix.subst_ s t1) (Ix.subst_ s t2)  
  subst_ s (SzQArr vs n p) = SzQArr vs (Ix.subst_ s' n) (Ix.subst_ s' p) where
    s' (Ix.BVar v) | v `elem` vs = Ix.Var (Ix.BVar v)
    s' v = s v

fvarsIx :: SizeType knd Ix.Term -> [Ix.VarId]
fvarsIx = foldr (\ ix vs -> Ix.fvars ix `List.union` vs) []

-- bvarsIx :: SizeType knd Ix.Term -> [Ix.VarId]
-- bvarsIx = foldr (\ ix vs -> Ix.bvars ix `List.union` vs) []

tvars :: SizeType knd ix -> [TypeVariable]
tvars (SzVar v)      = [v]
tvars (SzCon _ ts _) = concatMap tvars ts
tvars (SzArr n p)    = tvars n ++ tvars p
tvars (SzPair t1 t2) = tvars t1 ++ tvars t2
tvars (SzQArr _ n p) = tvars n ++ tvars p

metaVars :: SizeType knd Ix.Term -> [Ix.MetaVar]
metaVars = foldMap Ix.metaVars

-- pretty printing

prettyType :: (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
prettyType = ppTpe id
  where
    ppTpe :: (PP.Doc -> PP.Doc) -> (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
    ppTpe _ _   (SzVar v)          = PP.pretty v
    ppTpe _ pix (SzCon n [] ix)    = PP.group (PP.text n PP.<> PP.brackets (pix ix))
    ppTpe _ pix (SzCon n ts ix)    =
      PP.text n PP.<> PP.brackets (pix ix) PP.<> PP.tupled [ppTpe id pix t | t <- ts]
    ppTpe par pix (SzArr n t)      =      
      par (PP.nest 2 (PP.group (ppTpe PP.parens pix n
                     PP.<> PP.line PP.<> PP.text "->" PP.</> ppTpe id pix t)))
    ppTpe _ pix (SzPair t1 t2)   = PP.tupled [ppTpe id pix t1, ppTpe id pix t2]
    ppTpe par pix (SzQArr qvs n t) = par (PP.nest 2 (PP.group (ppQual qvs PP.<> ppTpe id pix (SzArr n t)))) where
        ppQual [] = PP.empty
        ppQual vs = PP.text "∀" PP.<+> ppSeq PP.space [ PP.pretty (Ix.BVar v) | v <- vs] PP.<> PP.text "."

instance PP.Pretty ix => PP.Pretty (SizeType knd ix) where
  pretty = prettyType PP.pretty

instance {-# OVERLAPABLE #-} (PP.Pretty f, PP.Pretty ix) => PP.Pretty (Signature f ix) where
  pretty sig = PP.vcat [ PP.hang 2 $ pp f n | (f, n) <- Map.toList sig ] where
    pp f n = PP.pretty "∑" PP.<> PP.parens (PP.pretty f) PP.<+> PP.text "↦" PP.<+> PP.pretty (runUnique (rename n))
  
