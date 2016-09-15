module HoSA.Data.SizeType where

import           Data.List (nub)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           HoSA.Utils
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram hiding (Signature)
import           HoSA.Data.CallSite
import qualified HoSA.Data.Index as Ix

data Kind = T | S

data SizeType (knd :: Kind) ix where 
  SzBase :: BaseType -> ix -> SizeType knd ix
  SzPair :: Type ix -> Type ix -> Type ix
  SzArr  :: Schema ix -> Type ix -> Type ix
  SzQArr :: [Ix.VarId] -> Schema ix -> Type ix -> Schema ix

instance Foldable (SizeType knd) where
  foldr f z (SzBase _ ix) = f ix z
  foldr f z (SzPair t1 t2) = foldr f (foldr f z t2) t1
  foldr f z (SzArr p n) = foldr f (foldr f z n) p
  foldr f z (SzQArr _ p n) = foldr f (foldr f z n) p  

type Type = SizeType 'T
type Schema = SizeType 'S

skeleton :: SizeType knd ix -> SimpleType
skeleton (SzBase (BT i) _) = TyBase (BT i)
skeleton (SzPair t1 t2) = skeleton t1 :*: skeleton t2
skeleton (SzArr n p) = skeleton n :-> skeleton p
skeleton (SzQArr _ n p) = skeleton n :-> skeleton p


instance Ix.Substitutable (SizeType knd Ix.Term) where
  type Image (SizeType knd Ix.Term) = Ix.Term
  subst_ s (SzBase bt ix) = SzBase bt (Ix.subst_ s ix)
  subst_ s (SzArr n p) = SzArr (Ix.subst_ s n) (Ix.subst_ s p)
  subst_ s (SzPair t1 t2) = SzPair (Ix.subst_ s t1) (Ix.subst_ s t2)  
  subst_ s (SzQArr vs n p) = SzQArr vs (Ix.subst_ s' n) (Ix.subst_ s' p) where
    s' (Ix.BVar v) | v `elem` vs = Ix.Var (Ix.BVar v)
    s' v = s v

fvars :: SizeType knd Ix.Term -> [Ix.VarId]
fvars = nub . walk where
  walk :: SizeType knd Ix.Term -> [Ix.VarId]
  walk (SzBase _ ix) = Ix.fvars ix
  walk (SzArr n p) = walk n ++ walk p
  walk (SzPair t1 t2) = walk t1 ++ walk t2
  walk (SzQArr _ n p) = walk n ++ walk p  

metaVars :: SizeType knd Ix.Term -> [Ix.MetaVar]
metaVars = foldMap Ix.metaVars

type Signature f ix = Map.Map f (Schema ix)

-- newtype Signature f ix = Signature { signatureToMap :: Map.Map f [(Ctx,Schema ix)] }

-- signatureFromList :: Ord f => [(CtxSymbol f,Schema ix)] -> Signature f ix
-- signatureFromList = Signature . foldl insert Map.empty where
--   insert m (f,s) = Map.insertWith (++) (csSymbol f) [(csCallsite f,s)] m

-- signatureToList :: Signature f ix -> [(CtxSymbol f,Schema ix)]
-- signatureToList (Signature m) = concatMap t (Map.toList m) where
--   t (f,ss) = [(CtxSym { csSymbol = f, csCallsite = cs },s) | (cs,s) <- ss]

-- lookupSchemas :: Ord f => f -> Signature f ix -> [(Ctx, Schema ix)]
-- lookupSchemas f = fromMaybe [] . Map.lookup f . signatureToMap

-- lookupSchema :: Ord f => CtxSymbol f -> Signature f ix -> Maybe (Schema ix)
-- lookupSchema f sig = do
--   ss <- Map.lookup (csSymbol f) (signatureToMap sig)
--   lookup (csCallsite f) ss

-- mapSignature :: (Schema ix -> Schema ix') -> Signature f ix -> Signature f ix'
-- mapSignature f (Signature m) = Signature (Map.map (\ es -> [(cc,f s) | (cc,s) <- es]) m)

-- pretty printing

prettyType :: (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
prettyType = ppTpe id
  where
    ppTpe :: (PP.Doc -> PP.Doc) -> (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
    ppTpe _ pix (SzBase bt ix) = PP.pretty bt PP.<> PP.brackets (pix ix)
    ppTpe par pix (SzArr n t) =      
      par (PP.hang 2 $
           ppTpe PP.parens pix n PP.<+> PP.text "->" PP.</> ppTpe id pix t)
    ppTpe par pix (SzPair t1 t2) =
      PP.parens (ppTpe id pix t1 PP.<//> PP.text ","  PP.<+> ppTpe id pix t2)
    ppTpe par pix (SzQArr qvs n t) = par (PP.hang 2 $ ppQual qvs PP.</> ppTpe id pix (SzArr n t)) where
        ppQual [] = PP.empty
        ppQual vs = PP.text "∀" PP.<+> ppSeq PP.space [ PP.pretty (Ix.BVar v) | v <- vs] PP.<> PP.text "."

-- instance (PP.Pretty f,PP.Pretty ix) => PP.Pretty (CallCtx f ::: SizeType knd ix) where
--   pretty (cc ::: s) = 
                                                                                                          
instance PP.Pretty ix => PP.Pretty (SizeType knd ix) where
  pretty = prettyType PP.pretty

instance (PP.Pretty f, PP.Pretty ix) => PP.Pretty (Signature f ix) where
  pretty sig = PP.vcat [ PP.hang 2 $ pp f n | (f, n) <- Map.toList sig ] where
    pp f n = PP.pretty "∑" PP.<> PP.parens (PP.pretty f) PP.<+> PP.text "↦" PP.<+> PP.pretty n
  
