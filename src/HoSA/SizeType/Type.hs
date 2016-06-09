module HoSA.SizeType.Type where

import           Data.List (nub)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           HoSA.Utils
import           HoSA.Data.Rewriting
import           HoSA.Data.SimpleType
import           HoSA.Data.CallSite
import qualified HoSA.SizeType.Index as Ix

data Kind = T | S

data SizeType (knd :: Kind) ix where 
  SzBase :: BaseType -> ix -> SizeType knd ix
  SzPair :: Type ix -> Type ix -> Type ix
  SzArr  :: Schema ix -> Type ix -> Type ix
  SzQArr :: [Ix.VarId] -> Schema ix -> Type ix -> Schema ix

type Type = SizeType 'T
type Schema = SizeType 'S

skeleton :: SizeType knd ix -> SimpleType
skeleton (SzBase (BT i) _) = TyBase (BT i)
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

-- uncurryUpto :: Type ix -> Int -> Maybe ([Schema ix], Type ix)
-- uncurryUpto t 0 = Just ([],t)
-- uncurryUpto (SzArr n t) i
--   | i > 0 = do
--       (ns,t') <- uncurryUpto t (i - 1)
--       return (n:ns,t')
-- uncurryUpto _ _ = Nothing

-- signature

newtype Signature ix = Signature { signatureToMap :: Map.Map Symbol [(CallCtx,Schema ix)] }

signatureFromList :: [(CallCtx,Schema ix)] -> Signature ix
signatureFromList = Signature . foldl insert Map.empty where
  insert m d@(cc,_) = Map.insertWith (++) (ctxSym cc) [d] m

signatureToList :: Signature ix -> [(CallCtx,Schema ix)]
signatureToList = concat . Map.elems . signatureToMap

lookupSchemas :: Symbol -> Signature ix -> [(CallCtx, Schema ix)]
lookupSchemas f = fromMaybe [] . Map.lookup f . signatureToMap

lookupSchema :: CallCtx -> Signature ix -> Maybe (Schema ix)
lookupSchema cc sig = do
  ss <- Map.lookup (ctxSym cc) (signatureToMap sig)
  lookup cc ss

mapSignature :: (Schema ix -> Schema ix') -> Signature ix -> Signature ix'
mapSignature f (Signature m) = Signature (Map.map (\ es -> [(cc,f s) | (cc,s) <- es]) m)

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

instance (PP.Pretty ix) => PP.Pretty (CallCtx ::: SizeType knd ix) where
  pretty (cc ::: s) = PP.pretty "∑" PP.<> PP.parens (PP.pretty cc) PP.<+> PP.text "↦" PP.<+> PP.pretty s
                                                                                                          
instance PP.Pretty ix => PP.Pretty (SizeType knd ix) where
  pretty = prettyType PP.pretty

instance (PP.Pretty ix) => PP.Pretty (Signature ix) where
  pretty sig = PP.vcat [ PP.hang 2 $ PP.pretty (cc ::: n) | (cc, n) <- signatureToList sig ]
