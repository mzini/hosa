module HoSA.SizeType where

import           Data.List (nub)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Rewriting.Applicative.SimpleTypes as ST
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           HoSA.CallSite
import qualified HoSA.Index as Ix
import           HoSA.Utils


data Kind = T | S

newtype BaseType = BT Int deriving (Eq)

data SizeType (knd :: Kind) ix where 
  TyBase :: BaseType -> ix -> SizeType knd ix
  TyArr  :: Schema ix -> Type ix -> Type ix
  TyQArr :: [Ix.VarId] -> Schema ix -> Type ix -> Schema ix

type Type = SizeType T
type Schema = SizeType S

skeleton :: SizeType knd ix -> ST.Type
skeleton (TyBase (BT i) _) = ST.BT i
skeleton (TyArr n p) = skeleton n ST.:~> skeleton p
skeleton (TyQArr _ n p) = skeleton n ST.:~> skeleton p


instance Ix.Substitutable (SizeType knd Ix.Term) where
  type Image (SizeType knd Ix.Term) = Ix.Term
  subst_ s (TyBase bt ix) = TyBase bt (Ix.subst_ s ix)
  subst_ s (TyArr n p) = TyArr (Ix.subst_ s n) (Ix.subst_ s p)
  subst_ s (TyQArr vs n p) = TyQArr vs (Ix.subst_ s' n) (Ix.subst_ s' p) where
    s' (Ix.BVar v) | v `elem` vs = Ix.Var (Ix.BVar v)
    s' v = s v

fvars :: SizeType knd Ix.Term -> [Ix.VarId]
fvars = nub . walk where
  walk :: SizeType knd Ix.Term -> [Ix.VarId]
  walk (TyBase _ ix) = Ix.fvars ix
  walk (TyArr n p) = walk n ++ walk p
  walk (TyQArr _ n p) = walk n ++ walk p  

uncurryUpto :: Type ix -> Int -> Maybe ([Schema ix], Type ix)
uncurryUpto t 0 = Just ([],t)
uncurryUpto (TyArr n t) i
  | i > 0 = do
      (ns,t') <- uncurryUpto t (i - 1)
      return (n:ns,t')
uncurryUpto _ _ = Nothing

-- signature

newtype Signature f ix = Signature { signatureToMap :: Map.Map f [(CallCtx f,Schema ix)] }

signatureFromList :: Ord f => [(CallCtx f,Schema ix)] -> Signature f ix
signatureFromList = Signature . foldl insert Map.empty where
  insert m d@(CallCtx f _ _,_) = Map.insertWith (++) f [d] m

signatureToList :: Signature f ix -> [(CallCtx f,Schema ix)]
signatureToList = concat . Map.elems . signatureToMap

lookupSchemas :: Ord f => f -> Signature f ix -> [(CallCtx f, Schema ix)]
lookupSchemas f = fromMaybe [] . Map.lookup f . signatureToMap

lookupSchema :: Ord f => CallCtx f -> Signature f ix -> Maybe (Schema ix)
lookupSchema cc@(CallCtx f _ _) sig = do
  ss <- Map.lookup f (signatureToMap sig)
  lookup cc ss

mapSignature :: (Schema ix -> Schema ix') -> Signature f ix -> Signature f ix'
mapSignature f (Signature m) = Signature (Map.map (\ es -> [(cc,f s) | (cc,s) <- es]) m)

-- pretty printing

instance PP.Pretty BaseType where
  pretty (BT i) = PP.text (names !! i) where
    names = [ [c] | c <- ['A'..'Z'] ] ++ [ 'B' : show i | i <- [(1 :: Int)..] ]
  

prettyType :: (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
prettyType = ppTpe id
  where
    ppTpe :: (PP.Doc -> PP.Doc) -> (ix -> PP.Doc) -> SizeType knd ix -> PP.Doc
    ppTpe _ pix (TyBase bt ix) = PP.pretty bt PP.<> PP.brackets (pix ix)
    ppTpe par pix (TyArr n t) =
      par (PP.hang 2 $
           ppTpe PP.parens pix n PP.<+> PP.text "->" PP.</> ppTpe id pix t)
    ppTpe par pix (TyQArr qvs n t) = par (PP.hang 2 $ ppQual qvs PP.</> ppTpe id pix (TyArr n t)) where
        ppQual [] = PP.empty
        ppQual vs = PP.text "forall" PP.<+> ppSeq PP.space [ PP.pretty (Ix.BVar v) | v <- vs] PP.<> PP.text "."

instance PP.Pretty ix => PP.Pretty (SizeType knd ix) where
  pretty = prettyType PP.pretty

instance (PP.Pretty f, PP.Pretty ix) => PP.Pretty (Signature f ix) where
  pretty sig = PP.vcat [ PP.hang 2 $ PP.pretty cc PP.<+> PP.text ":" PP.</> PP.pretty n
                       | (cc, n) <- signatureToList sig ]
