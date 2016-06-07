module HoSA.SizeType.Solve where

import           Control.Arrow (first)
import           Data.Tree (Forest)
import           HoSA.SizeType.Index
import           HoSA.SizeType.Type

import qualified GUBS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Control.Monad.IO.Class (MonadIO)

newtype V = V VarId deriving (Eq, Ord, Show)

type Interpretation = GUBS.Interpretation Sym
type Polynomial = GUBS.Polynomial Var
type CS = GUBS.ConstraintSystem Sym V
type Processor m = GUBS.Processor Sym Integer V m

toCS :: [Constraint] -> CS
toCS = map gconstraint where
  gconstraint (l :>=: r) = gterm l GUBS.:>=: gterm r --todo simplification?
  gconstraint (l :=: r) = gterm l GUBS.:=: gterm r
  gterm Zero = 0
  gterm (Succ ix) = gterm ix + 1
  gterm (Sum ixs) = sum [gterm ix | ix <- ixs]
  gterm (Var (FVar v)) =  GUBS.Var (V v)
  gterm (Var (BVar v)) =  error "toCS: constraint list contains bound variable"
  gterm (Fun f ixs) = GUBS.Fun f (gterm `map` ixs)
  gterm (MVar mv) =
    case unsafePeakVar mv of
      Left _ -> error "toCS: unset meta variable"
      Right t -> gterm t


interpretIx :: (Eq c, Num c) => Interpretation c -> Term -> Polynomial c
interpretIx _ Zero = GUBS.constant 0
interpretIx _ (Var v) = GUBS.variable v
interpretIx inter (Sum ixs) = sum (interpretIx inter `map` ixs)
interpretIx inter (Succ ix) = GUBS.constant 1 + interpretIx inter ix
interpretIx inter (Fun f ixs) = GUBS.get' inter f `GUBS.apply` (interpretIx inter `map` ixs)

interpretType :: (Eq c, Num c) => Interpretation c -> SizeType knd Term -> SizeType knd (Polynomial c)
interpretType inter (SzBase bt ix) = SzBase bt (interpretIx inter ix)
interpretType inter (SzPair t1 t2) = SzPair (interpretType inter t1) (interpretType inter t2)
interpretType inter (SzArr n t) = SzArr (interpretType inter n) (interpretType inter t)
interpretType inter (SzQArr ixs n t) = SzQArr ixs (interpretType inter n) (interpretType inter t)

interpretSig :: (Eq c, Num c) => Interpretation c -> Signature Term -> Signature (Polynomial c)
interpretSig inter = mapSignature (interpretType inter)

solveConstraints :: MonadIO m => Processor m -> Signature Term -> [Constraint] -> m (Maybe (Signature (Polynomial Integer)), Forest String)
solveConstraints p sig cs = first fromAnswer <$> toCS cs `GUBS.solveWith` p where
  fromAnswer (GUBS.Sat i) = Just (interpretSig i sig)
  fromAnswer _ = Nothing

instance PP.Pretty V where
  pretty (V v) = PP.text "x" PP.<> PP.int v
