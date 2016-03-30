module HoSA.Solve where

import           Control.Arrow (first)
import           Data.Tree (Forest)
import           HoSA.Index
import           HoSA.SizeType

import qualified GUBS as GUBS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Control.Monad.IO.Class (MonadIO)

type Interpretation = GUBS.Interpretation Sym
type Polynomial = GUBS.Polynomial Var
type CS = GUBS.ConstraintSystem Sym VarId
type Processor m = GUBS.Processor Sym Integer VarId m

toCS :: [Constraint] -> CS
toCS cs = [ gterm l GUBS.:>=: gterm r | l :>=: r <- cs ] where --todo simplification?
  gterm Zero = 0
  gterm (Succ ix) = gterm ix + 1
  gterm (Sum ixs) = sum [gterm ix | ix <- ixs]
  gterm (Var (FVar v)) =  GUBS.Var v
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
interpretType inter (TyBase bt ix) = TyBase bt (interpretIx inter ix)
interpretType inter (TyArr n t) = TyArr (interpretType inter n) (interpretType inter t)
interpretType inter (TyQArr ixs n t) = TyQArr ixs (interpretType inter n) (interpretType inter t)

interpretSig :: (Eq c, Num c) => Interpretation c -> Signature f Term -> Signature f (Polynomial c)
interpretSig inter = mapSignature (interpretType inter)

solveConstraints :: MonadIO m => Processor m -> Signature f Term -> [Constraint] -> m (Maybe (Signature f (Polynomial Integer)), Forest String)
solveConstraints p sig cs = first fromAnswer <$> toCS cs `GUBS.solveWith` p where
  fromAnswer (GUBS.Sat i) = Just (interpretSig i sig)
  fromAnswer _ = Nothing

