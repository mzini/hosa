module HoSA.SizeType.SOConstraint where

import           Control.Arrow (first)
import           Control.Monad (forM_)
import           Data.Tree (Forest)
import           Data.List ((\\))
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import           Data.Either (rights)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Control.Monad.IO.Class (MonadIO)
import qualified Constraints.Set.Solver as SetSolver

import qualified GUBS

import           HoSA.Data.Index
import           HoSA.Data.SizeType
import           HoSA.Utils



newtype V = V VarId deriving (Eq, Ord, Show)

type GubsCS = GUBS.ConstraintSystem Sym V

type FOCS = [Constraint]

data SOCS = SOCS [Constraint] [DConstraint]

type Interpretation = GUBS.Interpretation Sym
type Polynomial = GUBS.Polynomial Var
type Processor m = GUBS.Processor Sym Integer V m

instance Monoid SOCS where
  mempty = SOCS [] []
  SOCS cs1 ds1 `mappend` SOCS cs2 ds2 = SOCS (cs1 ++ cs2) (ds1 ++ ds2)




-- reduction to first order problem

vars :: Term -> [Either VarId MetaVar]
vars Zero = []
vars (Succ ix) = vars ix
vars (Sum ixs) = concatMap vars ixs
vars (Fun _ ixs) = concatMap vars ixs
vars (Var (BVar _)) = error "HoSA.SOConstraint.vars: constraint contains bound variable"
vars (Var (FVar v)) = [Left v]
vars (MVar mv) = [Right mv]



type SetConstraint = SetSolver.Inclusion Unique VarId

  
toSetConstraint :: [Constraint] -> [SetConstraint]
toSetConstraint = concatMap f where
  f (l :>=: r) = [ toExp vr SetSolver.<=! SetSolver.setVariable v
                | (Right (MetaVar v _)) <- vars l, vr <- vars r]
  f (l :=: r) = f (l :>=: r) ++ f (r :>=: l)
  toExp (Left v) = SetSolver.atom v
  toExp (Right (MetaVar v _)) = SetSolver.setVariable v
  
toFOCS :: (MonadUnique m, MonadIO m) => SOCS -> m FOCS
toFOCS (SOCS cs ds) = do
  let (Just solved) = SetSolver.solveSystem (toSetConstraint cs)
  forM_ (mvars cs) $ \ mv@(MetaVar u _) -> do
    let (Just vs) = catMaybes <$> map fromSolution <$> SetSolver.leastSolution solved u
    f <- uniqueSym 
    substituteMetaVar mv (Fun f (fvar `map` restrict u vs))
  return cs

  where
    restrict u vs = vs \\ [ v' | NOccur v' (MetaVar u' _) <- ds, u == u']
    uniqueSym = Sym Nothing <$> unique
    
    fromSolution SetSolver.EmptySet = Nothing
    fromSolution (SetSolver.ConstructedTerm c _ []) = Just c
  
    mvars = rights . concatMap (\ c -> vars (lhs c) ++ vars (rhs c))

      
toGubsCS :: FOCS -> GubsCS
toGubsCS = map gconstraint where
  gconstraint (l :>=: r) = gterm l GUBS.:>=: gterm r
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


-- interpretation
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

interpretSig :: (Eq c, Num c) => Interpretation c -> Signature f Term -> Signature f (Polynomial c)
interpretSig inter = Map.map (interpretType inter)

-- putting things together
solveConstraints :: (MonadUnique m, MonadIO m) => Processor m -> Signature f Term -> SOCS -> m (Maybe (Signature f (Polynomial Integer)), Forest String)
solveConstraints p sig socs = do
  cs <- toGubsCS <$> toFOCS socs
  first fromAnswer <$> cs `GUBS.solveWith` p
    where
      fromAnswer (GUBS.Sat i) = Just (interpretSig i sig)
      fromAnswer _ = Nothing

instance PP.Pretty V where
  pretty (V v) = PP.text "x" PP.<> PP.int v
