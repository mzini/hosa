module HoSA.SizeType.SOConstraint where

import           Control.Arrow (first)
import           Control.Monad (forM_, void, filterM, when, (>=>))
import           Data.Tree (Forest)
import           Data.List ((\\))
import           Data.Maybe (isNothing)
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Control.Monad.IO.Class (MonadIO)
import           Constraints.Set.Solver (atom, setVariable, (<=!))
import qualified Constraints.Set.Solver as SSolver

import qualified GUBS

import           HoSA.Data.Index
import           HoSA.Data.SizeType hiding (metaVars)
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

-- vars :: Term -> [Either VarId MetaVar]
-- vars Zero = []
-- vars (Succ ix) = vars ix
-- vars (Sum ixs) = concatMap vars ixs
-- vars (Fun _ ixs) = concatMap vars ixs
-- vars (Var (BVar _)) = error "HoSA.SOConstraint.vars: constraint contains bound variable"
-- vars (Var (FVar v)) = [Left v]
-- vars (MVar mv) = [Right mv]


vars :: MonadIO m => Term -> m [VarId]
vars Zero = return []
vars (Succ ix) = vars ix
vars (Sum ixs) = concatMapM vars ixs
vars (Fun _ ixs) = concatMapM vars ixs
vars (Var (BVar _)) = error "HoSA.SOConstraint.vars: constraint contains bound variable"
vars (Var (FVar v)) = return [v]
vars (MVar mv) = peakMetaVar mv >>= maybe (return []) vars


type SetConstraint = SSolver.Inclusion Unique VarId

isUnset :: MonadIO m => MetaVar -> m Bool
isUnset mv = isNothing <$> peakMetaVar mv

toSetConstraint :: MonadIO m => [Constraint] -> m [SetConstraint]
toSetConstraint = concatMapM f where
  f (l :>=: r) = do
    mvsl <- filterM isUnset (metaVars l)
    mvsr <- filterM isUnset (metaVars r)
    vsr <- vars r
    let inclusions  = [ atom vr <=! setVariable mvl
                      | (MetaVar mvl _) <- mvsl, vr <- vsr ]
        memberships = [ setVariable mvr <=! setVariable mvl
                      | (MetaVar mvl _) <- mvsl, (MetaVar mvr _) <- mvsr ]
    return (inclusions ++ memberships)
    
noccurs :: [DConstraint] -> MetaVar -> [VarId]
noccurs ds (MetaVar u _) = [ v' | NOccur v' (MetaVar u' _) <- ds, u == u']

inlineMVars :: MonadIO m => SOCS -> m SOCS
inlineMVars (SOCS cs ds) = do
  uncurry substituteMetaVar `mapM_` Map.elems mvSubst
  return (SOCS [ c | c <- cs, not (inlined c) ] ds)
  where
    mvSubst = foldl step Map.empty cs
    step m (MVar mv@(MetaVar u _) :>=: r) = Map.alter alter u m where
      alter Nothing = Just (mv, substFromList [ (v,Zero) | v <- noccurs ds mv ] `o` r)
      alter Just{} = Nothing
    step m (l :>=: _) = foldl (\ m' (MetaVar u _) -> Map.delete u m') m (metaVars l)

    inlined (MVar (MetaVar u _) :>=: _) = u `Map.member` mvSubst
    inlined _                           = False


skolemise :: (MonadUnique m, MonadIO m) => SOCS -> m FOCS
skolemise socs@(SOCS cs ds) = do
  Just solved <- SSolver.solveSystem <$> toSetConstraint cs
  let mvs = concat [ metaVars l ++ metaVars r | l :>=: r <- cs]
  forM_ mvs $ \ mv@(MetaVar u _) -> do
    unset <- isUnset mv
    when unset $ do 
      let (Just vs) = catMaybes <$> map fromSolution <$> SSolver.leastSolution solved u
      f <- Sym Nothing <$> unique
      void (substituteMetaVar mv (Fun f [fvar v | v <- vs \\ noccurs ds mv]))
  return cs

  where
    fromSolution SSolver.EmptySet                 = Nothing
    fromSolution (SSolver.ConstructedTerm c _ []) = Just c
    fromSolution _                                  = error "Don't know what to do with Set-Solver solution"

toFOCS :: (MonadUnique m, MonadIO m) => SOCS -> m FOCS
toFOCS = inlineMVars >=> skolemise
      
toGubsCS :: FOCS -> GubsCS
toGubsCS = map gconstraint where
  gconstraint (l :>=: r) = gterm l GUBS.:>=: gterm r
  -- gconstraint (l :=: r)  = gterm l GUBS.:=: gterm r
  gterm Zero           = 0
  gterm (Succ ix)      = gterm ix + 1
  gterm (Sum ixs)      = sum [gterm ix | ix <- ixs]
  gterm (Var (FVar v)) =  GUBS.Var (V v)
  gterm (Var (BVar _)) =  error "toCS: constraint list contains bound variable"
  gterm (Fun f ixs)    = GUBS.Fun f (gterm `map` ixs)
  gterm (MVar mv)      =
    case unsafePeakMetaVar mv of
      Left _ -> error "toCS: unset meta variable"
      Right t -> gterm t


-- interpretation
-- TODO 
interpretIx :: (Eq c, Num c) => Interpretation c -> Term -> Polynomial c
interpretIx _ Zero = GUBS.constant 0
interpretIx _ (Var v) = GUBS.variable v
interpretIx inter (Sum ixs) = sum (interpretIx inter `map` ixs)
interpretIx inter (Succ ix) = GUBS.constant 1 + interpretIx inter ix
interpretIx inter (Fun f ixs) = p `GUBS.apply` (interpretIx inter `map` ixs) where
  p = case GUBS.get inter f of
        Just p' -> p'
        Nothing -> fromInteger 0

interpretType :: (Eq c, Num c) => Interpretation c -> SizeType knd Term -> SizeType knd (Polynomial c)
interpretType _     (SzVar v)        = SzVar v
interpretType inter (SzCon n ts ix)  = SzCon n (interpretType inter `map` ts) (interpretIx inter ix)
interpretType inter (SzPair t1 t2)   = SzPair (interpretType inter t1) (interpretType inter t2)
interpretType inter (SzArr n t)      = SzArr (interpretType inter n) (interpretType inter t)
interpretType inter (SzQArr ixs n t) = SzQArr ixs (interpretType inter n) (interpretType inter t)

interpretSig :: (Eq c, Num c) => Interpretation c -> Signature f Term -> Signature f (Polynomial c)
interpretSig inter = Map.map (interpretType inter)

-- putting things together
solveConstraints :: (MonadUnique m, MonadIO m) => Processor m -> Signature f Term -> FOCS -> m (Maybe (Signature f (Polynomial Integer)), Forest String)
solveConstraints p sig focs = do
  first fromAnswer <$> (toGubsCS focs `GUBS.solveWith` p)
    where
      fromAnswer (GUBS.Sat i) = Just (interpretSig i sig)
      fromAnswer _ = Nothing

instance PP.Pretty V where
  pretty (V v) = PP.text "x" PP.<> PP.int v
