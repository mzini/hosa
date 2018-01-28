module HoSA.SizeType.SOConstraint where

import           Control.Arrow (first)
import           Control.Monad (forM_, void, filterM, when, forM)
import           Data.Tree (Forest)
import           Data.List ((\\))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Maybe (fromMaybe, isNothing, fromJust)
import           Data.Either (rights)
import           Data.Graph (graphFromEdges, reachable)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Control.Monad.IO.Class (MonadIO)

import qualified GUBS
import           GUBS.Algebra
import qualified GUBS.MaxPolynomial as Poly

import           HoSA.Data.Index
import           HoSA.Data.SizeType hiding (metaVars)
import           HoSA.Utils



newtype V = V VarId deriving (Eq, Ord, Show)

type GubsCS = GUBS.ConstraintSystem Sym V

type FOCS = [Constraint]

data SOCS = SOCS [Constraint] [DConstraint]

type Interpretation = GUBS.Interpretation Sym
type Polynomial = GUBS.MaxPoly Var
type Processor m = GUBS.Processor Sym Integer V m

instance Monoid SOCS where
  mempty = SOCS [] []
  SOCS cs1 ds1 `mappend` SOCS cs2 ds2 = SOCS (cs1 ++ cs2) (ds1 ++ ds2)


-- reduction to first order problem

vars :: MonadIO m => Term -> m [VarId]
vars Zero = return []
vars (Succ ix) = vars ix
vars (Mult _ ix) = vars ix
vars (Sum ixs) = concatMapM vars ixs
vars (Fun _ ixs) = concatMapM vars ixs
vars (Var (BVar _)) = error "HoSA.SOConstraint.vars: constraint contains bound variable"
vars (Var (FVar v)) = return [v]
vars (MVar mv) = peakMetaVar mv >>= maybe (return []) vars

isUnset :: MonadIO m => MetaVar -> m Bool
isUnset mv = isNothing <$> peakMetaVar mv

mvarIds :: MonadIO m => Term -> m [Unique]
mvarIds t = map metaVarId <$> filterM isUnset (metaVars t)

noccurs :: [DConstraint] -> MetaVar -> [VarId]
noccurs ds (MetaVar u _) = [ v' | NOccur v' (MetaVar u' _) <- ds, u == u']

-- inlineMVars :: MonadIO m => SOCS -> m SOCS
-- inlineMVars (SOCS cs ds) = do
--   uncurry substituteMetaVar `mapM_` Map.elems mvSubst
--   return (SOCS [ c | c <- cs, not (inlined c) ] ds)
--   where
--     mvSubst = Map.fromList [ (u,undefined)
--                            | [MVar mv@(MetaVar u _) :>=: r] <- groupWith (mvarId . lhs) cs]
--     mvarId (MVar (MetaVar u _)) = Just u
--     mvarId _                    = Nothing
--       -- foldl step Map.empty cs
--     -- step m (MVar mv@(MetaVar u _) :>=: r) = Map.alter alter u m where
--     --   alter Nothing = Just (mv, substFromList [ (v,Zero) | v <- noccurs ds mv ] `o` r)
--     --   alter Just{} = Nothing
--     -- step m (l :>=: _) = foldl (\ m' (MetaVar u _) -> Map.delete u m') m (metaVars l)

--     inlined (MVar (MetaVar u _) :>=: _) = u `Map.member` mvSubst
--     inlined _                           = False


skolemiseVars :: MonadIO m => [Constraint] -> m (Map.Map Unique (Set.Set VarId))
skolemiseVars cs = skolemiseVars' <$> forM cs (\ (l :>=: r) -> (,,) <$> mvarIds l <*> mvarIds r <*> vars r ) where
  skolemiseVars' vs = Map.fromList [(u,Set.fromList (rights (nf `map` reachable g (vf (Left u)))))
                                   | (mvsl,mvsr,_) <- vs
                                   , u <- mvsl ++ mvsr ]
    where
      vnodes = Map.fromList [ (Right v,[]) | (_,_,vsr) <- vs, v <- vsr ]
      mvnodes = Map.fromList [ (Left u,[]) | (mvsl,mvsr,_) <- vs, u <- mvsl ++ mvsr ]
      dependencies = Map.unionsWith (++) [ Map.fromList [ (Left u,map Left mvsr ++ map Right vsr) | u <- mvsl ]
                                         | (mvsl,mvsr,vsr) <- vs ]
      (g,nf,vf) = graphFromMap (Map.unions [dependencies, vnodes, mvnodes])
      
      graphFromMap m = (g', frst . nf', fromJust . vf')
        where (g',nf',vf') = graphFromEdges [ (n,n,ns) | (n,ns) <- Map.toList m]
              frst (a,_,_) = a
    
skolemise :: (MonadUnique m, MonadIO m) => SOCS -> m FOCS
skolemise (SOCS cs ds) = do
  svs <- skolemiseVars cs
  let mvs = concat [ metaVars l ++ metaVars r | l :>=: r <- cs]
      svars (MetaVar u _) = fromMaybe [] (Set.toList <$> Map.lookup u svs)
  forM_ mvs $ \ mv -> do
    unset <- isUnset mv
    when unset $ do 
      f <- Sym Nothing <$> unique
      void (substituteMetaVar mv (Fun f [fvar v | v <- svars mv \\ noccurs ds mv]))
  return cs


toFOCS :: (MonadUnique m, MonadIO m) => SOCS -> m FOCS
toFOCS = skolemise
      
toGubsCS :: FOCS -> GubsCS
toGubsCS = map gconstraint where
  gconstraint (l :>=: r) = gterm l GUBS.:>=: gterm r
  -- gconstraint (l :=: r)  = gterm l GUBS.:=: gterm r
  gterm Zero           = zero
  gterm (Succ ix)      = gterm ix .+ fromNatural (1::Integer)
  gterm (Mult n ix)    = fromNatural n .* gterm ix
  gterm (Sum ixs)      = sumA [gterm ix | ix <- ixs]
  gterm (Var (FVar v)) = GUBS.variable (V v)
  gterm (Var (BVar _)) = error "toCS: constraint list contains bound variable"
  gterm (Fun f ixs)    = GUBS.fun f (gterm `map` ixs)
  gterm (MVar mv)      =
    case unsafePeakMetaVar mv of
      Left _ -> error "toCS: unset meta variable"
      Right t -> gterm t


-- interpretation
type PartialPolynomial c = Maybe (Polynomial c)

interpretIx :: (IsNat c, Eq c, SemiRing c) => Interpretation c -> Term -> PartialPolynomial c
interpretIx _ Zero            = return zero
interpretIx _ (Var v)         = return (Poly.variable v)
interpretIx inter (Sum ixs)   = sumA <$> (interpretIx inter `mapM` ixs)
interpretIx inter (Mult n ix) = (.*) (fromNatural n) <$> interpretIx inter ix
interpretIx inter (Succ ix)   = (.+) one <$> interpretIx inter ix
interpretIx inter (Fun f ixs) = do
  p <- GUBS.get inter f (length ixs)
  GUBS.apply p <$> interpretIx inter `mapM` ixs
interpretIx _     MVar{}      = error "cannot interpret meta-variable"

interpretType :: (IsNat c, Eq c, SemiRing c) => Interpretation c -> SizeType knd Term -> SizeType knd (PartialPolynomial c)
interpretType _     (SzVar v)        = SzVar v
interpretType inter (SzCon n ts ix)  = SzCon n (interpretType inter `map` ts) (interpretIx inter ix)
interpretType inter (SzPair t1 t2)   = SzPair (interpretType inter t1) (interpretType inter t2)
interpretType inter (SzArr n t)      = SzArr (interpretType inter n) (interpretType inter t)
interpretType inter (SzQArr ixs n t) = SzQArr ixs (interpretType inter n) (interpretType inter t)

interpretSig :: (IsNat c, Eq c, SemiRing c) => Interpretation c -> Signature f Term -> Signature f (PartialPolynomial c)
interpretSig inter = Map.map (interpretType inter)

instance {-# OVERLAPPING #-} (Eq c, IsNat c, SemiRing c, PP.Pretty c) => PP.Pretty (PartialPolynomial c) where
  pretty Nothing = PP.text "?"
  pretty (Just p) = PP.pretty p
  
-- putting things together
type ConcreteSignature f = Signature f (PartialPolynomial Integer)
                                       
solveConstraints :: MonadIO m => Processor m -> Signature f Term -> FOCS -> m (Either (ConcreteSignature f) (ConcreteSignature f), Forest String)
solveConstraints p sig focs = first fromAnswer <$> (toGubsCS focs `GUBS.solveWithLog` p)
    where
      fromAnswer (GUBS.Sat i) = Right (interpretSig i sig)
      fromAnswer (GUBS.Open _ i) = Left (interpretSig i sig)

instance PP.Pretty V where
  pretty (V v) = PP.text "x" PP.<> PP.int v
