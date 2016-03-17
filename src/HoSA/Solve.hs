module HoSA.Solve where

import HoSA.Index
import HoSA.SizeType
import Data.Typeable (Typeable)
import Data.Data (Data)

import qualified GUBS as GUBS
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.IO.Class (MonadIO)

type Interpretation = GUBS.Interpretation Sym
type Polynomial = GUBS.Polynomial Var
type CS = GUBS.ConstraintSystem Sym VarId

toCS :: [Constraint] -> CS
toCS cs = [ gterm l GUBS.:>=: gterm r | l :>=: r <- cs ] where --todo simplification?
  gterm Zero = 0
  gterm (Succ ix) = gterm ix + 1
  gterm (Sum ixs) = sum [gterm ix | ix <- ixs]
  gterm (Var (FVar v)) =  GUBS.Var v
  gterm (Var (BVar v)) =  error "toCS: constraint list contains bound variable"
  gterm (Fun f ixs) = GUBS.Fun f (gterm `map` ixs)


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

data Solver = MiniSmt | Z3 deriving (Show, Data, Typeable)

solveConstraints :: MonadIO m => Solver -> Signature f Term -> [Constraint] -> m (Maybe (Signature f (Polynomial Integer)))
solveConstraints solver sig cs = do 
  mi <- case solver of { Z3 -> GUBS.z3 solveM; MiniSmt -> GUBS.miniSMT solveM }
  return (interpretSig <$> mi <*> return sig)
  where
    solveM :: GUBS.Solver s m => GUBS.SolverM s m (Maybe (GUBS.Interpretation Sym Integer))
    solveM = GUBS.solveWith GUBS.Simple GUBS.empty (toCS cs)
-- pretty printing


ppPower :: PP.Pretty a => (a, Int) -> PP.Doc
ppPower (v,i) = PP.pretty v PP.<> if i == 1 then PP.empty else PP.char '^' PP.<> PP.int i

instance PP.Pretty v => PP.Pretty (GUBS.Monomial v) where
  pretty mono = pretty' (GUBS.toPowers mono) where
    pretty' [] = PP.char '1'
    pretty' ps = PP.hcat (PP.punctuate (PP.char '*') [ppPower p | p <- ps])

instance (Eq c, Num c, PP.Pretty c, PP.Pretty v) => PP.Pretty (GUBS.Polynomial v c) where
  pretty poly = pretty' [p | p <- GUBS.toMonos poly, fst p /= 0] where 
    pretty' [] = PP.char '0'
    pretty' ps = PP.hcat (PP.punctuate (PP.char '+') (ppMono `map` ps))
    ppMono (1,mono) = PP.pretty mono
    ppMono (c,GUBS.toPowers -> []) = PP.pretty c
    ppMono (c,mono) = PP.pretty c PP.<> PP.char '*' PP.<> PP.pretty mono


