module HoSA.Data.CallSite where

import qualified Data.Map as M
import           Data.Maybe (fromJust)
import           Data.List (nub)
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type Ctx = [Location]

data CtxSymbol f = CtxSym { csSymbol   :: f
                          , csCallsite :: Location
                          , csContext  :: Maybe (CtxSymbol f) }
                 deriving (Eq, Ord, Show)

type CSAbstract f = (f, SimpleType, Location) -> CtxSymbol f -> CtxSymbol f

instance IsSymbol f => IsSymbol (CtxSymbol f) where
  isDefined = isDefined . csSymbol

initial :: f -> CtxSymbol f
initial f = CtxSym f 0 Nothing

locations :: CtxSymbol f -> [Location]
locations f = csCallsite f : maybe [] locations (csContext f)

cap :: Int -> CtxSymbol f -> CtxSymbol f
cap 0 f = f { csCallsite = 0, csContext = Nothing }
cap 1 f = f { csContext = Nothing }
cap i f = f { csContext = cap (i-1) <$> csContext f }


kca :: Eq f => Int -> CSAbstract f
kca n (f,tpf,l) g 
    | firstOrder tpf = CtxSym f 0 Nothing
    | csSymbol g == f = g
    | otherwise = cap n (CtxSym f l (Just g))
  where
    firstOrder (tp1 :-> tp2) = dataType tp1 && firstOrder tp2
    firstOrder tp = dataType tp

    dataType TyVar {}     = True
    dataType (TyCon _ as) = all dataType as
    dataType (a :*: b)    = dataType a && dataType b
    dataType _            = False
  

withCallContexts :: (Eq v, IsSymbol f, Eq f, Ord f) => CSAbstract f -> Maybe [f] -> TypedProgram f v -> TypedProgram (CtxSymbol f) v
withCallContexts abstr startSymbols p =
  walk [] [ (initial f, ident) | f <- M.keys (signature p), maybe True (elem f) startSymbols]
  where
    defines f eq = fst (definedSymbol (eqEqn eq)) == (csSymbol f)

    gtypeOf f = signature p M.! csSymbol f
      
    push (g,tp,l) f
      | isConstructor g = initial g
      | otherwise       = abstr (g,tp,l) f

  
    walk syms [] = TypedProgram { equations = concatMap definingEquation syms
                                , signature = sig }
      where
        sig = M.fromList (ds ++ cs)
        ds = [ (f,substitute subst (gtypeOf f)) | (f,subst) <- syms ]
        cs = [ (initial c, tp) | (c,tp) <- M.toList (signature p), isConstructor c ]
    walk seen (f:fs) =
      case ins f seen of
        Nothing -> walk seen fs
        Just seen' -> walk seen' (succs f ++ fs)
      
    succs (f, subst) = [ (push (f',tp,l) f, fromJust (matchType tp tp'))
                       | (f',tp',l) <- foldl (flip tfunsDL) [] bodies
                       , let tp = signature p M.! f']
      where
        bodies = [ substitute subst (rhs (eqEqn eq))| eq <- equations p, defines f eq ]
      
    ins e [] = Just [e]
    ins e1@(g,substg) (e2@(f, substf):fs)
      | f /= g = (:) e2 <$> ins e1 fs
      | subst `eqSubst` substf = Nothing
      | otherwise              = Just ((g,subst):fs)
      where
        vs = nub (fvs (gtypeOf g))
        subst = substFromList [ (v,substg v `antiUnifyType` substf v) | v <- vs]      
        s1 `eqSubst` s2 = and [ s1 v `equalModulo` s2 v | v <- vs]


    definingEquation (f,subst) =
      [ substitute subst TypedEquation { eqEnv = eqEnv teq
                                       , eqEqn = Equation (annotatedLhs teq) (annotatedRhs teq)
                                       , eqTpe = eqTpe teq }
      | teq <- equations p, defines f teq ]
      where
        annotatedLhs = mapExpression fun var . lhs . eqEqn where
          fun g tp _
            | g == csSymbol f = (f,tp)
            | otherwise       = (initial g, tp)
          var v  tp           = (v,tp)
        annotatedRhs = mapExpression fun var . rhs . eqEqn where
          fun g tp l = (push (g,tp,l) f, tp)
          var v  tp  = (v,tp)

-- -- pretty printing

instance PP.Pretty f => PP.Pretty (CtxSymbol f) where
  pretty (CtxSym f 0 Nothing) = PP.pretty f
  pretty f = PP.pretty (csSymbol f) PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") (PP.int `map` locations f)

