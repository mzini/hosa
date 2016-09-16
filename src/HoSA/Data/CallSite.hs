module HoSA.Data.CallSite where

import qualified Data.Map as M
import           Control.Monad (forM)
import           HoSA.Utils
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram
import           Control.Monad.Writer
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type Ctx = [Location]

data CtxSymbol f = CtxSym { csSymbol   :: f
                          , csCallsite :: Location
                          , csContext  :: Maybe (CtxSymbol f) }
                 deriving (Eq, Ord, Show)

type CSAbstract f = (f, SimpleType, Location) -> CtxSymbol f -> CtxSymbol f

instance IsSymbol f => IsSymbol (CtxSymbol f) where
  isDefined = isDefined . csSymbol

locations :: CtxSymbol f -> [Location]
locations f = csCallsite f : maybe [] locations (csContext f)

cap :: Int -> CtxSymbol f -> CtxSymbol f
cap 0 f = f { csCallsite = 0, csContext = Nothing }
cap 1 f = f { csContext = Nothing }
cap i f = f { csContext = cap (i-1) <$> csContext f }


kca :: Eq f => Int -> CSAbstract f
kca n (f,tp,l) g 
    | firstOrder tp = CtxSym f 0 Nothing
    | csSymbol g == f = g
    | otherwise = cap n (CtxSym f l (Just g))
  where
    firstOrder (tp1 :-> tp2) = dataType tp1 && firstOrder tp2
    firstOrder tp = dataType tp

    dataType TyBase{} = True
    dataType (a :*: b) = dataType a && dataType b
    dataType _ = False
  

withCallContexts :: (IsSymbol f, Ord f) => CSAbstract f -> Maybe [f] -> TypedProgram f v -> TypedProgram (CtxSymbol f) v
withCallContexts abstr startSymbols p = walk [] [CtxSym f 0 Nothing | f <- M.keys sig, maybe True (elem f) startSymbols || isConstructor f] where
  sig = signature p
  eqs = equations p
  definedBy f eq = fst (definedSymbol (eqEqn eq)) == (csSymbol f)
  
  walk seen [] = TypedProgram { equations = definingEquations seen
                              , signature = M.fromList [ (f,sig M.! csSymbol f) | f <- seen ] }
  walk seen (f:fs)
    | f `elem` seen = walk seen fs
    | otherwise     = walk (f : seen) (succs f ++ fs)

  succs f = execWriter $ forM bodies $
    mapExpressionM (\ g tp l -> let g' = abstr (g,tp,l) f in tell [g'] >> return (g',tp))
                   (\ v tp -> return (v,tp))
    where bodies = [ (rhs (eqEqn eq)) | eq <- eqs , definedBy f eq ]                               

  definingEquations fs = concatMap definingEquation fs where
    definingEquation f = do
      eq <- filter (definedBy f) eqs
      l <- annotateLhs f (lhs (eqEqn eq))
      let r = annotateRhs f (rhs (eqEqn eq))
      return TypedEquation { eqEnv = eqEnv eq
                           , eqEqn = Equation l r
                           , eqTpe = eqTpe eq }

    annotateLhs f (Fun _ tp l) = [Fun f tp l]
    annotateLhs f (Apply s t) = Apply <$> annotateLhs f s <*> annotateArg t where
      annotateArg (Var v tp) = [Var v tp]
      annotateArg (Fun g tp l) = [ Fun g' tp l | g' <- fs, csSymbol g' == g ]
      annotateArg (Apply s t) = Apply <$> annotateArg s <*> annotateArg t

  annotateRhs f = mapExpression (\ g tp l -> (abstr (g,tp,l) f, tp)) (\ v tp -> (v,tp))

-- -- pretty printing

instance PP.Pretty f => PP.Pretty (CtxSymbol f) where
  pretty (CtxSym f 0 Nothing) = PP.pretty f
  pretty f = PP.pretty (csSymbol f) PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") (PP.int `map` locations f)

-- instance PP.Pretty f => PP.Pretty (CallCtx f) where
--   pretty (CallCtx cs@(CallSite (f ::: _) _) css) = 
--     

-- -- instance {-# OVERLAPPING  #-} (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedTerm f v) where
-- --   pretty = PP.pretty . tmap toSym id where
-- --     toSym (CallSite (Symbol f ::: _) i) = Symbol (f ++ "@" ++ show i)
  
-- instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedRule f v) where
--   pretty rl = PP.hang 2 (PP.pretty (lhs (arlUntypedRule rl)) PP.<+> PP.text "=" PP.</> PP.pretty (arlAnnotatedRhs rl))
