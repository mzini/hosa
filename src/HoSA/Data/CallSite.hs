module HoSA.Data.CallSite where

import qualified Data.Map as M
import           Control.Monad (forM)
import           HoSA.Utils
import           HoSA.Data.Expression
import           HoSA.Data.SimplyTypedProgram
import           Control.Monad.Writer
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type Ctx = [Location]

data CtxSymbol f = CtxSym { csSymbol :: f
                          , csCallsite :: [Location] }
                 deriving (Eq, Ord, Show)

type CSAbstract f = (f, SimpleType, Location) -> CtxSymbol f -> CtxSymbol f

instance IsSymbol f => IsSymbol (CtxSymbol f) where
  isDefined = isDefined . csSymbol

kca :: Int -> CSAbstract f
kca n (f,tp,l) (CtxSym g ls) = CtxSym f ctx where
  ctx 
    | firstOrder tp = []
    | otherwise = take n (l:ls)

  firstOrder (tp1 :-> tp2) = dataType tp1 && firstOrder tp2
  firstOrder tp = dataType tp

  dataType TyBase{} = True
  dataType (a :*: b) = dataType a && dataType b
  dataType _ = False
  

withCallContexts :: Ord f => CSAbstract f -> Maybe [f] -> TypedProgram f v -> TypedProgram (CtxSymbol f) v
withCallContexts abstr startSymbols p = walk [] [CtxSym f [] | f <- M.keys sig, maybe True (elem f) startSymbols] where
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
      annotateArg (Fun f tp l) = [ Fun f' tp l | f' <- fs, csSymbol f' == f ]
      annotateArg (Apply s t) = Apply <$> annotateArg s <*> annotateArg t

  annotateRhs f = mapExpression (\ g tp l -> (abstr (g,tp,l) f, tp)) (\ v tp -> (v,tp))

-- -- pretty printing

instance PP.Pretty f => PP.Pretty (CtxSymbol f) where
  pretty (CtxSym f []) = PP.pretty f
  pretty (CtxSym f ls) = PP.pretty f PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") [PP.int l | l <- ls]

-- instance PP.Pretty f => PP.Pretty (CallCtx f) where
--   pretty (CallCtx cs@(CallSite (f ::: _) _) css) = 
--     

-- -- instance {-# OVERLAPPING  #-} (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedTerm f v) where
-- --   pretty = PP.pretty . tmap toSym id where
-- --     toSym (CallSite (Symbol f ::: _) i) = Symbol (f ++ "@" ++ show i)
  
-- instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (AnnotatedRule f v) where
--   pretty rl = PP.hang 2 (PP.pretty (lhs (arlUntypedRule rl)) PP.<+> PP.text "=" PP.</> PP.pretty (arlAnnotatedRhs rl))
