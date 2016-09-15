module HoSA.Ticking
  ( tickProgram
  -- , ntickATRS
  , TSymbol (..)
  , arity
  , translatedType
  , constrType
  , auxType
  , TVariable
  , TickedExpression
  , TickedEquation
  , TickedProgram)
where

import Control.Monad.Trans (lift)
import Control.Monad.Writer
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Map as Map
import Data.Maybe (catMaybes)

import HoSA.Data.Expression
import HoSA.Data.SimplyTypedProgram
import HoSA.Utils

data TSymbol f = TSymbol f Int -- auxiliary symbols f_i
             | TConstr f -- constructors
             | Tick -- tick constructor 
  deriving (Eq, Ord)

instance IsSymbol f => IsSymbol (TSymbol f) where
  isDefined TSymbol{} = True
  isDefined _ = False
  
data TVariable v = IdentV v
               | Fresh Int
  deriving (Eq, Ord)

type TickedExpression f v = TypedExpression (TSymbol f) (TVariable v)
type TickedEquation f v = TypedEquation (TSymbol f) (TVariable v)
type TickedProgram f v = TypedProgram (TSymbol f) (TVariable v)

type ArityDecl f = f -> Int

arity :: (Eq f, IsSymbol f, Ord f) => TypedProgram f v -> ArityDecl f
arity p = \ f -> arities Map.! f where
  
  arities = Map.mapWithKey ar (signature p)
  
  ar f tp | isConstructor f = tarity tp
          | otherwise = darity f
          
  darity f = maximum $ 0 : [ length args
                           | eq <- equations p
                           , let (Fun g _ _, args) = sexpr (lhs (eqEqn eq))
                           , f == g ]
             
----------------------------------------------------------------------
-- translation of simply typed terms
----------------------------------------------------------------------

clockType :: SimpleType
clockType = TyBase Clock

tick :: TickedExpression f v -> TickedExpression f v
tick t = Fun Tick (clockType :-> clockType) 0 `Apply` t

-- ticking monad
type TickM f a = WriterT [(TSymbol f,SimpleType)] (UniqueT UniqueM) a

runTick :: TickM f a -> (a, [(TSymbol f,SimpleType)])
runTick = runUnique . runUniqueT . runWriterT

freshLoc :: TickM f Location
freshLoc = uniqueToInt <$> lift unique

-- types
translatedType :: SimpleType -> SimpleType
translatedType (TyBase b) = TyBase b
translatedType (t1 :*: t2) = translatedType t1 :*: translatedType t2
translatedType (t1 :-> t2) = translatedType t1 :-> clockType :-> (translatedType t2 :*: clockType)

auxType :: SimpleType -> Int -> SimpleType
auxType tp 0 = clockType :-> (translatedType tp :*: clockType)
auxType (tp1 :-> tp2) i = translatedType tp1 :-> auxType tp2 (i - 1)

constrType :: SimpleType -> SimpleType 
constrType (t1 :-> t2) = translatedType t1 :-> constrType t2
constrType (TyBase b) = TyBase b

-- symbols and variables

freshVar :: TickM f (TVariable v)
freshVar = Fresh <$> uniqueToInt <$> unique

var :: v -> TVariable v
var = IdentV

resetFreshVar :: TickM f ()
resetFreshVar = reset


auxFun :: f -> SimpleType -> Int -> TickM f (TickedExpression f v)
auxFun f tp i = tell [(f',tp')] >> (Fun f' tp' <$> freshLoc)
  where
    tp' = auxType tp i
    f' = TSymbol f i    

constrSym :: f -> SimpleType -> TickM f (TSymbol f, SimpleType)
constrSym f tp = tell [(f',tp')] >> return (f',tp')
  where
    tp' = constrType tp
    f'  = TConstr f

constrFun :: f -> SimpleType -> TickM f (TickedExpression f v)
constrFun f tp = do
  (f',tp') <- constrSym f tp
  Fun f' tp' <$> freshLoc

-- rules
translateLhs :: ArityDecl f -> TypedExpression f v -> TickedExpression f v -> TickM f (TickedExpression f v)
translateLhs ar l t =  Apply <$> renameHead l <*> return t where
  renameHead (sexpr -> (Fun f tpf _,rest)) = fromSexpr <$> hd' <*> rest' where
    hd' = auxFun f tpf (length rest)
    rest' = mapExpressionM (\ f tp _ -> constrSym f tp) (\ v tp -> pure (var v,tp)) `mapM` rest

translateRhs :: IsSymbol f => ArityDecl f -> TypedExpression f v -> TickedExpression f v -> TickM f (TickedExpression f v)
translateRhs ar e t = translateK e t (\ e' t' -> return (e' `Pair` tick t')) where
  translateK (Var v tp) t k = k (Var (var v) tp) t
  translateK (Fun f tp _) t k | isConstructor f && ar f == 0 = constrFun f tp >>= flip k t
  translateK (Fun f tp _) t k = auxFun f tp 1 >>= flip k t
  translateK (Apply e1 e2) t k = translateK e1 t k1 where
    k1 e1' t1 = translateK e2 t1 (k2 e1')
    k2 e1' e2' t2 = do
      let (tp1 :-> tp2) = typeOf e1
      ve <- freshVar
      vc <- freshVar
      let te = translatedType tp2
      LetP (Apply (Apply e1' e2') t2) ((ve,te),(vc,clockType)) <$> k (Var ve te) (Var vc clockType)

translateEnv :: Ord v => TVariable v -> Environment v -> Environment (TVariable v)
translateEnv t env = Map.insert t clockType $ Map.fromList [ (IdentV w, translatedType tp) | (w, tp) <- Map.toList env ]

translateEquation :: (Ord v, IsSymbol f) => ArityDecl f -> TypedEquation f v -> TickM f (TickedEquation f v)
translateEquation ar TypedEquation {..} = do
  resetFreshVar
  t <- freshVar
  l' <- translateLhs ar (lhs eqEqn) (Var t clockType)
  r' <- translateRhs ar (rhs eqEqn) (Var t clockType)
  return TypedEquation { eqEnv = translateEnv t eqEnv
                       , eqEqn = Equation l' r'
                       , eqTpe = translatedType eqTpe :*: clockType}

auxiliaryEquations :: (IsSymbol f, Ord v) => ArityDecl f -> (f,SimpleType) -> TickM f [TickedEquation f v]
                                                                          
auxiliaryEquations ar (f,tpf) = mapM (auxEquation tpf) [1 .. if isDefined f then arf - 1 else arf] where
    arf = ar f
    vars = walk 1 tpf where
    walk i (tp1 :-> tp2) = (Var (Fresh i) (translatedType tp1)) : walk (i+1) tp2
    walk _ _ = []

    auxEquation tp i = do
      fi <- auxFun f tpf i
      fi' <- if i < arf then auxFun f tpf (i + 1) else constrFun f tpf
      let t = Var (Fresh (i+1)) clockType
          vs = take i vars
          l = fromSexpr fi (vs ++ [t])
          r = fromSexpr fi' vs `Pair` t
      return TypedEquation { eqEnv = Map.fromList [ (v,tp) | Var v tp <- t : vs ]
                           , eqEqn = Equation l r 
                           , eqTpe = typeOf l }

tickProgram :: (Ord v, IsSymbol f, Ord f) => TypedProgram f v -> (TickedProgram f v, TickedProgram f v)
tickProgram p = ( TypedProgram { equations = eqs, signature = Map.fromList fs }
                , TypedProgram { equations = aeqs, signature = Map.fromList afs })
  where
    (eqs,fs) = runTick $ translateEquation (arity p) `mapM` equations p
    (aeqs,afs) = runTick $ auxiliaryEquations (arity p) `concatMapM` (Map.toList (signature p))
         -- ++ auxEquations ar `concatMap` signatureToDecls (statrsSignature statrs)

-- ntickATRS :: STAtrs Symbol Variable -> TickedAtrs
-- ntickATRS statrs = STAtrs { statrsEquations = rs
--                           , statrsSignature = signatureFromDecls (funs rs) }
--   where
--     rs = liftSTEquation `map` statrsEquations statrs
--     liftSTEquation STEquation { .. } = STEquation { strlEnv = Map.mapKeys IdentV strlEnv
--                                       , strlUntypedEquation = liftEquation liftUTExpression strlUntypedEquation
--                                       , strlTypedEquation = liftEquation liftTExpression strlTypedEquation
--                                       , strlType = strlType}

--     liftEquation f (Equation l r) = Equation (f l) (f r)
--     liftTExpression = tmap (\ (f ::: tp) -> liftFun f ::: tp) (\ (v ::: tp) -> IdentV v ::: tp)
--     liftUTExpression = tmap liftFun IdentV
--     liftFun f@Defined{} = TSymbol f 0
--     liftFun f@Constr{} = TConstr f
      
                   
         
-- pretty printers
instance PP.Pretty f => PP.Pretty (TSymbol f) where
  pretty (TSymbol f 0) = PP.bold (PP.pretty f)
  pretty (TSymbol f i) = PP.bold (PP.pretty f) PP.<> PP.text "#" PP.<> PP.int i
  pretty (TConstr c) = PP.pretty c
  pretty Tick = PP.text "T"
  
instance PP.Pretty v => PP.Pretty (TVariable v) where
  pretty (IdentV v) = PP.pretty v
  pretty (Fresh u) = PP.text "v" PP.<> PP.int u
