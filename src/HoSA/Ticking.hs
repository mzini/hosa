module HoSA.Ticking
  ( tickProgram
  -- , ntickATRS
  , TSymbol (..)
  , arity
  , translatedType
  , clockType
  , auxType
  , TVariable
  , TickedExpression
  , TickedEquation
  , TickedProgram)
where

import           Control.Monad.Writer
import           Control.Monad.Reader
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Map as Map

import           HoSA.Data.MLTypes
import           HoSA.Data.Program
import           HoSA.Utils

data TSymbol f = TSymbol f Int -- auxiliary symbols f_i
             | TConstr f -- constructors
             | Tick -- tick constructor 
  deriving (Eq, Ord)

instance IsSymbol (TSymbol f) where
  isDefined TSymbol{} = True
  isDefined _         = False
  
data TVariable v = IdentV v | Fresh Int
  deriving (Eq, Ord)

type TickedExpression f v = TypedExpression (TSymbol f) (TVariable v)
type TickedEquation f v = TypedEquation (TSymbol f) (TVariable v)
type TickedProgram f v = Program (TSymbol f) (TVariable v)

type ArityDecl f = f -> Int

arity :: (IsSymbol f, Ord f) => Program f v -> ArityDecl f
arity p = \ f -> arities Map.! f where
  
  arities = Map.mapWithKey ar (signature p)
  
  ar f tp | isConstructor f = tarity tp
          | otherwise       = darity f
          
  darity f = maximum $ 0 : [ length args
                           | eq <- equations p
                           , let (Fun g _ _, args) = sexpr (lhs (eqEqn eq))
                           , f == g ]
             
----------------------------------------------------------------------
-- translation of simply typed terms
----------------------------------------------------------------------

clockType :: SimpleType
clockType = TyCon "#" []

tick :: TickedExpression f v -> TickedExpression f v
tick t = Apply clockType (Fun Tick (clockType :-> clockType) emptyLoc) t

-- ticking monad
type TickM f a = WriterT [(TSymbol f,SimpleType)] (ReaderT (Signature f) (UniqueT UniqueM)) a

runTick :: Signature f -> TickM f a -> (a, [(TSymbol f,SimpleType)])
runTick sig = runUnique . runUniqueT . flip runReaderT sig . runWriterT

freshLoc :: TickM f Location
freshLoc = lift unique

-- types
translatedType :: SimpleType -> SimpleType
translatedType (TyVar v)    = TyVar v
translatedType (TyCon n ts) = TyCon n (translatedType `map` ts)
translatedType (t1 :*: t2)  = translatedType t1 :*: translatedType t2
translatedType (t1 :-> t2)  = translatedType t1 :-> clockType :-> (translatedType t2 :*: clockType)

auxType :: SimpleType -> Int -> SimpleType
auxType tp 0            = clockType :-> (translatedType tp :*: clockType)
auxType (tp1 :-> tp2) i = translatedType tp1 :-> auxType tp2 (i - 1)
auxType _ _             = error "auxType not defined on given type"

constrType :: SimpleType -> SimpleType 
constrType (t1 :-> t2)  = translatedType t1 :-> constrType t2
constrType (TyCon n ts) = TyCon n ts
constrType  _           = error "auxType not defined on given type"

-- symbols and variables

freshVar :: TickM f (TVariable v)
freshVar = Fresh <$> uniqueToInt <$> unique

var :: v -> TVariable v
var = IdentV

resetFreshVar :: TickM f ()
resetFreshVar = reset

lookupType :: Ord f => f -> TickM f SimpleType
lookupType f = (Map.! f) <$> lift ask

auxFun :: Ord f => f -> Int -> TickM f (TickedExpression f v)
auxFun f i = do
  tp <- flip auxType i <$> lookupType f
  tell [(TSymbol f i,tp)]
  Fun (TSymbol f i) tp <$> freshLoc

constrSym :: Ord f => f -> TickM f (TSymbol f, SimpleType)
constrSym f = do
  tp <- constrType <$> lookupType f
  tell [(TConstr f,tp)]
  return (TConstr f,tp)

constrFun :: Ord f => f -> TickM f (TickedExpression f v)
constrFun f = do
  (f',tp') <- constrSym f
  Fun f' tp' <$> freshLoc

-- rules
translateLhs :: (Ord f, Eq v) => TypedExpression f v -> TickedExpression f v -> TickM f (TickedExpression f v)
translateLhs l t =  apply <$> renameHead l <*> return t where
  renameHead (sexpr -> (Fun f _ _,rest)) = foldl apply <$> h <*> r where
    h = auxFun f (length rest)
    r = mapExpressionM (\ g _  _ -> constrSym g) (\ v tp -> pure (var v,tp)) `mapM` rest
  renameHead _ = error "translateLhs: non-proper lhs given" 

translateRhs :: (Ord f, Eq v) => IsSymbol f => TypedExpression f v -> TickedExpression f v -> TickM f (TickedExpression f v)
translateRhs e time = translateK e time (\ e' t' -> return (e' `pair` tick t')) where
  translateK (Var v tp) t k = k (Var (var v) (translatedType tp)) t
  translateK (Fun f tp _) t k = do
    f0 <- auxFun f 0
    ve <- freshVar
    vc <- freshVar
    letp (apply f0 t) (ve,vc) <$> k (Var ve (translatedType tp)) (Var vc clockType)
  translateK (Pair _ e1 e2) t k = translateK e1 t k1 where
    k1 e1' t1 = translateK e2 t1 (k2 e1')
    k2 e1' e2' t2 = k (pair e1' e2') t2 --TODO
  translateK (Apply _ e1 e2) t k = translateK e1 t k1 where
    k1 e1' t1 = translateK e2 t1 (k2 e1')
    k2 e1' e2' t2 = do
      let (_ :-> tp2) = typeOf e1
      ve <- freshVar
      vc <- freshVar
      letp (apply (apply e1' e2') t2) (ve,vc) <$> k (Var ve (translatedType tp2)) (Var vc clockType)
  translateK (If _ eg et ee) t k = translateK eg t k1 where
    k1 eg' t1 = ite eg' <$> translateK et t1 k <*> translateK ee t1 k
  translateK _ _ _ = error "translateRhs: non-proper rhs given"
  
translateEnv :: Ord v => TVariable v -> Environment v -> Environment (TVariable v)
translateEnv t env = Map.insert t clockType $ Map.fromList [ (IdentV w, translatedType tp) | (w, tp) <- Map.toList env ]

translateEquation :: (Ord f, Ord v, IsSymbol f) => TypedEquation f v -> TickM f (TickedEquation f v)
translateEquation TypedEquation {..} = do
  resetFreshVar
  t <- freshVar
  l' <- translateLhs (lhs eqEqn) (Var t clockType)
  r' <- translateRhs (rhs eqEqn) (Var t clockType)
  return TypedEquation { eqEnv = translateEnv t eqEnv
                       , eqEqn = Equation l' r'
                       , eqTpe = translatedType eqTpe :*: clockType }

auxiliaryEquations :: (Ord f, IsSymbol f, Ord v) => ArityDecl f -> (f,SimpleType) -> TickM f [TickedEquation f v]
                                                                          
auxiliaryEquations ar (f,tpf) = mapM auxEquation [0 .. if isDefined f then arf - 1 else arf] where
    arf = ar f
    vars = walk 1 tpf where
    walk i (tp1 :-> tp2) = (Var (Fresh i) (translatedType tp1)) : walk (i+1) tp2
    walk _ _ = []

    auxEquation i = do
      fi <- auxFun f i
      fi' <- if i < arf then auxFun f (i + 1) else constrFun f
      let t = Var (Fresh (i+1)) clockType
          vs = take i vars
          fromSexp = foldl apply
          l = fromSexp fi (vs ++ [t])
          r = fromSexp fi' vs `pair` t
      return TypedEquation { eqEnv = Map.fromList [ (v,tpv) | Var v tpv <- t : vs ]
                           , eqEqn = Equation l r 
                           , eqTpe = typeOf l }

tickProgram :: (Ord v, IsSymbol f, Ord f) => Program f v -> (TickedProgram f v, TickedProgram f v)
tickProgram p = ( Program { equations = eqs, signature = Map.fromList fs, mainFns = [] } --TODO
                , Program { equations = aeqs, signature = Map.fromList afs, mainFns = [] })
  where
    sig = signature p
    (eqs,fs) = runTick sig $ translateEquation `mapM` equations p
    (aeqs,afs) = runTick sig $ auxiliaryEquations (arity p) `concatMapM` (Map.toList sig)
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
  pretty (TSymbol f i) = PP.bold (PP.pretty f) PP.<> PP.text "#" PP.<> PP.int i
  pretty (TConstr c) = PP.pretty c
  pretty Tick = PP.text "T"
  
instance PP.Pretty v => PP.Pretty (TVariable v) where
  pretty (IdentV v) = PP.pretty v
  pretty (Fresh u) = PP.text "v" PP.<> PP.int u
