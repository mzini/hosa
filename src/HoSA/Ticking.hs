module HoSA.Ticking
  (tickATRS
  , ntickATRS
  , TSymbol
  , TVariable)
where

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (catMaybes)

import HoSA.Data.Rewriting
import HoSA.Data.SimpleType
import HoSA.Utils

data TSymbol = TSymbol String Int -- auxiliary symbols f_i
             | TConstr String -- constructors
             | Tick -- tick constructor 
  deriving (Eq, Ord)

data TVariable = IdentV Variable
               | Fresh Int
  deriving (Eq, Ord)

type TickedTerm = STTerm TSymbol TVariable
type TickedRule = STRule TSymbol TVariable
type TickedAtrs = STAtrs TSymbol TVariable

-- TODO: simplify? inlining, lets...
-- -- substCapturing :: (v -> Term f v) -> Term f v -> Term f v
-- -- substCapturing s (Var v) = s v
-- -- substCapturing _ (Fun f) = Fun f
-- -- substCapturing s (Apply e1 e2) = Apply (substCapturing s e1) (substCapturing s e2)
-- -- substCapturing s (Pair e1 e2) = Pair (substCapturing s e1) (substCapturing s e2)
-- -- substCapturing s (Let e1 vs e2) = Let (substCapturing s e1) vs (substCapturing s e2)

-- lett :: Eq v => TTerm f v -> (TVariable v, TVariable v) -> TTerm f v -> TTerm f v
-- lett (Pair e1 e2) (v1,v2) e
--   | inline e1 e && inline e2 e = substCapturing s e where
--       inline Fun {} _ = True
--       inline Var {} _ = True
--       s v | v == v1 = e1
--           | v == v2 = e2
--           | otherwise = Var v
-- lett e1 vs e2 = Let e1 vs e2

type ArityDecl = Symbol -> Int

arity :: STAtrs Symbol Variable -> ArityDecl
arity statrs = \ f -> arities M.! f where
  
  arities = M.fromList [ (f, ar f tp) | (f ::: tp) <- signatureToDecls (statrsSignature statrs) ]
  
  ar Constr{} tp = tarity tp -- ar c = n where c ::: t1 -> ... -> tn -> B
  ar f@Defined{} _ = darity f -- maximal arity in lhs
    
  darity f = maximum $ 0 : [ length args
                           | rl <- statrsRules statrs
                           , let (Fun g, args) = sexpr (lhs (strlUntypedRule rl))
                           , f == g ]
             
----------------------------------------------------------------------
-- translation of simply typed terms
----------------------------------------------------------------------

clockType :: SimpleType
clockType = TyBase Clock

tick :: TickedTerm -> TickedTerm
tick t = Fun (Tick ::: clockType :-> clockType) `Apply` t

-- ticking monad
type TickM a = UniqueM a

freshVar :: SimpleType -> TickM (TVariable ::: SimpleType)
freshVar tp = do
  v <- Fresh <$> uniqueToInt <$> unique
  return (v ::: tp)

-- types
translateType :: SimpleType -> SimpleType
translateType (TyBase b) = TyBase b
translateType (t1 :*: t2) = translateType t1 :*: translateType t2
translateType (t1 :-> t2) = translateType t1 :-> clockType :-> (translateType t2 :*: clockType)

-- symbols
var :: (Variable ::: SimpleType) -> (TVariable ::: SimpleType)
var (v ::: tp) = IdentV v ::: translateType tp

auxFun :: (Symbol ::: SimpleType) -> Int -> TickedTerm
auxFun (f ::: tp) i = Fun (TSymbol (symbolName f) i ::: auxType tp i) where
  auxType tp 0 = clockType :-> (translateType tp :*: clockType)
  auxType (tp1 :-> tp2) i = translateType tp1 :-> auxType tp2 (i - 1)

constrSym :: Symbol ::: SimpleType -> TSymbol ::: SimpleType
constrSym (f ::: tp) = TConstr (symbolName f) ::: tp

constrFun :: Symbol ::: SimpleType -> TickedTerm
constrFun f = Fun (constrSym f)

-- rules
translateLhs :: ArityDecl -> STTerm Symbol Variable -> TickedTerm -> TickM TickedTerm
translateLhs ar l t =  return (renameHead l `Apply` t) where
  renameHead (sexpr -> (Fun f,rest)) = fromSexpr hd' rest' where
    hd' = auxFun f (length rest)
    rest' = tmap constrSym var `map` rest

translateRhs :: ArityDecl -> STTerm Symbol Variable -> TickedTerm -> TickM TickedTerm
translateRhs ar e t = translateK e t (\ e' t' -> return (e' `Pair` tick t')) where
  translateK (Var v) t k = k (Var (var v)) t
  translateK (Fun f@(c@Constr{} ::: _)) t k | ar c == 0 = k (constrFun f) t
  translateK (Fun f) t k = k (auxFun f 1) t
  translateK (Apply e1 e2) t k = translateK e1 t k1 where
    k1 e1' t1 = translateK e2 t1 (k2 e1')
    k2 e1' e2' t2 = do
      let (tp1 :-> tp2) = typeOf e1
      e <- freshVar (translateType tp2)
      te <- freshVar clockType
      Let (Apply (Apply e1' e2') t2) (e,te) <$> k (Var e) (Var te)

translateEnv :: TVariable -> Environment Variable -> Environment TVariable
translateEnv t env = M.insert t clockType $ M.fromList [ (IdentV w, translateType tp) | (w, tp) <- M.toList env ]

translateRule :: ArityDecl -> STRule Symbol Variable -> TickedRule
translateRule ar STRule {..} = runUnique $ do
  t@(v:::_) <- freshVar clockType
  let Rule l r = strlTypedRule
  l' <- translateLhs ar l (Var t)
  r' <- translateRhs ar r (Var t)
  return STRule { strlEnv = translateEnv v strlEnv
                , strlUntypedRule = Rule (unType l') (unType r')
                , strlTypedRule = Rule l' r'
                , strlType = translateType strlType :*: clockType}

auxRules :: ArityDecl -> (Symbol ::: SimpleType) -> [TickedRule]
auxRules ar (f ::: tpf) = [ auxRule tpf i | i <- [1 .. if definedP f then arf - 1 else arf]] where
  arf = ar f
  vars = walk 1 tpf where
    walk i (tp1 :-> tp2) = (Fresh i ::: translateType tp1) : walk (i+1) tp2
    walk _ _ = []

  auxRule tp i = STRule { strlEnv = envFromDecls (vs ++ [t])
                        , strlUntypedRule = Rule (unType l) (unType r)
                        , strlTypedRule = Rule l r
                        , strlType = typeOf l }
    where
      vs = take i vars
      t = Fresh (i+1) ::: clockType
      l = fromSexpr (auxFun (f ::: tpf) i) [Var vi | vi <- vs ++ [t]]
      r = fromSexpr hd [Var vi | vi <- vs] `Pair` Var t where
        hd | i < arf = auxFun (f ::: tpf) (i + 1)
           | otherwise = constrFun (f ::: tpf)
  
tickATRS :: STAtrs Symbol Variable -> TickedAtrs
tickATRS statrs = STAtrs { statrsRules = rs
                         , statrsSignature = signatureFromDecls (funs rs) }
  where
    ar = arity statrs
    rs = translateRule ar `map` statrsRules statrs
         ++ auxRules ar `concatMap` signatureToDecls (statrsSignature statrs)

ntickATRS :: STAtrs Symbol Variable -> TickedAtrs
ntickATRS statrs = undefined
         
-- pretty printers
instance PP.Pretty TSymbol where
  pretty (TSymbol f i) = PP.pretty (Defined (f ++ "#" ++ show i))
  pretty (TConstr n) = PP.pretty (Constr n)
  pretty Tick = PP.text "T"
  
instance PP.Pretty TVariable where
  pretty (IdentV v) = PP.pretty v
  pretty (Fresh u) = PP.text "v" PP.<> PP.int u
