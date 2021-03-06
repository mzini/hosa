module HoSA.Data.Program.Pretty
  (
    prettyExpression
  , prettyEquation
  , prettyProgram
  ) where

import Data.List (partition, sortBy)
import qualified Data.Map as Map
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import HoSA.Utils (uniqueToInt,(//))
import HoSA.Data.MLTypes
import HoSA.Data.Program.CallSite
import HoSA.Data.Program.Equation
import HoSA.Data.Program.Expression (funs)
import HoSA.Data.Program.Types


----------------------------------------------------------------------
-- Utils
----------------------------------------------------------------------

ppTuple :: (PP.Pretty a, PP.Pretty b) => (a,b) -> PP.Doc
ppTuple (a,b) = PP.tupled [ PP.pretty a, PP.pretty b]

----------------------------------------------------------------------
-- Symbols
----------------------------------------------------------------------

instance PP.Pretty Symbol where
  pretty f | defined f = PP.bold (PP.text (symName f))
           | otherwise = PP.text (symName f)
                         
instance PP.Pretty Variable where
  pretty = PP.text . varName

instance PP.Pretty f => PP.Pretty (CtxSymbol f) where
  pretty (CtxSym f u Nothing) | uniqueToInt u == 0 = PP.pretty f
  pretty f = PP.pretty (csSymbol f) PP.<> PP.text "@" PP.<> loc where
    loc = PP.hcat $ PP.punctuate (PP.text ".") (ppLoc `map` locations f)
    ppLoc = PP.int . uniqueToInt

prettyExpression :: Bool -> (f -> PP.Doc) -> (v -> PP.Doc) -> Expression f v tp -> PP.Doc
prettyExpression showLabel ppFun ppVar = pp id where
  pp _ (Var v _) = ppVar v
  pp _ (Fun f _ l)
    | showLabel = ppFun f PP.<> PP.text "@" PP.<> PP.int (uniqueToInt l)
    | otherwise = ppFun f 
  pp _ (Pair _ t1 t2) = ppTuple (pp id t1, pp id t2)
  pp par (Apply _ t1 t2) =
    par (pp id t1 PP.</> pp PP.parens t2)
  pp par (If _ tg tt te) =
    par (PP.text "if" PP.<+> pp id tg
         // PP.hang 2 (PP.text "then" PP.<+> pp id tt)
         // PP.hang 2 (PP.text "else" PP.<+> pp id te))
  pp par (LetP _ t1 ((x,_),(y,_)) t2) =
    par (PP.align (PP.text "let" PP.<+> ppTuple (ppVar x, ppVar y)
                   PP.<+> PP.text "=" PP.<+> pp id t1
                   PP.<$> PP.hang 3 (PP.text "in" PP.<+> pp id t2)))

prettyEquation :: (f -> PP.Doc) -> (v -> PP.Doc) -> Equation f v tp -> PP.Doc
prettyEquation ppFun ppVar eqn = pp False (lhs eqn) PP.<+> PP.text "=" PP.</> ppDist (rhs eqn) where
  pp showLabel = prettyExpression showLabel ppFun ppVar
  ppDist (Distribution _ [(1,r)]) = pp False r
  ppDist (Distribution d ls) =
    PP.encloseSep (PP.text "{") (PP.text "}") (PP.text ";")
    [ppRatio d p PP.<+> PP.text ":" PP.<+> pp False r | (p,r) <- ls ]
  ppRatio d p = PP.int p PP.<> PP.text "/" PP.<> PP.int d


instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Expression f v tp) where
  pretty = prettyExpression True PP.pretty PP.pretty
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (Equation f v tp) where
  pretty = prettyEquation PP.pretty PP.pretty
instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypedEquation f v) where
  pretty TypedEquation{..} =
    PP.group (PP.pretty eqEnv)
    PP.<+> PP.text "⊦"
    PP.</> PP.group (prettyEquation PP.pretty PP.pretty eqEqn
                     PP.<+> PP.text ":"
                     PP.</> PP.pretty eqTpe)

prettyProgram :: (IsSymbol f, Eq f, PP.Pretty f, PP.Pretty v, PP.Pretty d) => Program f v -> Map.Map f d -> PP.Doc
prettyProgram Program{..} sig = 
    PP.vcat [ ppDecl d tp
              PP.<$> PP.vcat (PP.pretty `map` eqs)
              PP.<$> PP.empty
            | (d,tp) <- sortBy occurrence ds
            , let eqs = [eq | eq <- untypedEquations, fst (definedSymbol eq) == d]
            , not (null eqs)]
    PP.<$> PP.text "where"
    PP.<$> PP.indent 2 (PP.vcat [ppDecl c tp | (c,tp) <- cs, c `elem` fs])
    -- PP.<$> if null mainFns
    --         then PP.empty
    --         else PP.text ""
    --              PP.<$> (PP.text "main function(s):"
    --                      // PP.hang 2 (PP.hcat (PP.punctuate (PP.text ",") [PP.pretty f | f <- mainFns])))
    where
      ppDecl f tp = PP.pretty f PP.<+> PP.text "::" PP.<+> PP.pretty tp
      occurrence (d1,_) (d2,_) = walk untypedEquations where
        walk [] = EQ
        walk (eq:eqs)
          | fst (definedSymbol eq) == d1 = GT
          | fst (definedSymbol eq) == d2 = LT
          | otherwise = walk eqs
      untypedEquations = eqEqn `map` equations
      fs = concatMap (\ e -> funs (lhs e) ++ concatMap funs (rhss e)) untypedEquations
      (ds,cs) = partition (isDefined . fst) (Map.toList sig)
      
  
instance (IsSymbol f, Eq f, PP.Pretty f, PP.Pretty v) => PP.Pretty (Program f v) where
  pretty p = prettyProgram p (Map.map ren (signature p)) where
    ren tp = rename (fvs tp) tp

instance (PP.Pretty f, PP.Pretty v) => PP.Pretty (TypingError f v) where
  pretty (IncompatibleType rl t has expected) =
          PP.text "Typing error in rule:"
          PP.<$> PP.indent 2 (PP.pretty rl)
          PP.<$> PP.text "The term" PP.<+> PP.pretty t
          PP.<+> PP.text "has type"
          PP.<+> PP.squotes (PP.pretty has)
          PP.<> PP.text ", but" PP.<+> PP.squotes (PP.pretty expected) PP.<+> PP.text "is expected."
  pretty (IllformedConstructorType c tp) =
    PP.text "Illformed Constructor type for constructor" PP.<+> PP.squotes (PP.pretty c)
    PP.<$> PP.indent 2 (PP.pretty tp)      
  pretty (LetPInLHS rl) =
    PP.text "LetP in lhs encountered:"
    PP.<$> PP.indent 2 (PP.pretty rl)    
  pretty (VariableUndefined rl v) =
    PP.text "Variable" PP.<+> PP.squotes (PP.pretty v) PP.<+> PP.text "undefined:"
    PP.<$> PP.indent 2 (PP.pretty rl)  
  pretty (ConstructorMissingSignature f) =
    PP.text "The constructor" PP.<+> PP.squotes (PP.pretty f) PP.<+> PP.text "misses a type declaration."
