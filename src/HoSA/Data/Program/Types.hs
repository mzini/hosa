module HoSA.Data.Program.Types
  (
    -- * Symbols
    Symbol (..)
  , pattern NIL
  , pattern CONS
  , Variable (..)
  , IsSymbol (..)
  , isConstructor
    -- * Expression
  , Location
  , Expression (..)
  , Equation (..)
  , UntypedExpression
  , TypedExpression
    -- * Equation  
  , UntypedEquation
  , TypedEquation (..)
    -- * Programs
  , Program (..)
    -- * Type Inference
  , TypingError (..)
  )
where

import           HoSA.Utils
import           HoSA.Data.MLTypes

----------------------------------------------------------------------
-- Symbols
----------------------------------------------------------------------

data Symbol = Symbol { symName :: String, defined :: Bool }
  deriving (Eq, Ord, Show)

newtype Variable = Variable { varName :: String }
  deriving (Eq, Ord, Show)

class IsSymbol f where
  isDefined :: f -> Bool

instance IsSymbol Symbol where
  isDefined = defined

isConstructor :: IsSymbol f => f -> Bool
isConstructor = not . isDefined

pattern NIL = Symbol "[]" False
pattern CONS = Symbol "(:)" False

----------------------------------------------------------------------
-- Expressions
----------------------------------------------------------------------

type Location = Unique

data Expression f v tp =
  Var v tp
  | Pair (tp,tp) (Expression f v tp) (Expression f v tp)
  | Fun f tp Location
  | Apply tp (Expression f v tp) (Expression f v tp)
  | LetP tp (Expression f v tp) ((v,tp),(v,tp)) (Expression f v tp)  

data Equation f v tp = Equation { lhs :: Expression f v tp, rhs :: Expression f v tp }

type UntypedExpression f v = Expression f v ()
type UntypedEquation f v = Equation f v ()
type TypedExpression f v = Expression f v SimpleType

----------------------------------------------------------------------
-- Programs
----------------------------------------------------------------------

data TypedEquation f v = TypedEquation { eqEnv :: Environment v
                                       , eqEqn :: Equation f v SimpleType
                                       , eqTpe :: SimpleType }
                  
data Program f v = Program { equations :: [TypedEquation f v]
                           , signature :: Signature f }

----------------------------------------------------------------------
-- Type Inference
----------------------------------------------------------------------

data TypingError f v =
  IncompatibleType (UntypedEquation f v) (UntypedExpression f v) SimpleType SimpleType
  | LetPInLHS (UntypedEquation f v)
  | IllformedConstructorType f SimpleType
  | VariableUndefined (UntypedEquation f v) v
  | ConstructorMissingSignature f
    
