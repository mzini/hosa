module HoSA.Data.Program.Equation
  (
    definedSymbol
  , rhss
  )
where

import Data.Maybe (fromJust)

import HoSA.Data.MLTypes
import HoSA.Data.Program.Types
import HoSA.Data.Program.Expression

----------------------------------------------------------------------
-- ops
----------------------------------------------------------------------

definedSymbol :: Equation f v tp -> (f,tp)
definedSymbol = fromJust . headSymbol . lhs

rhss :: Equation f v tp -> [Expression f v tp]
rhss (rhs -> Distribution _ l) = map snd l
                           

----------------------------------------------------------------------
-- substitutions
----------------------------------------------------------------------

instance Eq v => TSubstitutable (Equation f v SimpleType) where
  substitute s (Equation lhs rhs) = Equation  (substitute s lhs) (substitute s rhs)

instance Eq v => TSubstitutable (TypedEquation f v) where
  substitute s (TypedEquation env eq tpe) = TypedEquation (substitute s env) (substitute s eq) (substitute s tpe)
