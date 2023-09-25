open import Data.List
open import Agda.Builtin.Nat


square : List Nat -> List Nat
square [] = []
square ( x ∷ xs ) = ((x * x) ∷ []) ++ ( square xs )


