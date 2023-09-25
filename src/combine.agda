open import Data.Maybe
open import CanonicalBinaryTrie 


{- TODO: Dont know how to implement this. -}
combine_by_tac : {A B C: Set} -> (A -> B -> C) -> Tree_I A -> Tree_I B -> Tree C
combine_by_tac _ _ _ = Empty 