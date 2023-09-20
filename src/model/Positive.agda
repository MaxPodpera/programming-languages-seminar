module Positive where
    data Positive : Set where 
        xH : Positive
        xI : Positive -> Positive
        xO : Positive -> Positive