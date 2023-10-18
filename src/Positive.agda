open import Data.Bool

module Positive where
    data Positive : Set where 
        xH : Positive
        xI : Positive -> Positive
        xO : Positive -> Positive

    one : Positive
    one = xH

    two : Positive
    two = xO xH

    three : Positive 
    three = xI xH

    four : Positive
    four = xO (xO xH)

    five : Positive
    five = xI (xO xH)

    six : Positive
    six = xO (xI xH)

    seven : Positive
    seven = xI (xI xH)

    eight : Positive
    eight = xO (xO (xO xH))

    nine : Positive
    nine = xI (xO (xO xH))

    ten : Positive
    ten = xO (xI (xO xH))

    eleven : Positive
    eleven = xI (xI (xO xH))

    twelve : Positive
    twelve = xO (xO (xI xH))

    thirteen : Positive
    thirteen = xI (xO (xI xH))

    fourteen : Positive
    fourteen = xO (xI (xI xH))

    fifteen : Positive
    fifteen = xI (xI (xI xH))