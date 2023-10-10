open import Data.Maybe
open import Data.Bool
open import Positive
open import CanonicalBinaryTrie

module get where 


    {- Get Version1 -}
    get' : {A : Set} -> Positive -> Tree' A -> Maybe A 
    get' xH (node001 _ ) = nothing
    get' xH (node010 v ) = just v 
    get' xH (node011 v _ ) = just v
    get' xH (node100 _ ) = nothing
    get' xH (node101 _ _ ) = nothing
    get' xH (node110 _ v) = just v 
    get' xH (node111 _ v _) = just v

    get' (xO q) (node001 _ )= nothing
    get' (xO q) (node010 _ )= nothing 
    get' (xO q) (node011 _ _ )= nothing
    get' (xO q) (node100 l )= get' q l
    get' (xO q) (node101 l _ )=  get' q l
    get' (xO q) (node110 l _ )= get' q l
    get' (xO q) (node111 l _ _ )= get' q l

    get' (xI q) (node001 r )= get' q r
    get' (xI q) (node010 _ )= nothing 
    get' (xI q) (node011 _ r )= get' q r
    get' (xI q) (node100 r )= nothing
    get' (xI q) (node101 _ r )=  get' q r
    get' (xI q) (node110 _ _ )= nothing
    get' (xI q) (node111 _ _ r )= get' q r


    get : {A : Set} -> Positive -> Tree A -> Maybe A
    get _ Empty = nothing
    get p (Nodes n) = get' p n
