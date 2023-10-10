open import Data.Maybe

open import Positive
open import CanonicalBinaryTrie

module set where 

    set0 : {A : Set} -> Positive -> A -> Tree' A
    set0 xH v = node010 v 
    set0 (xO q) v = node100 (set0 q v)
    set0 (xI q) v = node001 (set0 q v)


    set' : {A : Set} -> Positive -> A -> Tree' A -> Tree' A
    set' xH v (node001 r )= node011 v r 
    set' xH v (node010 _ )= node010 v 
    set' xH v (node011 _ r )= node011 v r 
    set' xH v (node100 l )= node110 l v
    set' xH v (node101 l r )= node111 l v r 
    set' xH v (node110 l _ )= node110 l v  
    set' xH v (node111 l _ r )= node111 l v r 

    set' (xO q) v (node001 r )= node101 (set0 q v) r 
    set' (xO q) v (node010 v1 )= node110 (set0 q v) v1
    set' (xO q) v (node011 v1 r )= node111 (set0 q v) v1 r
    set' (xO q) v (node100 l )= node100 (set' q v l)
    set' (xO q) v (node101 l r )= node101 (set' q v l) r
    set' (xO q) v (node110 l v1 )= node110 (set' q v l) v1 
    set' (xO q) v (node111 l v1 r )= node111 (set' q v l) v1 r

    set' (xI q) v (node001 r )= node001 (set' q v r)
    set' (xI q) v (node010 v1 )= node011 v1 (set0 q v)
    set' (xI q) v (node011 v1 r )= node011 v1 (set' q v r)
    set' (xI q) v (node100 l )= node101 l (set0 q v)
    set' (xI q) v (node101 l r )= node101 l (set' q v r)
    set' (xI q) v (node110 l v1 )= node111 l v1 (set0 q v)
    set' (xI q) v (node111 l v1 r )= node111 l v1 (set' q v r)

    set : {A : Set} -> Positive -> A -> Tree A -> Tree A
    set p v Empty = Nodes (set0 p v)
    set p v (Nodes m) = Nodes (set' p v m)
