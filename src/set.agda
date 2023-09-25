open import Data.Maybe

open import Positive
open import CanonicalBinaryTrie

module set where 
    {- Set Version1 -}
    set0 : {A : Set} -> Positive -> A -> Tree_I A
    set0 xH v = node010 v 
    set0 (xI q) v = node001 (set0 q v)
    set0 (xO q) v = node100 (set0 q v)

    set_ : {A : Set} -> Positive -> A -> Tree_I A -> Tree_I A
    set_ xH v (node001 r )= node011 v r 
    set_ xH v (node010 _ )= node010 v 
    set_ xH v (node011 _ r )= node011 v r 
    set_ xH v (node100 l )= node110 l v
    set_ xH v (node101 l r )= node111 l v r 
    set_ xH v (node110 l _ )= node110 l v  
    set_ xH v (node111 l _ r )= node111 l v r 

    set_ (xO q) v (node001 r )= node101 (set0 q v) r 
    set_ (xO q) v (node010 v1 )= node110 (set0 q v) v1
    set_ (xO q) v (node011 v1 r )= node111 (set0 q v) v1 r
    set_ (xO q) v (node100 l )= node100 (set_ q v l)
    set_ (xO q) v (node101 l r )= node101 (set_ q v l) r
    set_ (xO q) v (node110 l v1 )= node110 (set_ q v l) v1 
    set_ (xO q) v (node111 l v1 r )= node111 (set_ q v l) v1 r

    set_ (xI q) v (node001 r )= node001 (set_ q v r)
    set_ (xI q) v (node010 v1 )= node011 v1 (set0 q v)
    set_ (xI q) v (node011 v1 r )= node011 v1 (set_ q v r)
    set_ (xI q) v (node100 l )= node101 l (set0 q v)
    set_ (xI q) v (node101 l r )= node101 l (set_ q v r)
    set_ (xI q) v (node110 l v1 )= node111 l v1 (set0 q v)
    set_ (xI q) v (node111 l v1 r )= node111 l v1 (set_ q v r)

    set1 : {A : Set} -> Positive -> A -> Tree A -> Tree A
    set1 p v Empty = Nodes (set0 p v)
    set1 p v (Nodes m) = Nodes (set_ p v m)
