open import Data.Maybe
open import Positive


module CanonicalBinaryTrie where 
    
    {- Canonical Binary Tries -}
    data Tree_I (A : Set) : Set where 
        node001 : Tree_I A -> Tree_I A
        node010 : A -> Tree_I A
        node011 : A -> Tree_I A -> Tree_I A 
        node100 : Tree_I A -> Tree_I A 
        node101 : Tree_I A -> Tree_I A -> Tree_I A
        node110 : Tree_I A -> A -> Tree_I A 
        node111 : Tree_I A -> A -> Tree_I A -> Tree_I A

    data Tree (A : Set) : Set where 
        Empty : Tree A
        Nodes : Tree_I A -> Tree A 

    node : {A : Set} -> Tree A -> Maybe A -> Tree A -> Tree A 
    node Empty nothing Empty = Empty
    node Empty nothing (Nodes r) = Nodes (node001 r)
    node Empty (just v) Empty = Nodes (node010 v)
    node Empty (just v) (Nodes r) = Nodes (node011 v r)
    node (Nodes l) nothing Empty = Nodes (node100 l)
    node (Nodes l) nothing (Nodes r) = Nodes (node101 l r)
    node (Nodes l) (just v) Empty = Nodes (node110 l v)
    node (Nodes l) (just v) (Nodes r) = Nodes (node111 l v r)


