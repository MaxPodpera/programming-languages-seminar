open import Data.Maybe
open import CanonicalBinaryTrie


mapFilterI : {A B : Set} -> (A -> Maybe B) -> Tree_I A -> Tree B
mapFilterI f (node001 r) = node Empty nothing (mapFilterI f r)
mapFilterI f (node010 v) = node Empty (f v) Empty
mapFilterI f (node011 v r) = node Empty (f v) (mapFilterI f r)
mapFilterI f (node100 l) = node (mapFilterI f l) nothing Empty
mapFilterI f (node101 l r) = node (mapFilterI f l) nothing (mapFilterI f r)
mapFilterI f (node110 l v) = node (mapFilterI f l) (f v) Empty
mapFilterI f (node111 l v r) = node (mapFilterI f l) (f v) (mapFilterI f r)

{-I added this for practicality -}
mapFilter : {A B : Set} -> (A -> Maybe B) -> Tree A -> Tree B 
mapFilter f Empty = Empty
mapFilter f (Nodes t) = mapFilterI f t 

