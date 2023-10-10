open import Data.Maybe
open import CanonicalBinaryTrie


mapFilter' : {A B : Set} -> (A -> Maybe B) -> Tree' A -> Tree B
mapFilter' f (node001 r) = node Empty nothing (mapFilter' f r)
mapFilter' f (node010 v) = node Empty (f v) Empty
mapFilter' f (node011 v r) = node Empty (f v) (mapFilter' f r)
mapFilter' f (node100 l) = node (mapFilter' f l) nothing Empty
mapFilter' f (node101 l r) = node (mapFilter' f l) nothing (mapFilter' f r)
mapFilter' f (node110 l v) = node (mapFilter' f l) (f v) Empty
mapFilter' f (node111 l v r) = node (mapFilter' f l) (f v) (mapFilter' f r)

{-I added this for practicality -}
mapFilter : {A B : Set} -> (A -> Maybe B) -> Tree A -> Tree B 
mapFilter f Empty = Empty
mapFilter f (Nodes t) = mapFilter' f t 

