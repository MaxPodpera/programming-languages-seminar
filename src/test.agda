{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Data.Maybe
open import IO
open import CanonicalBinaryTrie
open import Positive
open import get
open import set
open import mapFilter
open import Data.Bool
open import Data.List

exampleTrie : Tree Nat
exampleTrie = 
    let 
        trie1 = set1 one 1 Empty
        trie2 = set1 three 3 trie1
        trie3 = set1 thirteen 13 trie2
        trie4 = set1 four 4 trie3
        trie5 = set1 eleven 11 trie4
        trie6 = set1 five 5 trie5
        trie7 = set1 fourteen 14 trie5
    in
        trie7

toNat : Maybe Nat -> Nat 
toNat nothing = 0
toNat (just a) = a 

testPattern : List Positive -> List Nat
testPattern [] = []
testPattern (x ∷ xs) = ((toNat (get1 x exampleTrie)) ∷ []) ++ (testPattern xs)

postitiveList : List Positive
postitiveList = one ∷ two ∷ three ∷ four ∷ five ∷ six ∷ seven ∷ eight ∷ nine ∷ ten ∷ eleven ∷ twelve ∷ thirteen ∷ fourteen ∷ fifteen ∷ []


{- C-c c-l .... C-c C-n -}
{- 1 ∷ 0 ∷ 3 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 11 ∷ 0 ∷ 13 ∷ 14 ∷ 0 ∷ [] -}
testGet : List Nat
testGet = testPattern postitiveList
