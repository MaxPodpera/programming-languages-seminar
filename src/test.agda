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
        trie7 = set1 fourteen 14 trie6
    in
        trie7

toNat : Maybe Nat -> Nat 
toNat nothing = 0
toNat (just a) = a 

testPattern : List Positive -> Tree Nat -> List Nat
testPattern [] trie = []
testPattern (x ∷ xs) trie = ((toNat (get1 x trie)) ∷ []) ++ (testPattern xs trie)

square : Nat -> Maybe Nat
square n = just ( n * n )

mappedTrie : Tree  Nat
mappedTrie = mapFilter square exampleTrie
{- Helper -}

postitiveList : List Positive
postitiveList = one ∷ two ∷ three ∷ four ∷ five ∷ six ∷ seven ∷ eight ∷ nine ∷ ten ∷ eleven ∷ twelve ∷ thirteen ∷ fourteen ∷ fifteen ∷ []

{- C-c c-l .... C-c C-n -}
{- 1 ∷ 0 ∷ 3 ∷ 4 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 11 ∷ 0 ∷ 13 ∷ 14 ∷ 0 ∷ [] -}
testGet : List Nat
testGet = testPattern postitiveList exampleTrie

{- 1 ∷ 0 ∷ 9 ∷ 16 ∷ 25 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 121 ∷ 0 ∷ 169 ∷ 196 ∷ 0 ∷ [] -}
testMap : List Nat 
testMap = testPattern postitiveList mappedTrie