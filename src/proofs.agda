open import Positive
open import CanonicalBinaryTrie using (Tree)
open import get 
open import set

open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
module proofs where
  {-get i empty = nothing               // gempty -}
  gempty : {A : Set} -> ∀ (p : Positive) -> get {A = A} p Tree.Empty ≡ nothing
  gempty p = refl
  
  {-get i (set i v m) = Some v          // gss (getSetSame) -}
  {-gss : {A : Set} -> ∀ (p : Positive) (t : Tree A) (v : A) → get p (set p v t) ≡ just v
  gss xH Tree.Empty v =
    begin 
      get xH (set xH v Tree.Empty)
    ≡⟨⟩
      get xH (Tree.Nodes (CanonicalBinaryTrie.Tree'.node010 v))
    ≡⟨⟩
      just v 
    ∎
  gss (xI p) t v = 
    begin 
      get (p q) (set (p q) v t)
    ≡⟨⟩
      get q (set q v t)
    ≡⟨⟩
      just v 
    ∎-}

  {-gss (xI p) Tree.Empty v =
    begin
      get (xI p) (set (xI p) v Tree.Empty)
    ≡⟨⟩
      get (xI p) (Tree.Nodes (set0 (xI p) v))
    ≡⟨⟩
      get' (xI p) (set0 (xI p) v)
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨⟩
      just v 
    ∎
  gss (xO p) Tree.Empty v =
    begin
      get (xO p) (set (xO p) v Tree.Empty)
    ≡⟨⟩
      get (xO p) (Tree.Nodes (set0 (xO p) v))
    ≡⟨⟩
      get' (xO p) (set0 (xO p) v)
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨⟩
      just v 
    ∎-}
  
  {-i != j get i (set j vm) = get i m   // gso (getSetOther)-}
  
  gso : {A : Set} -> ∀ (i j : Positive) (t : Tree A) (v : A) →  get i (set j v t) ≡ get i t 
  gso i j t v = {!   !}
