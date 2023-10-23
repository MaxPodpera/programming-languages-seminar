open import Positive
open import CanonicalBinaryTrie
open import get 
open import set

open import Data.Maybe

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; _≢_)
open import Data.Empty
open Eq.≡-Reasoning
open import Agda.Builtin.Bool

module proofs where

  proof-2 : {A : Set} → ∀ (p : Positive) (v : A) → get' p (set0 p v) ≡ just v
  proof-2 xH v = refl
  proof-2 (xI p) v = proof-2 p v
  proof-2 (xO p) v = proof-2 p v
  
  proof-1 : {A : Set} → ∀ (p : Positive) (v : A) (t : Tree' A) → get' p (set' p v t) ≡ just v 
  proof-1 xH v (node001 t) = refl
  proof-1 xH v (node010 x) = refl
  proof-1 xH v (node011 x t) = refl
  proof-1 xH v (node100 t) = refl
  proof-1 xH v (node101 t t₁) = refl
  proof-1 xH v (node110 t x) = refl
  proof-1 xH v (node111 t x t₁) = refl
  proof-1 (xI p) v (node001 t) = proof-1 p v t
  proof-1 (xI p) v (node010 x) = 
    begin 
      get' (xI p) (set' (xI p) v (node010 x))
    ≡⟨⟩
      get' (xI p) (node011 x (set0 p v))
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xI p) v (node011 x t) = proof-1 p v t
  proof-1 (xI p) v (node100 t) =
    begin 
      get' (xI p) (set' (xI p) v (node100 t))
    ≡⟨⟩
      get' (xI p) (node101 t (set0 p v))
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xI p) v (node101 t t₁) = proof-1 p v t₁
  proof-1 (xI p) v (node110 t x) =
    begin 
      get' (xI p) (set' (xI p) v (node110 t x))
    ≡⟨⟩
      get' (xI p) (node111 t x (set0 p v))
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xI p) v (node111 t x t₁) = proof-1 p v t₁
  proof-1 (xO p) v (node001 t) = 
    begin 
      get' (xO p) (set' (xO p) v (node001 t))
    ≡⟨⟩
      get' (xO p) (node101 (set0 p v) t)
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xO p) v (node010 x) = 
    begin 
      get' (xO p) (set' (xO p) v (node010 x))
    ≡⟨⟩
      get' (xO p) (node110 (set0 p v) x)
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xO p) v (node011 x t) =
    begin 
      get' (xO p) (set' (xO p) v (node011 x t))
    ≡⟨⟩
      get' (xO p) (node111 (set0 p v) x t)
    ≡⟨⟩
      get' p (set0 p v)
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  proof-1 (xO p) v (node100 t) = proof-1 p v t
  proof-1 (xO p) v (node101 t t₁) = proof-1 p v t
  proof-1 (xO p) v (node110 t x) = proof-1 p v t
  proof-1 (xO p) v (node111 t x t₁) = proof-1 p v t

  {-get i empty = nothing               // gempty -}
  gempty : {A : Set} → ∀ (p : Positive) → get {A = A} p Empty ≡ nothing
  gempty p = refl

  {--}
  gss : {A : Set} -> ∀ (p : Positive) (t : Tree A) (v : A) → get p (set {A = A} p v t) ≡ just v
  -- xH
  gss xH Empty v = refl
  gss xH (Nodes (node001 x)) v = refl
  gss xH (Nodes (node010 x)) v = refl
  gss xH (Nodes (node011 x x₁)) v = refl
  gss xH (Nodes (node100 x)) v = refl
  gss xH (Nodes (node101 x x₁)) v = refl
  gss xH (Nodes (node110 x x₁)) v = refl
  gss xH (Nodes (node111 x x₁ x₂)) v = refl
  -- xI
  gss (xI p) Empty v = 
    begin
      get (xI p) (set (xI p) v Empty)
    ≡⟨⟩
      get (xI p) (Nodes (set0 (xI p) v))
    ≡⟨⟩
      get (xI p) (Nodes (node001 (set0 p v)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node001 t)) v = 
    begin
      get (xI p) (set (xI p) v (Nodes (node001 t)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node001 t)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node010 x)) v =
    begin
      get (xI p) (set (xI p) v (Nodes (node010 x)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node010 x)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node011 x t)) v =
    begin
      get (xI p) (set (xI p) v (Nodes (node011 x t)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node011 x t)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node100 t)) v = 
    begin
      get (xI p) (set (xI p) v (Nodes (node100 t)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node100 t)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node101 t t₁)) v = 
    begin
      get (xI p) (set (xI p) v (Nodes (node101 t t₁)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node101 t t₁)))
    ≡⟨⟩
      get p (Nodes (set' p v t₁))
    ≡⟨ proof-1 p v t₁ ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node110 t x)) v = 
    begin
      get (xI p) (set (xI p) v (Nodes (node110 t x)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node110 t x)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xI p) (Nodes (node111 t x t₁)) v =
    begin
      get (xI p) (set (xI p) v (Nodes (node111 t x t₁)))
    ≡⟨⟩
      get (xI p) (Nodes (set' (xI p) v (node111 t x t₁)))
    ≡⟨⟩
      get p (Nodes (set' p v t₁))
    ≡⟨ proof-1 p v t₁ ⟩
      just v 
    ∎
  -- xO 
  gss (xO p) Empty v = 
    begin
      get (xO p) (set (xO p) v Empty)
    ≡⟨⟩
      get (xO p) (Nodes (set0 (xO p) v))
    ≡⟨⟩
      get (xO p) (Nodes (node100 (set0 p v)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node001 t)) v = 
    begin
      get (xO p) (set (xO p) v (Nodes (node001 t)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node001 t)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node010 x)) v = 
    begin
      get (xO p) (set (xO p) v (Nodes (node010 x)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node010 x)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node011 x t)) v =
    begin
      get (xO p) (set (xO p) v (Nodes (node011 x t)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node011 x t)))
    ≡⟨⟩
      get p (Nodes (set0 p v))
    ≡⟨ proof-2 p v ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node100 t)) v =
    begin
      get (xO p) (set (xO p) v (Nodes (node100 t)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node100 t)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node101 t t₁)) v =
    begin
      get (xO p) (set (xO p) v (Nodes (node101 t t₁)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node101 t t₁)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node110 t x)) v = 
    begin
      get (xO p) (set (xO p) v (Nodes (node110 t x)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node110 t x)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎
  gss (xO p) (Nodes (node111 t x t₁)) v =
    begin
      get (xO p) (set (xO p) v (Nodes (node111 t x t₁)))
    ≡⟨⟩
      get (xO p) (Nodes (set' (xO p) v (node111 t x t₁)))
    ≡⟨⟩
      get p (Nodes (set' p v t))
    ≡⟨ proof-1 p v t ⟩
      just v 
    ∎

  {-i != j get i (set j vm) = get i m   // gso (getSetOther)-}
  gso : {A : Set} -> ∀ (i j : Positive) (t : Tree A) (v : A) → ((i ≡ j) → ⊥) → get i (set j v t) ≡ get i t
  gso xH xH t v neq = ⊥-elim (neq refl)
  -- -----------------------
  gso xH (xI q) Empty v = λ _ → refl
  gso xH (xI q) (Nodes (node001 x)) v = λ _ → refl
  gso xH (xI q) (Nodes (node010 x)) v = λ _ → refl
  gso xH (xI q) (Nodes (node011 x x₁)) v = λ _ → refl
  gso xH (xI q) (Nodes (node100 x)) v = λ _ → refl
  gso xH (xI q) (Nodes (node101 x x₁)) v = λ _ → refl
  gso xH (xI q) (Nodes (node110 x x₁)) v = λ _ → refl
  gso xH (xI q) (Nodes (node111 x x₁ x₂)) v = λ _ → refl 
  -- -----------------------
  gso xH (xO q) Empty v = λ _ → refl
  gso xH (xO q) (Nodes (node001 x)) v = λ _ → refl
  gso xH (xO q) (Nodes (node010 x)) v = λ _ → refl
  gso xH (xO q) (Nodes (node011 x x₁)) v = λ _ → refl
  gso xH (xO q) (Nodes (node100 x)) v = λ _ → refl
  gso xH (xO q) (Nodes (node101 x x₁)) v = λ _ → refl
  gso xH (xO q) (Nodes (node110 x x₁)) v = λ _ → refl
  gso xH (xO q) (Nodes (node111 x x₁ x₂)) v = λ _ → refl
  -- -----------------------  
  gso (xI p) xH Empty v = λ _ → refl
  gso (xI p) xH (Nodes (node001 x)) v = λ _ → refl
  gso (xI p) xH (Nodes (node010 x)) v = λ _ → refl
  gso (xI p) xH (Nodes (node011 x x₁)) v = λ _ → refl
  gso (xI p) xH (Nodes (node100 x)) v = λ _ → refl
  gso (xI p) xH (Nodes (node101 x x₁)) v = λ _ → refl
  gso (xI p) xH (Nodes (node110 x x₁)) v = λ _ → refl
  gso (xI p) xH (Nodes (node111 x x₁ x₂)) v = λ _ → refl
  -- -----------------------
  gso (xI p) (xI q) Empty v neq =
    {-begin 
      get (xI p) (set (xI q) v Empty)
    ≡⟨ cong (p ≡ q) (neq) ⟩
      get p (set q v Empty)
    ≡⟨ gso p q Empty v ⟩
      get p Empty 
    ≡⟨⟩
      nothing
    ∎ -}
    begin
      get (xI p) (set (xI q) v Empty)
    ≡⟨⟩
      get (xI p) (Nodes (node001 (set0 q v)))
    ≡⟨ gso (xI p) (xI q) (Nodes (node001 (set0 q v))) ⟩
      nothing
    ∎ 








  ------------------------
  {-
  gso (xI p) (xI q) (Nodes (node001 t)) v neq = 
    begin 
      get (xI p) (set (xI q) v (Nodes (node001 t)))
    ≡⟨⟩
      get (xI p) (Nodes (node001 (set' q v t)))
    ≡⟨ cong (xI q) (Nodes (node001 (set' q v t ))) ⟩
      get p (Nodes (set' q v t))
    ≡⟨ refl ⟩
      gso p q (Nodes (set' q v t)) v 
      get (xI p) (Nodes (node001 (set' q v t )))
    ∎ -}
  gso (xI p) (xI q) (Nodes (node010 x)) v = {!   !}
  gso (xI p) (xI q) (Nodes (node011 x x₁)) v = {!   !}
  gso (xI p) (xI q) (Nodes (node100 x)) v = {!   !}
  gso (xI p) (xI q) (Nodes (node101 x x₁)) v = {!   !}
  gso (xI p) (xI q) (Nodes (node110 x x₁)) v = {!   !}
  gso (xI p) (xI q) (Nodes (node111 x x₁ x₂)) v = {!   !}
  -- -----------------------
  gso (xI p) (xO q) Empty v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node001 x)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node010 x)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node011 x x₁)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node100 x)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node101 x x₁)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node110 x x₁)) v = λ _ → refl
  gso (xI p) (xO q) (Nodes (node111 x x₁ x₂)) v = λ _ → refl
  -- -----------------------
  gso (xO p) xH Empty v = λ _ → refl
  gso (xO p) xH (Nodes (node001 x)) v = λ _ → refl
  gso (xO p) xH (Nodes (node010 x)) v = λ _ → refl
  gso (xO p) xH (Nodes (node011 x x₁)) v = λ _ → refl
  gso (xO p) xH (Nodes (node100 x)) v = λ _ → refl
  gso (xO p) xH (Nodes (node101 x x₁)) v = λ _ → refl
  gso (xO p) xH (Nodes (node110 x x₁)) v = λ _ → refl
  gso (xO p) xH (Nodes (node111 x x₁ x₂)) v = λ _ → refl 
  -- -----------------------
  gso (xO p) (xI q) Empty v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node001 x)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node010 x)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node011 x x₁)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node100 x)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node101 x x₁)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node110 x x₁)) v = λ _ → refl
  gso (xO p) (xI q) (Nodes (node111 x x₁ x₂)) v = λ _ → refl
  -- -----------------------     
  gso (xO p) (xO q) t v neq = {!   !}
  