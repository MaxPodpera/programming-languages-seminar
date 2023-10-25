open import Positive
open import CanonicalBinaryTrie
open import get 
open import set
open import mapFilter

open import Agda.Builtin.Unit
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
import Agda.Primitive 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; _≢_)
open import Data.Empty
open Eq.≡-Reasoning
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (contradiction)
import Relation.Nullary.Negation using (contraposition)


module proofs where
 
  data _≠_ : Positive → Positive → Set where 
    i≠o : ∀ {p q : Positive} → (xI p) ≠ (xO q)
    o≠i : ∀ {p q : Positive} → (xO p) ≠ (xI q)
    i≠i : ∀ {p q : Positive} → p ≠ q → (xI p) ≠ (xI q)
    o≠o : ∀ {p q : Positive} → p ≠ q → (xO p) ≠ (xO q)

  ≠-sym : ∀ {p q : Positive} → p ≠ q → q ≠ p
  ≠-sym i≠o = o≠i
  ≠-sym o≠i = i≠o
  ≠-sym (i≠i x) = i≠i (≠-sym x)
  ≠-sym (o≠o x) = o≠o (≠-sym x)

  inv-≠II : ∀ {p q : Positive} → (xI p) ≠ (xI q) → p ≠ q 
  inv-≠II (i≠i x) = x 

  inv-≠OO : ∀ {p q : Positive} → (xO p) ≠ (xO q) → p ≠ q 
  inv-≠OO (o≠o x) = x
  
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


  gso : {A : Set} → ∀ (i j : Positive) (t : Tree A) (v : A) → (i ≠ j) → (get i (set j v t) ≡ get i t)
  gso .(xI _) .(xO _) Empty v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node001 x)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node010 x)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node011 x x₁)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node100 x)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node101 x x₁)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node110 x x₁)) v i≠o = refl
  gso .(xI _) .(xO _) (Nodes (node111 x x₁ x₂)) v i≠o = refl
  gso .(xO _) .(xI _) Empty v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node001 x)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node010 x)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node011 x x₁)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node100 x)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node101 x x₁)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node110 x x₁)) v o≠i = refl
  gso .(xO _) .(xI _) (Nodes (node111 x x₁ x₂)) v o≠i = refl
  gso (xI p) (xI q) Empty v (i≠i x) = gso p q Empty v x 
  gso (xI p) (xI q) (Nodes (node001 x₁)) v (i≠i x) = gso p q (Nodes x₁) v x
  gso (xI p) (xI q) (Nodes (node010 x₁)) v (i≠i x) = gso p q Empty v x 
  gso (xI p) (xI q) (Nodes (node011 x₁ x₂)) v (i≠i x) = gso p q (Nodes x₂) v x 
  gso (xI p) (xI q) (Nodes (node100 x₁)) v (i≠i x) = gso p q Empty v x 
  gso (xI p) (xI q) (Nodes (node101 x₁ x₂)) v (i≠i x) = gso p q (Nodes x₂) v x 
  gso (xI p) (xI q) (Nodes (node110 x₁ x₂)) v (i≠i x) = gso p q Empty v x 
  gso (xI p) (xI q) (Nodes (node111 x₁ x₂ x₃)) v (i≠i x) = gso p q (Nodes x₃) v x 
  gso (xO p) (xO q) Empty v (o≠o x) = gso p q Empty v x
  gso (xO p) (xO q) (Nodes (node001 x₁)) v (o≠o x) = gso p q Empty v x 
  gso (xO p) (xO q) (Nodes (node010 x₁)) v (o≠o x) = gso p q Empty v x
  gso (xO p) (xO q) (Nodes (node011 x₁ x₂)) v (o≠o x) = gso p q Empty v x 
  gso (xO p) (xO q) (Nodes (node100 x₁)) v (o≠o x) = gso p q (Nodes x₁) v x
  gso (xO p) (xO q) (Nodes (node101 x₁ x₂)) v (o≠o x) = gso p q (Nodes x₁) v x 
  gso (xO p) (xO q) (Nodes (node110 x₁ x₂)) v (o≠o x) = gso p q (Nodes x₁) v x 
  gso (xO p) (xO q) (Nodes (node111 x₁ x₂ x₃)) v (o≠o x) = gso p q (Nodes x₁) v x 