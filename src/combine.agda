open import Data.Maybe

open import Positive
open import CanonicalBinaryTrie
open import mapFilter

module combine where 

    combine'_l_helper : {A B C : Set} → (Maybe A → Maybe B → Maybe C) → (Maybe A → Maybe C)
    combine'_l_helper f = λ _ → f _ nothing 

    combine'_l : {A B C : Set} → Tree' A → (Maybe A → Maybe B → Maybe C) → Tree' C
    combine'_l t f = mapFilter' (λ _ → f _ nothing) t --mapFilter' (temp f) t --mapFilter' (λ a → f a nothing) t

    combine'_r : {A B C : Set} → Tree' B → (Maybe A → Maybe B → C) → Tree' C
    combine'_r t f = {!   !} --  mapFilter' (λ b → f nothing b) t 

    combine' : {A B C : Set} → Tree' A → Tree' B → (Maybe A → Maybe B → C) → Tree' C 
    combine' (node001 a) (node001 b) f = combine' a b f
    combine' (node001 a) (node010 x) f = node011 (f nothing (just x)) (combine'_l a f)
    combine' (node001 a) (node011 x b) f = node011 (f nothing (just x)) (combine' a b f)
    combine' (node001 a) (node100 b) f = node101 (combine'_l a f) (combine'_r b f)
    combine' (node001 a) (node101 b b₁) f = node101 (combine' a b f) (combine'_r b f)
    combine' (node001 a) (node110 b x) f = node111 (combine'_r b f) (f nothing (just x)) (combine'_l a f)
    combine' (node001 a) (node111 b x b₁) f = node111 (combine'_r b f) (f nothing (just x)) (combine' a b₁ f)
    combine' (node010 x) (node001 b) f = node011 (f (just x) nothing) (combine'_r b f)
    combine' (node010 x) (node010 x₁) f = node010 (f (just x) (just x₁))
    combine' (node010 x) (node011 x₁ b) f = node011 (f (just x) (just x₁)) (combine'_r b f)
    combine' (node010 x) (node100 b) f = node110 (combine'_r b f) (f (just x) nothing)
    combine' (node010 x) (node101 b b₁) f = node111 (combine'_r b f) (f (just x) nothing) (combine'_r b₁ f)
    combine' (node010 x) (node110 b x₁) f = node110 (combine'_r b f) (f (just x) (just x₁))
    combine' (node010 x) (node111 b x₁ b₁) f = node111 (combine'_r b f) (f (just x) (just x₁)) (combine'_r b₁ f)
    combine' (node011 x a) (node001 b) f = node011 (f (just x) nothing) (combine' a b f)
    combine' (node011 x a) (node010 x₁) f = node011 (f (just x) (just x₁)) (combine'_l a f)
    combine' (node011 x a) (node011 x₁ b) f = node011 (f (just x) (just x₁)) (combine' a b f)
    combine' (node011 x a) (node100 b) f = node111 (combine'_r b f) (f (just x) nothing) (combine'_l a f)
    combine' (node011 x a) (node101 b b₁) f = node111 (combine'_r b f) (f (just x) nothing) (combine' a b f)
    combine' (node011 x a) (node110 b x₁) f = node111 (combine'_r b f) (f (just x) (just x₁)) (combine'_l a f)
    combine' (node011 x a) (node111 b x₁ b₁) f = node111 (combine'_r b f) (f (just x) (just x₁)) (combine' a b₁ f)
    combine' (node100 a) (node001 b) f = node101 (combine'_l a f) (combine'_r b f)
    combine' (node100 a) (node010 x) f = node110 (combine'_l a f) (f nothing (just x))
    combine' (node100 a) (node011 x b) f = node111 (combine'_l a f) (f nothing (just x)) (combine'_r b f)
    combine' (node100 a) (node100 b) f = node100 (combine' a b f)
    combine' (node100 a) (node101 b b₁) f = node101 (combine' a b f) (combine'_r b₁ f)
    combine' (node100 a) (node110 b x) f = node110 (combine' a b f) (f nothing (just x))
    combine' (node100 a) (node111 b x b₁) f = node111 (combine' a b f) (f nothing (just x)) (combine'_r b₁ f)
    combine' (node101 a a₁) (node001 b) f = node101 (combine'_l a f) (combine' a₁ b f)
    combine' (node101 a a₁) (node010 x) f = node111 (combine'_l a f) (f nothing (just x)) (combine'_l a₁ f)
    combine' (node101 a a₁) (node011 x b) f = node111 (combine'_l a f) (f nothing (just x)) (combine' a₁ b f)
    combine' (node101 a a₁) (node100 b) f = node101 (combine' a b f) (combine'_l a₁ f)
    combine' (node101 a a₁) (node101 b b₁) f = node101 (combine' a b f) (combine' a₁ b₁ f)
    combine' (node101 a a₁) (node110 b x) f = node111 (combine' a b f) (f nothing (just x)) (combine'_l a₁ f)
    combine' (node101 a a₁) (node111 b x b₁) f = node111 (combine' a b f) (f nothing (just x)) (combine' a₁ b₁ f)
    combine' (node110 a x) (node001 b) f = node111 (combine'_l a f) (f (just x) nothing) (combine'_r b f)
    combine' (node110 a x) (node010 x₁) f = node110 (combine'_l a f) (f (just x) (just x₁))
    combine' (node110 a x) (node011 x₁ b) f = node111 (combine'_l a f) (f (just x) (just x₁)) (combine'_r b f)
    combine' (node110 a x) (node100 b) f = node110 (combine' a b f) (f (just x) nothing)
    combine' (node110 a x) (node101 b b₁) f = node111 (combine' a b f) (f (just x) nothing) (combine'_r b f)
    combine' (node110 a x) (node110 b x₁) f = node110 (combine' a b f) (f (just x) (just x₁))
    combine' (node110 a x) (node111 b x₁ b₁) f = node111 (combine' a b f) (f (just x) (just x₁)) (combine'_r b₁ f)
    combine' (node111 a x a₁) (node001 b) f = node111 (combine'_l a f) (f (just x) nothing) (combine' a₁ b f)
    combine' (node111 a x a₁) (node010 x₁) f = node111 (combine'_l a f) (f (just x) (just x₁)) (combine'_l a₁ f) 
    combine' (node111 a x a₁) (node011 x₁ b) f = node111 (combine'_l a f) (f (just x) (just x₁)) (combine' a₁ b f)
    combine' (node111 a x a₁) (node100 b) f = node111 (combine' a b f) (f (just x) nothing) (combine'_l a₁ f)
    combine' (node111 a x a₁) (node101 b b₁) f = node111 (combine' a b f) (f (just x) nothing) (combine' a₁ b₁ f)
    combine' (node111 a x a₁) (node110 b x₁) f = node111 (combine' a b f) (f (just x) (just x₁)) (combine'_l a₁ f)
    combine' (node111 a x a₁) (node111 b x₁ b₁) f = node111 (combine' a b f) (f (just x) (just x₁)) (combine' a₁ b₁ f)


    combine : {A B C : Set} → Tree A → Tree B → (Maybe A → Maybe B → C) → Tree C
    combine Empty Empty f = Empty
    combine Empty (Nodes x) f = {!   !} --Nodes (combine' nothing (just x) f)
    combine (Nodes x) Empty f = {!   !} --Nodes (combine' (just x) nothing f)
    combine (Nodes x) (Nodes x₁) f = {!   !} -- Nodes (combine' (just x) (just x₁) f)
