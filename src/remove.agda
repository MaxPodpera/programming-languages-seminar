open import Data.Maybe

open import Positive
open import CanonicalBinaryTrie

module remove where 

    resolve' : {A : Set} → Maybe (Tree' A) → Maybe A → Maybe (Tree' A) → Maybe (Tree' A)
    resolve' (just l) (just v) (just r) = just (node111 l v r)
    resolve' (just l) (just v) nothing = just (node110 l v)
    resolve' (just l) nothing (just r) = just (node101 l r)
    resolve' (just l) nothing nothing = just (node100 l)
    resolve' nothing (just v) (just r) = just (node011 v r)
    resolve' nothing (just v) nothing = just (node010 v)
    resolve' nothing nothing (just r) = just (node001 r)
    resolve' nothing nothing nothing = nothing 

    remove' : {A : Set} → Positive → Tree' A → Maybe (Tree' A)
    remove' xH (node001 t)      = resolve' nothing nothing (just t)
    remove' xH (node010 x)      = resolve' nothing nothing nothing
    remove' xH (node011 x t)    = resolve' nothing nothing (just t)
    remove' xH (node100 t)      = resolve' (just t) nothing nothing 
    remove' xH (node101 t t₁)   = resolve' (just t) nothing (just t₁)
    remove' xH (node110 t x)    = resolve' (just t) nothing nothing 
    remove' xH (node111 t x t₁) = resolve' (just t) nothing (just t₁)
    remove' (xI p) (node001 t)      = resolve' nothing nothing (remove' p t)
    remove' (xI p) (node010 x)      = resolve' nothing (just x) (nothing)
    remove' (xI p) (node011 x t)    = resolve' nothing (just x) (remove' p t)
    remove' (xI p) (node100 t)      = resolve' (just t) nothing nothing
    remove' (xI p) (node101 t t₁)   = resolve' (just t) nothing (remove' p t₁)
    remove' (xI p) (node110 t x)    = resolve' (just t) (just x) nothing
    remove' (xI p) (node111 t x t₁) = resolve' (just t) (just x) (remove' p t₁)
    remove' (xO p) (node001 t)      = resolve' nothing nothing (just t)
    remove' (xO p) (node010 x)      = resolve' nothing (just x) nothing
    remove' (xO p) (node011 x t)    = resolve' nothing (just x) (just t)
    remove' (xO p) (node100 t)      = resolve' (remove' p t) nothing nothing
    remove' (xO p) (node101 t t₁)   = resolve' (remove' p t) nothing (just t₁)
    remove' (xO p) (node110 t x)    = resolve' (remove' p t) (just x) nothing
    remove' (xO p) (node111 t x t₁) = resolve' (remove' p t) (just x) (just t₁)

    resolve : {A : Set} → Maybe (Tree' A) → Tree A 
    resolve nothing = Empty 
    resolve (just t) = Nodes t 

    remove : {A : Set} → Positive → Tree A → Tree A 
    remove _ Empty = Empty
    remove p (Nodes t) = resolve (remove' p t)
