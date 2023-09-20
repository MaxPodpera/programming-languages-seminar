open  import Data.Maybe
module CanonicalBinaryTrie where 
    {- Positive -}
    data Positive : Set where 
        xH : Positive
        xI : Positive -> Positive
        xO : Positive -> Positive

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

    {- Get Version1 -}
    get1 : {A : Set} -> Positive -> Tree_I A -> Maybe A 
    get1 xH (node001 _ ) = nothing
    get1 xH (node010 v ) = just v 
    get1 xH (node011 v _ ) = just v
    get1 xH (node100 _ ) = nothing
    get1 xH (node101 _ _ ) = nothing
    get1 xH (node110 _ v) = just v 
    get1 xH (node111 _ v _) = just v

    get1 (xO q) (node001 _ )= nothing
    get1 (xO q) (node010 _ )= nothing 
    get1 (xO q) (node011 _ _ )= nothing
    get1 (xO q) (node100 l )= get1 q l
    get1 (xO q) (node101 l _ )=  get1 q l
    get1 (xO q) (node110 l _ )= get1 q l
    get1 (xO q) (node111 l _ _ )= get1 q l

    get1 (xI q) (node001 r )= get1 q r
    get1 (xI q) (node010 _ )= nothing 
    get1 (xI q) (node011 _ r )= get1 q r
    get1 (xI q) (node100 r )= nothing
    get1 (xI q) (node101 _ r )=  get1 q r
    get1 (xI q) (node110 _ _ )= nothing
    get1 (xI q) (node111 _ _ r )= get1 q r


    get : {A : Set} -> Positive -> Tree A -> Maybe A
    get _ Empty = nothing
    get p (Nodes n) = get1 p n 

    {- Set Version1 -}
    set0 : {A : Set} -> Positive -> A -> Tree_I A
    set0 xH v = node010 v 
    set0 (xI q) v = node001 (set0 q v)
    set0 (xO q) v = node100 (set0 q v)

    set_ : {A : Set} -> Positive -> A -> Tree_I A -> Tree_I A
    set_ xH v (node001 r )= node011 v r 
    set_ xH v (node010 _ )= node010 v 
    set_ xH v (node011 _ r )= node011 v r 
    set_ xH v (node100 l )= node110 l v
    set_ xH v (node101 l r )= node111 l v r 
    set_ xH v (node110 l _ )= node110 l v  
    set_ xH v (node111 l _ r )= node111 l v r 

    set_ (xO q) v (node001 r )= node101 (set0 q v) r 
    set_ (xO q) v (node010 v1 )= node110 (set0 q v) v1
    set_ (xO q) v (node011 v1 r )= node111 (set0 q v) v1 r
    set_ (xO q) v (node100 l )= node100 (set_ q v l)
    set_ (xO q) v (node101 l r )= node101 (set_ q v l) r
    set_ (xO q) v (node110 l v1 )= node110 (set_ q v l) v1 
    set_ (xO q) v (node111 l v1 r )= node111 (set_ q v l) v1 r

    set_ (xI q) v (node001 r )= node001 (set_ q v r)
    set_ (xI q) v (node010 v1 )= node011 v1 (set0 q v)
    set_ (xI q) v (node011 v1 r )= node011 v1 (set_ q v r)
    set_ (xI q) v (node100 l )= node101 l (set0 q v)
    set_ (xI q) v (node101 l r )= node101 l (set_ q v r)
    set_ (xI q) v (node110 l v1 )= node111 l v1 (set0 q v)
    set_ (xI q) v (node111 l v1 r )= node111 l v1 (set_ q v r)

    set : {A : Set} -> Positive -> A -> Tree A -> Tree A
    set p v Empty = Nodes (set0 p v)
    set p v (Nodes m) = Nodes (set_ p v m)
