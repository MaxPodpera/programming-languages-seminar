module CanonicalBinaryTrie.OP.get where 
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
