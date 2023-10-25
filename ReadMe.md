# Canonical Binary Tries

This repositotry contains a implementation of the Efficient Extensional Binary Tries paper.

In the test.agda file a few simple test cases can be found.

The proofs.agda file contains proofs for the 
get empty property (get on an empty Tree returns nothing)
gss set and then get on the same index returns the previously set value
gso set and then get on different indexes do not influence each other.

The proofs can be executed using the emacs mode. 
Open the file and use C-c C-l to load the file.

The paper introduces a few Requirements to be fulfilled by their datastructure. (Page 2)

1. Basic operators: empty (the finite map with an empty domain), get (the lookup operator), and set (the update operator).                   
2. Proofs1 of basic laws: get i empty = None, get i (set i v m) = Some v, i!=j →get i (set j v m) = get i m.                                 
3. A purely functional implementation (which rules out hash tables, for example).                                                            
4. A persistent semantics, so that set j v m does not destroy m; this arises naturally from the purely functional implementation.           
5. Efficient representation of keys.                                                                                                       
6. Efficient asymptotic time complexity of get and set operations, as extracted to OCaml.                                                    
7. Linear-time computation of the list of key-binding pairs of a finite-map, in sorted order by key, with proofs of its properties.
8. Linear-time combining two finite maps m1 and m2 with function f yielding a map m
such that, at any key i, m(i) = f(m1(i), m2(i)) ; with proofs of its properties.

Extended Requirements
9. Efficiency in the face of sparseness: that is, if the magnitude of individual keys is much greater than the number of keys bound in the map.
10. Efficiency not only as extracted to OCaml (i.e., with proofs erased), but also as represented in Coq and computed within Coq (i.e., without proof erasure).
11. Extensionality: the property that (∀i. m1(i) = m2(i)) → m1 = m2. This allows Leibniz equality to be used in proofs about the larger systems in which the finite maps are embedded; otherwise, equivalence relations must be used, which is less convenient.

The proofs.agda file contains proofs for the properties of point 2.

The definitions of the functions and Datatypes are taken from Chapter 4 of the paper.