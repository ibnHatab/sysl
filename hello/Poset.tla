------------------------------ MODULE Poset -------------------------------

EXTENDS Naturals, Integers


(*
         proset - a set with preorder
         poset - partially-ordered set
         and totally-ordered set
*)

Proset(S, _ \preceq _) == /\ \A a \in S: a \preceq a (* Reflexivity *)
                   /\ \A a,b,c \in S: (a \preceq b /\ b \preceq c) => a \preceq c (* Transitivity *)

Poset(S, _ \preceq _) == /\ Proset(S, \preceq)
                  /\ \A a,b \in S : (a \preceq b /\ b \preceq a) => a = b (* Antisymmetry *)

Toset(S, _ \preceq _) == /\ Poset(S, \preceq)
                  /\ \A a,b \in S : a \preceq b \/ b \preceq a (* Totality *)

(*
The semigroup, monoid and group.
*)

Semigroup(S, _ \cdot _) == /\ \A a,b \in S: a \cdot b \in S (* Closure *)
                      /\ \A a,b,c \in S: ((a \cdot b) \cdot c) = (a \cdot (b \cdot c)) (* Associativity *)

Monoid(M, _ \cdot _) == /\ Semigroup(M, \cdot)
                   /\ \E id \in M: \A a \in M: /\ (id \cdot a) = a /\ (a \cdot id) = a (* Identity element *)

Group(G, _ \cdot _) == /\ Monoid(G, \cdot)
                  /\ \E id \in G: \A a \in G: /\ id \cdot a = a /\ a \cdot id = a
                                       /\ \E b \in G: a \cdot b = id /\ b \cdot a = id (* Inverse element *)

AbelianGroup(G, _ \cdot _) == /\ Group(G, \cdot)
                         /\ \A a,b: a \cdot b = b \cdot a (* Commutativity *)

(*
 Quotient set.
*)
Quotient(S, _ \sim _) == /\ { x \in SUBSET S: /\ x # {}
                                       /\ \A a,b \in x: a \sim b
                                       /\ \A a \in S: ( \E b \in x: a \sim b) => a \in x }


(* T == /\ Print(Quotient({1,2,3,4}, LAMBDA a,b: a%2 = b%2), TRUE) *)

AnyOf(S) == CHOOSE x \in S: TRUE
ClassOf(a,S,_ \sim _) == {b \in S: b \sim a}
Quotient(S, _ \sim _) == {ClassOf(a, S, \sim): a \in S}


THEOREM AbelianGroup(Int, +)

THEOREM \A n \in Nat \ {0}: LET a \sim b == a % n = b % n (* Eq mod n*)
                             a (+) b == ClassOf(AnyOf(a) + AnyOf(b), Int, \sim) (* Sum on equiv class *)
                         IN AbelianGroup(Quotient(Int, \sim), (+))

THEOREM UniqueIdentity ==
        ASSUME NEW M, NEW _ \cdot _, Monoid(M, \cdot)
        PROVE \A x,y \in M: /\ \A a \in M: (x \cdot a) = a /\ (a \cdot x) = a
                         /\ \A a \in M: (y \cdot a) = a /\ (a \cdot y) = a
                => x = y
    BY DEF Monoid

=============================================================================
