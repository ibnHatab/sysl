-------------------------------- MODULE Data ---------------------------------

EXTENDS Sequences, Naturals, Poset

Map(F(_),seq) == [i \in DOMAIN seq |-> F(seq[i])]

RECURSIVE Helper(_)
FlatMap(F(_),seq) == LET Helper(s) == IF Len(s) = 0 THEN {}
                                                  ELSE F(Head(s)) \o Helper(Tail(s))
                    IN Helper(seq)

CONSTANTS M,N
ASSUME /\ M \in Nat
       /\ N \in Nat

CONSTANTS S,_ \preceq _
ASSUME Poset(S, \preceq)

CONSTANTS C,D,F(_)
THEOREM (C = D) => (F(C) = F(D))

CONSTANTS K(_),L(_)
ASSUME \A x: K(x) = L(x)


=============================================================================
