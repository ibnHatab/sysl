--------------------- MODULE Proof --------------------

EXTENDS Naturals

THEOREM ForallIntr ==
        ASSUME NEW P(_), NEW S,
               ASSUME NEW x \in S
               PROVE P(x)
        PROVE \A x \in S: P(x)
    OBVIOUS

THEOREM NatInduction ==
        ASSUME NEW P(_),
               P(0),
               \A n \in Nat: P(n) => P(n+1)
        PROVE \A n \in Nat: P(n)

THEOREM ASSUME NEW x \in Nat
        PROVE x = 0 \/ x - 1 >= 0
    BY NatInduction

=======================================================
