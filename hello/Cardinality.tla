------------------------------ MODULE Cardinality --------------------------

EXTENDS Naturals, Fn

RECURSIVE Cardinality(_)
Cardinality(s) == IF s = {} THEN 0
                           ELSE LET x == CHOOSE x \in s: TRUE
                                IN 1 + Cardinality(s \ {x})

Card(s) == CHOOSE n \in Nat: \E f \in [1..n -> s]: Bijection(f,s)

Cardn(s) ==
         LET TheLargestSuch(S,_ \succ _,P(_)) ==
                                CHOOSE x \in S: P(x) /\ \A y \in S : y \succ x => ~ P(y)
         IN TheLargestSuch(Nat,>,LAMBDA n: \E f \in [1..n -> s]: Injection(f))


(* Sorting *)
Permutations(seq) == LET N == Len(seq)
                        PermsOfNums == {f \in [1..N -> 1..N]: Injection(f)}
                    IN { seq \cdot perms: perms \in PermsOfNums }

Ordered(seq,_ \preceq _) == \A i,j \in Len(seq): i < j => seq[i] \preceq seq[j]
Sort(seq,_ \preceq _) == CHOOSE out \in Permutations(seq): Ordered(out,\preceq)

(* Linked list *)
CONSTANT S
RECURSIVE Node
NULL == CHOOSE x: x \notin Node
Node == [elem: S, next: Node \cup {NULL}]

RECURSIVE LenList(_)
LenList(ll) == IF ll = NULL THEN 0 ELSE 1 + LenList(ll.next)

RECURSIVE View(_,_)
ListAsSeq(ll) == LET View(i,node) == IF i = 1 THEN node.elem
                                            ELSE View(i-1, node.next)
                IN [i \in 1..LenList(ll) |-> View(i,ll)]

RECURSIVE SeqAsList(_)
SeqAsList(s) == IF s = {} THEN NULL
                         ELSE [elem |-> s[1], next |-> SeqAsList(Tail(s))]

THEOREM \A s \in Seq(S): s = ListAsSeq(SeqAsList(s))

=============================================================================
