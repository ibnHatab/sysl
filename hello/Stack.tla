----------------------- MODULE Stack ------------------------

EXTENDS Sequences

CONSTANTS X,
          EMPTY,
          push, pop,top

Least(C(_)) == CHOOSE T: /\ C(T)
                        /\ \A U \in SUBSET T: C(U) => U=T

LOCAL StackT(U) ==
                /\ EMPTY \in U
                /\ \A x \in X, s \in U: push(s,x) \in U
                /\ \A x \in X, s \in U: push(s,x) \notin EMPTY

Stack == Least(StackT)

AXIOM A1 == /\ push \in [Stack \X X -> Stack \ {EMPTY}]
           /\ pop \in [Stack \ {EMPTY} -> Stack]
           /\ top \in [Stack \ {EMPTY} -> X]

AXIOM A2 == \A x \in X, s \in Stack: top(push(s,x)) = x
AXIOM A3 == \A x \in X, s \in Stack: pop(push(s,x)) = s


=============================================================
