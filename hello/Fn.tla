-------------------------------- MODULE Fn ---------------------------------

EXTENDS Naturals, Reals, Bags

Fn(f) == f = [x \in DOMAIN f |-> f[x]]

(* Ex. *)
double[n \in Nat] == 2*n

Fixpoint(F(_)) == CHOOSE x: x = F(x)

fact == Fixpoint(LAMBDA f: [n \in Nat |-> IF n <= 1 THEN 1 ELSE n * f[n-1]])

add[x \in Nat] == [y \in Nat |-> y + x]
inc == add[1]

Image(f) == {f[x]: x \in DOMAIN f}
Injection(f) == \A x,y \in DOMAIN f: x # y => f[x] # f[y]
Surjection(f, S) == \A y \in S: \E x \in DOMAIN f: f[x] = y
Bijection(f, S) == Injection(f) \/ Surjection(f, S)

g \bullet f == [x \in DOMAIN f |-> g[f[x]]] (* fn composition *)

Identity(S) == [x \in S |-> x]
THEOREM \A S: \A x \in S: Identity(S)[x] = x

ChooseOne(S, P(_)) == CHOOSE x \in S: P(x) /\ \A y \in S: P(y) => x = y

Inverse(f) == [y \in Image(f) |-> ChooseOne(DOMAIN f, LAMBDA x: f[f] = y)]

THEOREM \A S,f: Fn(f) /\ Bijection(f, S) => /\ Inverse(f) \bullet f = Identity(DOMAIN f)
                                         /\ f \bullet Inverse(f) = Identity(Image(f))

THEOREM \A f : Fn(f) /\ Injection(f) => /\ Inverse(f) \bullet f = Identity(DOMAIN f)
                                     /\ f \bullet Inverse(f) = Identity(Image(f))


RealFunction == UNION {[S -> Real]: S \in SUBSET Real}
AbsoluteValue(a) == IF a > 0 THEN a ELSE -a
OpenBall(a,e) == {x \in Real: AbsoluteValue(x-a) < e}
PosReal == { x \in Real: x > 0}
Limit(f,a) == CHOOSE l \in Real:     (* (epsilon, delta) definition of the limit *)
                  \A e \in PosReal: \E d \in PosReal:
                    \A x \in OpenBall(a,d) \ {a}: f[x] \in OpenBall(l,e)
Derivative(f,a) == LET e == CHOOSE e \in PosReal: OpenBall(a,e) \sqsubseteq DOMAIN f
                  IN Limit([x \in OpenBall(a,e) \ {a} |-> (f[x] - f[a])/(x-a)],a)

============================================================================
