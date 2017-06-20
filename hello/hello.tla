------------------------------ MODULE hello -------------------------------

EXTENDS Naturals, Reals

Double(x) == 2*x

ApplyTwice(Op(_), x) == Op(Op(x))

(* a << b == a%b = 0 *)

RECURSIVE Fact(_)
Fact(n) == IF n <=1 THEN 1 ELSE n*Fact(n-1)

Ss == ApplyTwice(LAMBDA x: x*x, 3)

Foo(a,b) == LET x == IF a <= b THEN a ELSE b
                y == x*a
            IN y*b

ExistOne(S, P(_)) == \E x \in S : P(x) /\ \A y \in S : P(y) => y = x

IsPartialOrder(R(_,_), S) ==
    /\ \A x,y,z \in S : R(x,y) /\ R(y,x) => R(x,z)
    /\ \A x \in S: \lnot R(x,x)

IsPartialOrderL(_\prec _, S) ==
    /\ \A x,y,z \in S : x \prec y /\ y \prec x =>  x \prec z
    /\ \A x \in S: \lnot x \prec x

Choice(P(_), Q(_)) ==
       /\ ( \E x: P(x)) <=> P(CHOOSE x: P(x)) (* exist *)
       /\ ( \A x: P(x)) <=> P(CHOOSE x: ~ P(x)) (* forall *)
       /\ ( \A x: P(x) <=> Q(x)) => (CHOOSE x: P(x)) = (CHOOSE x: Q(x)) (* rigth-uniqueness *)

ChooseOne(S, P(_)) == CHOOSE x \in S: P(x) /\ \A y \in S: P(y) => x = y
AnyOf(S) == CHOOSE x \in S: TRUE

(* Define Primes *)
Divides(p,n) == \E q \in Int : p*q = n
Prime(n) == n > 1 /\ \A p \in Nat: Divides(p,n) => p = n \/ p = 1

DivisorsOf(n) == {p \in Int: Divides(p,n)}
SetMax(S) == CHOOSE x \in S: \A y \in S: x >= y
GCD(m,n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))


=============================================================================
