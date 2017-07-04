------------------------ MODULE Fact ------------------------

EXTENDS Naturals, Sequences, Integers

VARIABLES N,i,f

Fact2 == /\ N \in Nat /\ f = 1 /\ i = N
        /\ [] [IF i > 1 THEN f' = f*i /\ i' = i-1 /\ UNCHANGED N
                      ELSE UNCHANGED {f,i,N}]_{f,i,N}

VARIABLES pc,stack

vars == {f,i,pc,stack}

Top == stack[1]
Push(x) == stack' = {x} \circ stack
Pop == stack' = Tail(stack)

Return(x) == f' = x /\ {i,pc}' = Top /\ Pop
Recurse(x) == i' = x /\ pc' = 1 /\ Push({i,pc+1})

Fact3 == /\ N \in Nat /\ f = 1 /\ i = N /\ pc = 1 /\ stack = {{"-"},-1}
        /\ [] [ /\ pc # -1
              /\ IF pc = 1 /\ i > 1 THEN Recurse(i-1) /\ UNCHANGED f
                                  ELSE Return(IF i <= 1 THEN 1 ELSE i*f)
              /\ UNCHANGED N]_vars

VARIABLE depth

Space == depth = 0 /\ [depth' = depth + (Len(stack)' - Len(stack))]_{depth,stack}

(* THEOREM \A n \in Nat: N = n /\ Fac3 /\ Space => [][depth <= n] *)

BigO(f) == {g \in [Nat -> Nat]: \Ec \in Nat: \A k \in Nat: g[k] <= c * f[k]}

Complexity(CompClass,Alg,Input,InputSize(_),measere) ==
          \E f \in CompClass: \A x \in Input: Alg(x) => [] (measere <= f[InputSize(x)])

log(n) == n (* ??? *)

ct == Complexity(BigO([k \in Nat |-> 2^k]),
                LAMBDA n: N=n /\ Fact3 /\ Space,
                Nat, LAMBDA n: log(n), depth)

Fact1 == /\ N \in Nat /\ f=1 /\ i=2
        /\ [] [ /\ i<= N
              /\ f' = f*i
              /\ i' =i+1
              /\ UNCHANGED N]_{f,i,N}

==============================================================
