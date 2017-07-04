-------------------- MODULE InternalStack --------------------

EXTENDS Sequences

CONSTANTS X
VARIABLES buf,in,out
vars == {buf,in,out}

NOTHING == CHOOSE x: x \notin X

Init == buf \in {} /\ in = NOTHING /\ out = NOTHING
Push == in' \in X /\ buf' = {in'} \circ buf /\ UNCHANGED out
Pop == buf # {} /\ out' = Head(buf) /\ buf' = Tail(buf) /\ UNCHANGED in
Top == buf # {} /\ out' = Head(buf) /\ buf' = Tail(buf) /\ UNCHANGED {in,buf}

IStack == Init /\ [][Push \/ Pop \/ Top]_vars


==============================================================

-------------------- MODULE SStack --------------------
CONSTANT X
VARIABLES in,out

LOCAL Internal(buf) == INSTANCE InternalStack

SStack == \EE buf: Internal(buf)!IStack

=======================================================
