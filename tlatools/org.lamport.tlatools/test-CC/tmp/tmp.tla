--------------------------------- MODULE tmp ---------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

VARIABLE msgs
VARIABLE cnt

CONSTANT domain
Init == /\ msgs = [x \in {1,2,3} |-> x]
        /\ cnt = 4
AddOne == /\ cnt < 10
          /\ msgs' = msgs @@ (cnt :> cnt)
          /\ cnt' = cnt + 1

Next == \/ AddOne

==================