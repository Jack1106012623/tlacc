---------------------- MODULE SimpleLoopWithProcedure ----------------------
EXTENDS Naturals, Sequences, TLC

(*   

--algorithm SimpleLoopWithProcedure                                     
     variable x = 0; y \in {1, 2}; n = 0; i = 0;                         
     procedure Incr(incr = 0)                                                
      variable z = 2;                                                    
      begin i1 : x := incr + z + x;                                      
            i2 : return;                                                 
     end procedure                                                       
     begin a : while i < 10                                              
                 do   when Print(x, TRUE);                               
                      i := i + 1 ;                                       
                      call Incr(y) ;                                     
               end while ;                                               
     end algorithm  

*)

					
\* BEGIN TRANSLATION PC-ce6dc0e05794186934b5326b29e10c79eb2c436351738bb26855ec9fb0cd6cd2
VARIABLES x, y, n, i, pc, stack, incr, z

vars == << x, y, n, i, pc, stack, incr, z >>

Init == (* Global variables *)
        /\ x = 0
        /\ y \in {1, 2}
        /\ n = 0
        /\ i = 0
        (* Procedure Incr *)
        /\ incr = 0
        /\ z = 2
        /\ stack = << >>
        /\ pc = "a"

i1 == /\ pc = "i1"
      /\ x' = incr + z + x
      /\ pc' = "i2"
      /\ UNCHANGED << y, n, i, stack, incr, z >>

i2 == /\ pc = "i2"
      /\ pc' = Head(stack).pc
      /\ z' = Head(stack).z
      /\ incr' = Head(stack).incr
      /\ stack' = Tail(stack)
      /\ UNCHANGED << x, y, n, i >>

Incr == i1 \/ i2

a == /\ pc = "a"
     /\ IF i < 10
           THEN /\ Print(x, TRUE)
                /\ i' = i + 1
                /\ /\ incr' = y
                   /\ stack' = << [ procedure |->  "Incr",
                                    pc        |->  "a",
                                    z         |->  z,
                                    incr      |->  incr ] >>
                                \o stack
                /\ z' = 2
                /\ pc' = "i1"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << i, stack, incr, z >>
     /\ UNCHANGED << x, y, n >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Incr \/ a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-06375659b5cf637b6d744f7ef696a1ba0f39e46f663bff8cfc8b368967cfccfc
=============================================================================
