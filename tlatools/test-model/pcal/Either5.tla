------------------------------- MODULE Either5 ------------------------------ 
EXTENDS Naturals, Sequences, TLC

(* --algorithm Either
      variables x = 0 ; y = 0 ; z = 0 ;
      procedure Foo(a) 
       begin c: x := x + a ;
                return 
       end procedure;           
      begin a: either x := 1 ; y := 0 ;
                   or y := 1 ; 
                   or call Foo(1) ; 
                     b: assert x = 1 ;
               end either ;
             d:  assert x+y = 1 ;
     end algorithm
*)

\* BEGIN TRANSLATION PC-e61e46b2a621103192df33569e78ac667a248e9cefc0781ac218bc789db1e5fb
\* Label a at line 10 col 16 changed to a_
CONSTANT defaultInitValue
VARIABLES x, y, z, pc, stack, a

vars == << x, y, z, pc, stack, a >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ z = 0
        (* Procedure Foo *)
        /\ a = defaultInitValue
        /\ stack = << >>
        /\ pc = "a_"

c == /\ pc = "c"
     /\ x' = x + a
     /\ pc' = Head(stack).pc
     /\ a' = Head(stack).a
     /\ stack' = Tail(stack)
     /\ UNCHANGED << y, z >>

Foo == c

a_ == /\ pc = "a_"
      /\ \/ /\ x' = 1
            /\ y' = 0
            /\ pc' = "d"
            /\ UNCHANGED <<stack, a>>
         \/ /\ y' = 1
            /\ pc' = "d"
            /\ UNCHANGED <<x, stack, a>>
         \/ /\ /\ a' = 1
               /\ stack' = << [ procedure |->  "Foo",
                                pc        |->  "b",
                                a         |->  a ] >>
                            \o stack
            /\ pc' = "c"
            /\ UNCHANGED <<x, y>>
      /\ z' = z

b == /\ pc = "b"
     /\ Assert(x = 1, "Failure of assertion at line 13, column 25.")
     /\ pc' = "d"
     /\ UNCHANGED << x, y, z, stack, a >>

d == /\ pc = "d"
     /\ Assert(x+y = 1, "Failure of assertion at line 15, column 18.")
     /\ pc' = "Done"
     /\ UNCHANGED << x, y, z, stack, a >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Foo \/ a_ \/ b \/ d
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-152281d3e9d37725984a653c43105f74966a09b70a3b30fec7a6003a61c8584d

=============================================================================
