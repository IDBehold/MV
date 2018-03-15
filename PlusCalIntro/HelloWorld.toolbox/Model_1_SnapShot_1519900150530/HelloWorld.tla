----------------------------- MODULE HelloWorld -----------------------------
\* TLA+
EXTENDS Integers

\* PlusCal
(* --algorithm hello_world
variable x \in 1..5
begin
    Add: 
        x := x+1;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..5
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ x' = x+1
       /\ pc' = "Done"

Next == Add
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Thu Mar 01 11:28:53 CET 2018 by jacob
\* Created Thu Mar 01 11:18:13 CET 2018 by jacob
