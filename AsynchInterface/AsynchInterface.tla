-------------------------- MODULE AsynchInterface --------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE val, rdy, ack
TypeInvariant == /\ val \in Data
                 /\ rdy \in {0,1}
                 /\ ack \in {0,1}

-----------------------------------------------------------------------------

Init == /\ val \in Data
        /\ rdy \in {0,1}
        /\ ack=rdy
        
Send == /\ rdy=ack
        /\ val' \in Data
        /\ rdy'=1-rdy
        /\ UNCHANGED ack

Receive == /\ rdy /= ack
           /\ ack'=1-ack
           /\ UNCHANGED<<val,rdy>>

Next == Send \/ Receive

Spec == Init /\ [][Next]_<<val,rdy,ack>>

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Mon Feb 12 14:41:04 CET 2018 by jacob
\* Created Mon Feb 12 13:50:41 CET 2018 by jacob
