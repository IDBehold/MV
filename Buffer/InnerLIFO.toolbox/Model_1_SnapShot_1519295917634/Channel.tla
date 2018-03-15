------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

TypeInvariant == chan \in [val:Data, rdy:{0,1}, ack:{0,1}]

-----------------------------------------------------------------------------

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy
        
Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1-@]

Receive == /\ chan.rdy /= chan.ack
           /\ chan' = [chan EXCEPT !.ack = 1-@]

Next == (\E d \in Data : Send(d)) \/ Receive

Spec == Init /\ [][Next]_chan

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Mon Feb 12 14:57:15 CET 2018 by jacob
\* Created Mon Feb 12 14:42:22 CET 2018 by jacob
