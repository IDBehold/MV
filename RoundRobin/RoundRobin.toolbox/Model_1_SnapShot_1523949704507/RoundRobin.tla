----------------------------- MODULE RoundRobin -----------------------------

EXTENDS Naturals
VARIABLES PC, CHAN, PHONE, ACCESSCOUNT
CONSTANT NodeCount

-----------------------------------------------------------------------------

IDs                 == 0 .. NodeCount - 1

TypeInvariant       == /\ PC \in [IDs -> 1..4]
                       /\ CHAN \in [IDs -> BOOLEAN]
                       /\ PHONE \in [IDs -> BOOLEAN]
                       /\ ACCESSCOUNT \in {0 .. NodeCount}
                       /\ ACCESSCOUNT <= 1
                       

-----------------------------------------------------------------------------

Init               ==  /\ PC = [p \in IDs |-> 1]
                       /\ CHAN = [[p \in IDs |-> FALSE] EXCEPT ![0] = TRUE]
                       /\ PHONE = [p \in IDs |-> FALSE]
                       /\ ACCESSCOUNT = 0

WaitForToken(id)    == /\ PC[id] = 1
                       /\ CHAN[id] = FALSE
                       /\ UNCHANGED<<PHONE, CHAN, PC, ACCESSCOUNT>>
                    
ReceiveToken(id)    == /\ PC[id] = 1
                       /\ CHAN[id] = TRUE
                       /\ PC' = [PC EXCEPT ![id] = 2]
                       /\ CHAN' = [CHAN EXCEPT ![id] = FALSE]
                       /\ UNCHANGED <<PHONE, ACCESSCOUNT>>
                       
PickUpPhone(id)     == /\ PC[id] = 2
                       /\ PC' = [PC EXCEPT ![id] = 3]
                       /\ PHONE' = [PHONE EXCEPT ![id] = TRUE]
                       /\ ACCESSCOUNT' = ACCESSCOUNT + 1
                       /\ UNCHANGED <<CHAN>>

HangUpPhone(id)     == /\ PC[id] = 3
                       /\ PHONE' = [PHONE EXCEPT ![id] = FALSE]
                       /\ PC' = [PC EXCEPT ![id] = 4]
                       /\ ACCESSCOUNT' = ACCESSCOUNT - 1
                       /\ UNCHANGED <<CHAN>>

SendToken(id, idNext) == /\ PC[id] = 4
                         /\ CHAN' = [CHAN EXCEPT ![id] = FALSE, ![idNext] = TRUE]
                         /\ PC' = [PC EXCEPT ![id] = 1]
                         /\ UNCHANGED <<PHONE, ACCESSCOUNT>>

Proc(n,x)           == \/ WaitForToken(n)
                       \/ ReceiveToken(n)
                       \/ PickUpPhone(n)
                       \/ HangUpPhone(n)
                       \/ SendToken(n,x)

Next                == \E n \in IDs : Proc(n, (n+1) % NodeCount)
                 
NoStarvation        == \A n \in IDs : [](PC[n] = 1 ~> PHONE[n] = TRUE)
 
-------------------------------------------------------------------------------

Spec == Init /\ [][Next]_<< PC, CHAN, PHONE, ACCESSCOUNT >> /\ NoStarvation
                 




=============================================================================
\* Modification History
\* Last modified Tue Apr 17 09:21:18 CEST 2018 by jensk
\* Created Mon Apr 16 12:30:39 CEST 2018 by jensk
