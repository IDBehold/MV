----------------------------- MODULE RoundRobin -----------------------------

EXTENDS Naturals
VARIABLES PC, CHAN, PHONE, ACCESSCOUNT
CONSTANT NodeCount

-----------------------------------------------------------------------------

IDs                 == 0 .. NodeCount - 1

\****************************************************************************************************************
\* Channel is instantiated as a boolean, representing either an empty or full buffer (containing the token)
\* Phone is the shared resource.
\* Access Count is used to assert that no more than one process uses the resource(phone) at once. 
\****************************************************************************************************************
TypeInvariant       == /\ PC \in [IDs -> 1..4]
                       /\ CHAN \in [IDs -> BOOLEAN]
                       /\ PHONE \in [IDs -> BOOLEAN]
                       /\ ACCESSCOUNT \in (0 .. NodeCount)
                       /\ ACCESSCOUNT <= 1

-----------------------------------------------------------------------------

Init               ==  /\ PC = [p \in IDs |-> 1]
                       /\ CHAN = [[p \in IDs |-> FALSE] EXCEPT ![0] = TRUE]
                       /\ PHONE = [p \in IDs |-> FALSE]
                       /\ ACCESSCOUNT = 0

\****************************************************************************************************************
\* Allows for processes to wait
\****************************************************************************************************************
WaitForToken(id)    == /\ PC[id] = 1
                       /\ CHAN[id] = FALSE
                       /\ UNCHANGED<<PHONE, CHAN, PC, ACCESSCOUNT>>
                    
\****************************************************************************************************************
\* Allows for proccesses to receive the token when their channel is set to true
\****************************************************************************************************************
ReceiveToken(id)    == /\ PC[id] = 1
                       /\ CHAN[id] = TRUE
                       /\ PC' = [PC EXCEPT ![id] = 2]
                       /\ CHAN' = [CHAN EXCEPT ![id] = FALSE]
                       /\ UNCHANGED <<PHONE, ACCESSCOUNT>>

\****************************************************************************************************************
\* Allows for a process to pick up the phone and increase the accesscount
\****************************************************************************************************************                       
PickUpPhone(id)     == /\ PC[id] = 2
                       /\ PC' = [PC EXCEPT ![id] = 3]
                       /\ PHONE' = [PHONE EXCEPT ![id] = TRUE]
                       /\ ACCESSCOUNT' = ACCESSCOUNT + 1
                       /\ UNCHANGED <<CHAN>>

\****************************************************************************************************************
\* Decreases the accesscount and stops using the phone
\****************************************************************************************************************
HangUpPhone(id)     == /\ PC[id] = 3
                       /\ PHONE' = [PHONE EXCEPT ![id] = FALSE]
                       /\ PC' = [PC EXCEPT ![id] = 4]
                       /\ ACCESSCOUNT' = ACCESSCOUNT - 1
                       /\ UNCHANGED <<CHAN>>


\****************************************************************************************************************
\* Allows for a process to pass along the token, setting its own channel to false and the subsequent channel to true
\****************************************************************************************************************
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

\****************************************************************************************************************
\* Liveness property, securing that if the process counter of a process is 1, then eventually the process will receive the token and access the phone
\****************************************************************************************************************                 
NoStarvation        == \A n \in IDs : [](PC[n] = 1 ~> PHONE[n] = TRUE)
 
-------------------------------------------------------------------------------

Spec == Init /\ [][Next]_<< PC, CHAN, PHONE, ACCESSCOUNT >> /\ NoStarvation
                 

=============================================================================
\* Modification History
\* Last modified Tue Apr 17 09:42:03 CEST 2018 by jensk
\* Created Mon Apr 16 12:30:39 CEST 2018 by jensk
