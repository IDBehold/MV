---------------------------- MODULE LIFO -------------------------------
EXTENDS Naturals, Sequences
CONSTANT Message, QueueSize
VARIABLES in, out, lifoq

LIFOInterface == INSTANCE LIFO_Interface WITH q <- lifoq
-----------------------------------------------------------------------------

\****************************************************************************************************************
\* Receive message from channel `in'.
\* change the queue to contain a concatination of the new value from the in channel and the original queue
\****************************************************************************************************************
BufRcv == /\ LIFOInterface!InChan!Rcv                 
          /\ lifoq' = <<in.val>> \o lifoq       
          /\ UNCHANGED out

BufSend == /\ lifoq # << >>                                 \* Enabled only if q is nonempty.
           /\ LIFOInterface!OutChan!Send(Head(lifoq))       \* Send Tail(q) on channel `out'
           /\ lifoq' = Tail(lifoq)                          \* and remove it from q.
           /\ UNCHANGED in

Next == \/ LIFOInterface!INext
        \/ BufRcv
        \/ BufSend
        
        
\*********************************************************************************************
\* BufRcv should eventually be called if LIFOInterface!Send(msg) has been enabled
\*********************************************************************************************        
Liveness1 == \E msg \in Message : WF_<<in, out, lifoq>>(LIFOInterface!Send(msg) \/ BufRcv)

\*********************************************************************************************
\* While the lifoq is NOT empty BufSend is enabled
\*********************************************************************************************
Liveness2 == SF_<<in, out, lifoq>>(lifoq # << >> \/ BufSend)

\*********************************************************************************************
\* LIFOInterface!Rcv should eventually be called if BufSend has been enabled
\*********************************************************************************************
Liveness3 == WF_<<in, out, lifoq>>(BufSend \/ LIFOInterface!Rcv)

Spec == LIFOInterface!Init /\ [][Next]_<<in, out, lifoq>> /\ LIFOInterface!Liveness /\ Liveness1 /\ Liveness2 /\ Liveness3

-----------------------------------------------------------------------------
THEOREM Spec => []LIFOInterface!TypeInvariant
=============================================================================

