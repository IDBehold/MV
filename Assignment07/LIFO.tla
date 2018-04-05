---------------------------- MODULE LIFO -------------------------------
EXTENDS Naturals, Sequences
CONSTANT Message, QueueSize
VARIABLES in, out, lifoq

LIFOInterface == INSTANCE LIFO_Interface WITH q <- lifoq
-----------------------------------------------------------------------------

Init == /\ LIFOInterface!Init
TypeInvariant  ==  LIFOInterface!TypeInvariant

\****************************************************************************************************************
\* Send uses the generalized send method
\****************************************************************************************************************
SSend(msg)  ==  LIFOInterface!Send(msg)

\****************************************************************************************************************
\* Receive message from channel `in'.
\* change the queue to contain a concatination of the new value from the in channel and the original queue
\****************************************************************************************************************
BufRcv == /\ LIFOInterface!InChan!Rcv                 
          /\ lifoq' = <<in.val>> \o lifoq       
          /\ UNCHANGED out

BufSend == /\ lifoq # << >>                                 \* Enabled only if q is nonempty.
           /\ LIFOInterface!OutChan!Send(Head(lifoq))       \* Send Tail(q) on channel `out'
           /\ lifoq' = Tail(lifoq)                          \*   and remove it from q.
           /\ UNCHANGED in

RRcv == LIFOInterface!Rcv

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, lifoq>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================

