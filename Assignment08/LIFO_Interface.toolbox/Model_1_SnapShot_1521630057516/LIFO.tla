---------------------------- MODULE LIFO -------------------------------
EXTENDS Naturals, Sequences, LIFO_Interface
CONSTANT Message, QueueSize
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out
-----------------------------------------------------------------------------

Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

\****************************************************************************************************************
\* Added a queueSize constant to the typeinvariants, so that the buffer had a finite number of elements
\****************************************************************************************************************
TypeInvariant  ==  /\ InChan!TypeInvariant
                   /\ OutChan!TypeInvariant
                   /\ q \in Seq(Message)
                   /\ QueueSize > 0
                   /\ QueueSize \in Nat
                   /\ Len(q) <= QueueSize


\****************************************************************************************************************
\* Changed sender send to only be applicable when the current length of the queue is lower than the maximum queue size
\****************************************************************************************************************
SSend(msg)  ==  /\ InChan!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ Len(q) < QueueSize

\****************************************************************************************************************
\* Receive message from channel `in'.
\* change the queue to contain a concatination of the new value from the in channel and the original queue
\****************************************************************************************************************
BufRcv == /\ InChan!Rcv                 
          /\ q' = <<in.val>> \o q       
          /\ UNCHANGED out

BufSend == /\ q # << >>                 \* Enabled only if q is nonempty.
           /\ OutChan!Send(Head(q))     \* Send Tail(q) on channel `out'
           /\ q' = Tail(q)              \*   and remove it from q.
           /\ UNCHANGED in

RRcv == /\ OutChan!Rcv          \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================

