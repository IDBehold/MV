---------------------------- MODULE LIFO_Interface -------------------------------
EXTENDS Naturals, Sequences
CONSTANT QueueSize, Message
VARIABLES q, in, out

InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------

\****************************************************************************************************************
\* Generalized sender/reciever interface - The Send and Rcv methods and a queue is specified, while specifics about how its done is omitted
\****************************************************************************************************************
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>
        
TypeInvariant  ==  /\ InChan!TypeInvariant
           /\ OutChan!TypeInvariant
           /\ q \in Seq(Message)
           /\ QueueSize > 0
           /\ QueueSize \in Nat
           /\ Len(q) <= QueueSize
        
Send(msg)  ==  /\ InChan!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ Len(q) < QueueSize

Rcv == /\ OutChan!Rcv              \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>
        
INext == \/ \E msg \in Message : Send(msg)
        \/ Rcv
        
\*Liveness == \E msg \in Message : WF_<<in, out, q>>(Send(msg) \/ Rcv)

ISpec == Init /\ [][INext]_<<in, out, q>> \*/\ Liveness
-----------------------------------------------------------------------------
THEOREM ISpec => []TypeInvariant
=============================================================================

