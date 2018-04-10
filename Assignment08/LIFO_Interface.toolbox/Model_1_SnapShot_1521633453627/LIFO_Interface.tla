---------------------------- MODULE LIFO_Interface -------------------------------
EXTENDS Naturals, Sequences
CONSTANT QueueSize, Message
VARIABLES q, in, out

InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------
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
=============================================================================

