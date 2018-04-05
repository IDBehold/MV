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
        
Send(msg)  ==  /\ InChan!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ Len(q) < QueueSize

Rcv == /\ OutChan!Rcv              \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>
=============================================================================

