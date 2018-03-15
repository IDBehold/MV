------------------------------ MODULE InnerLIFO ------------------------------
EXTENDS Naturals, Sequences
CONSTANT Message, BufSize
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------
MyLen ==[s \in Seq(Nat) |-> Len(s)]


Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

TypeInvariant  ==  /\ InChan!TypeInvariant
                   /\ OutChan!TypeInvariant
                   /\ q \in Seq(Message)
                   /\ BufSize \in Nat
                   /\ MyLen[q] <= BufSize

SSend(msg)  ==  /\ InChan!Send(msg)        \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ MyLen[q] < BufSize

BufRcv == /\ InChan!Receive                \* Receive message from channel `in'.
          /\ q' = <<in.val>> \o q          \* insert val at the head of q.
          /\ UNCHANGED out

BufSend == /\ MyLen[q] > 0                    \* Enabled only if q is nonempty.
           /\ OutChan!Send(Head(q))        \* Send Head(q) on channel `out'
           /\ q' = Tail(q)                 \* and remove it from q.
           /\ UNCHANGED in

RRcv == /\ OutChan!Receive                 \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Thu Mar 08 09:58:50 CET 2018 by jacob
\* Created Mon Feb 12 14:42:22 CET 2018 by jacob
