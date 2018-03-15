------------------------------ MODULE InnerLIFO ------------------------------
EXTENDS Naturals, Sequences
CONSTANT Message, BufSize
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

TypeInvariant  ==  /\ InChan!TypeInvariant
                   /\ OutChan!TypeInvariant
                   /\ q \in Seq(Message)
                   /\ BufSize \in Nat
                   /\ Len(q) <= BufSize

SSend(msg)  ==  /\ InChan!Send(msg) \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ Len(q) < BufSize

BufRcv == /\ InChan!Receive              \* Receive message from channel `in'.
          /\ q' = Append(q, in.val)  \*   and append it to tail of q.
          /\ UNCHANGED out

BufSend == /\ q # << >>               \* Enabled only if q is nonempty.
           /\ OutChan!Send(Head(q))   \* Send Head(q) on channel `out'
           /\ q' = Tail(q)            \*   and remove it from q.
           /\ UNCHANGED in

RRcv == /\ OutChan!Receive          \* Receive message from channel `out'.
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
\* Last modified Thu Feb 22 11:38:27 CET 2018 by jacob
\* Created Mon Feb 12 14:42:22 CET 2018 by jacob
