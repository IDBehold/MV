------------------------------ MODULE InnerLIFO ------------------------------
EXTENDS Naturals, Sequences, BufferInterface
CONSTANT Message, BufSize
VARIABLES in, out, q
InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

-----------------------------------------------------------------------------
\*************************************************************************************
\* Functions and operators
\*************************************************************************************

\* Wraps Len(s) operator into a function
MyLen == [s \in Seq(Nat) |-> Len(s)] 

\* Simple increment function
inc == [i \in Nat |-> i+1] 

\* Simple increment operator
OpInc(i) == i + 1 

\* Recursive implementation of the length of a sequence
RecursiveLen[s \in Seq(Nat)] == IF s = << >> THEN 0 ELSE 1 + RecursiveLen[Tail(s)] 

\* The model cannot be run when using this definition
RecLen == CHOOSE RecLen :
                RecLen = [s \in Seq(Nat) |-> IF s = << >> THEN 0 ELSE 1 + RecLen[Tail(s)]]

\* Recursive implementation of a factorial function
fact[n \in Nat] == IF n = 0 THEN 1 ELSE n*fact[n-1] 

\* Recursive function for finding the n'th fibonacci number
fib[n \in Nat] == IF n <= 1 THEN n ELSE fib[n-1] + fib[n-2] 

-------------------------------------------------------------------------------
Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = << >>

TypeInvariant  ==  /\ InChan!TypeInvariant
                   /\ OutChan!TypeInvariant
                   /\ q \in Seq(Message)
                   /\ BufSize \in Nat
                   /\ RecursiveLen[q] <= BufSize

SSend(msg)  ==  /\ InChan!Send(msg)        \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>
                /\ RecursiveLen[q] < BufSize

BufRcv == /\ InChan!Receive                \* Receive message from channel `in'.
          /\ q' = <<in.val>> \o q          \* insert val at the head of q.
          /\ UNCHANGED out

BufSend == /\ RecursiveLen[q] > 0          \* Enabled only if q is nonempty.
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
\* Last modified Thu Apr 05 10:49:10 CEST 2018 by jacob
\* Created Mon Feb 12 14:42:22 CET 2018 by jacob
