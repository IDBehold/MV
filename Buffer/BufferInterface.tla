-------------------------- MODULE BufferInterface --------------------------
VARIABLE bufInt

CONSTANTS Send(_,_,_,_),
          Rcv(_,_,_),
          InitBufInt,
          Proc,
          Val

ASSUME \A p, d, biOld, biNew : /\ Send(p, d, biOld, biNew) \in BOOLEAN
                               /\ Rcv(p, biOld, biNew) \in BOOLEAN

-----------------------------------------------------------------------------

BReq == [op:{"Send"}, val: Val] \cup [op:{"Rcv"}]

NoVal == CHOOSE v : v \notin Val

=============================================================================
\* Modification History
\* Last modified Thu Mar 15 09:41:29 CET 2018 by jacob
\* Created Thu Mar 15 09:27:49 CET 2018 by jacob
