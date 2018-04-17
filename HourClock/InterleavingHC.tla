--------------------------- MODULE InterleavingHC ---------------------------

EXTENDS Integers
VARIABLE hr1, hr2

----------------------------------------------------------------------------

TCini == /\ hr1 \in (1 .. 12)
         /\ hr2 \in (1 .. 12)

HCnxt(hr) == /\ hr' = IF hr /= 12 THEN hr + 1 ELSE 1

TCnxt == \/ HCnxt(hr1) /\ (hr2' = hr2)
         \/ HCnxt(hr2) /\ (hr1' = hr1)

Spec == /\ TCini 
        /\ [][TCnxt]_<<hr1,hr2>>

----------------------------------------------------------------------------

THEOREM Spec => []TCini
=============================================================================
\* Modification History
\* Last modified Tue Apr 17 09:24:45 CEST 2018 by jacob
\* Created Tue Apr 17 09:18:49 CEST 2018 by jacob
