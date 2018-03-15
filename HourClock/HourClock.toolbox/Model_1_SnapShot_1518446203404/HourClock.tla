----------------------------- MODULE HourClock -----------------------------

EXTENDS Integers
VARIABLE hr, tmp
HCini == /\ hr \in (1 .. 12)
         /\ tmp > -273


HCnxt == /\ hr' = IF hr /= 12 THEN hr + 1 ELSE 1
         /\ tmp' > -273


HC == HCini /\ [][HCnxt]_<<tmp,hr>>

----------------------------------------------------------------------------

THEOREM HC => []HCini
=============================================================================
\* Modification History
\* Last modified Mon Feb 12 15:36:28 CET 2018 by jacob
\* Created Mon Feb 05 14:25:15 CET 2018 by jacob