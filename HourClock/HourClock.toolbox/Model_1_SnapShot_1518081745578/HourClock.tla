----------------------------- MODULE HourClock -----------------------------

EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr /= 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
=============================================================================
\* Modification History
\* Last modified Thu Feb 08 10:22:18 CET 2018 by jacob
\* Created Mon Feb 05 14:25:15 CET 2018 by jacob