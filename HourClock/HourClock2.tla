----------------------------- MODULE HourClock -----------------------------


=============================================================================
\* Modification History
\* Last modified Mon Feb 05 14:23:34 CET 2018 by jacob
\* Created Mon Feb 05 14:08:58 CET 2018 by jacob
EXTENDS Naturals
VARIABLE hr, tmp
HCini == hr \in  (1..12)
HCnxt == hr' = IF hr /= 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr


THEOREM HC => []HCini