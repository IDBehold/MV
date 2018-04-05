----------------------------- MODULE Functions -----------------------------
EXTENDS Naturals, Sequences
VARIABLE x



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

TestFib == x = 1

TestNext == /\ fib[1] = 1
            /\ fib[2] = 2
            /\ fib[3] = 3
            /\ fib[4] = 5
            /\ fib[5] = 8
            /\ fib[6] = 13
            /\ fib[7] = 21
            /\ fib[8] = 34
            /\ fib[9] = 55
            /\ fib[10] = 89
            /\ x' = 1 - x

TypeInvariant == /\ fib[1] = 1
            /\ fib[2] = 2
            /\ fib[3] = 3
            /\ fib[4] = 5
            /\ fib[5] = 8
            /\ fib[6] = 13
            /\ fib[7] = 21
            /\ fib[8] = 34
            /\ fib[9] = 55
            /\ fib[10] = 89

Spec == TestFib /\ [][TestNext]_<<x>>

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Thu Mar 15 10:56:10 CET 2018 by jensk
\* Created Thu Mar 15 10:26:44 CET 2018 by jensk
