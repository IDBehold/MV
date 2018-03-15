---------------------------- MODULE PlusCalLIFO ----------------------------
\* TLA+
EXTENDS Naturals, Sequences, TLC
CONSTANT QueueSize, Message 

\*PlusCal
(*
--algorithm FIFO {
  variables
    inchan \in [val : Message, rdy : {0,1}, ack : {0,1}],
                
    outchan \in [val : Message, rdy : {0,1}, ack : {0,1}];
                 
    q = <<>>; 

\****************************************************************************************************************
\* Added a queueSize constant to the typeinvariants, so that the buffer had a finite number of elements
\****************************************************************************************************************
  macro CheckInvariants(chan) {
    assert (chan.val \in Message); 
    assert (chan.rdy \in {0,1}); 
    assert (chan.ack \in {0,1});
    assert (q \in Seq(Message));
    assert (QueueSize > 0);
    assert (QueueSize \in Nat);
    assert (Len(q) <= QueueSize);
  }

\****************************************************************************************************************
\* Changed sender send to only be applicable when the current length of the queue is lower than the maximum queue size
\****************************************************************************************************************
  process (SSend = "ssend")
    variable oldrdy;
  {    
    ss0:  while (TRUE) {
    ss1:    await inchan.rdy = inchan.ack;
    ss2:    oldrdy := inchan.rdy;
            inchan.rdy := 1 - inchan.rdy;
            CheckInvariants(inchan);
            assert (inchan.rdy # oldrdy);
            assert (inchan.rdy # inchan.ack);
          }    
    
  }; \* end process SSend

\****************************************************************************************************************
\* Receive message from channel `in'.
\* change the queue to contain a concatination of the new value from the in channel and the original queue
\****************************************************************************************************************
  process (BufRcv = "bufrcv")
        variable oldack;
  {
    br0:  while (TRUE) {
    br1:    await inchan.rdy # inchan.ack /\ Len(q) < QueueSize;
    br2:    oldack := inchan.ack;
            inchan.ack := 1 - inchan.ack;
            q := <<inchan.val>> \o q;
            CheckInvariants(inchan);
            assert (inchan.ack # oldack);
            assert (inchan.rdy = inchan.ack);
          }       
  }; \* end process BufRecv

  process (BufSend = "bufsend")
    variable oldrdy, rval;
  {    
    bs0:  while (TRUE) {
    bs1:    await outchan.rdy = outchan.ack  /\ q # << >>;
    bs2:    oldrdy := outchan.rdy;
            outchan.rdy := 1 - outchan.rdy;
            rval := Head(q);
            q := Tail(q);
    
            CheckInvariants(outchan);
            assert (outchan.rdy # oldrdy);
            assert (outchan.rdy # outchan.ack);
            
            
    bs3:    outchan.val := rval; 
    \*********************************************************************************************
    \*Hack to get value into outchan. Not able to do it in bs2. outchan.val := Head(q) requires its own label and therefor couldn't be done in bs2.
    \********************************************************************************************
          }    
    
  }; \* end process BufSend


  process (RRcv = "rrcv")
        variable oldack;
  {
    rr0:  while (TRUE) {
    rr1:    await outchan.rdy # outchan.ack;
    rr2:    oldack := outchan.ack;
            outchan.ack := 1 - outchan.ack;
            CheckInvariants(outchan);
            assert (outchan.ack # oldack);
            assert (outchan.rdy = outchan.ack);
          }       
  }; \* end process RRecv

}
*)
\* BEGIN TRANSLATION
\* Process variable oldrdy of process SSend at line 33 col 14 changed to oldrdy_
\* Process variable oldack of process BufRcv at line 51 col 18 changed to oldack_
CONSTANT defaultInitValue
VARIABLES inchan, outchan, q, pc, oldrdy_, oldack_, oldrdy, rval, oldack

vars == << inchan, outchan, q, pc, oldrdy_, oldack_, oldrdy, rval, oldack >>

ProcSet == {"ssend"} \cup {"bufrcv"} \cup {"bufsend"} \cup {"rrcv"}

Init == (* Global variables *)
        /\ inchan \in [val : Message, rdy : {0,1}, ack : {0,1}]
        /\ outchan \in [val : Message, rdy : {0,1}, ack : {0,1}]
        /\ q = <<>>
        (* Process SSend *)
        /\ oldrdy_ = defaultInitValue
        (* Process BufRcv *)
        /\ oldack_ = defaultInitValue
        (* Process BufSend *)
        /\ oldrdy = defaultInitValue
        /\ rval = defaultInitValue
        (* Process RRcv *)
        /\ oldack = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "ssend" -> "ss0"
                                        [] self = "bufrcv" -> "br0"
                                        [] self = "bufsend" -> "bs0"
                                        [] self = "rrcv" -> "rr0"]

ss0 == /\ pc["ssend"] = "ss0"
       /\ pc' = [pc EXCEPT !["ssend"] = "ss1"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

ss1 == /\ pc["ssend"] = "ss1"
       /\ inchan.rdy = inchan.ack
       /\ pc' = [pc EXCEPT !["ssend"] = "ss2"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

ss2 == /\ pc["ssend"] = "ss2"
       /\ oldrdy_' = inchan.rdy
       /\ inchan' = [inchan EXCEPT !.rdy = 1 - inchan.rdy]
       /\ Assert((inchan'.val \in Message), 
                 "Failure of assertion at line 20, column 5 of macro called at line 39, column 13.")
       /\ Assert((inchan'.rdy \in {0,1}), 
                 "Failure of assertion at line 21, column 5 of macro called at line 39, column 13.")
       /\ Assert((inchan'.ack \in {0,1}), 
                 "Failure of assertion at line 22, column 5 of macro called at line 39, column 13.")
       /\ Assert((q \in Seq(Message)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 39, column 13.")
       /\ Assert((QueueSize > 0), 
                 "Failure of assertion at line 24, column 5 of macro called at line 39, column 13.")
       /\ Assert((QueueSize \in Nat), 
                 "Failure of assertion at line 25, column 5 of macro called at line 39, column 13.")
       /\ Assert((Len(q) <= QueueSize), 
                 "Failure of assertion at line 26, column 5 of macro called at line 39, column 13.")
       /\ Assert((inchan'.rdy # oldrdy_'), 
                 "Failure of assertion at line 40, column 13.")
       /\ Assert((inchan'.rdy # inchan'.ack), 
                 "Failure of assertion at line 41, column 13.")
       /\ pc' = [pc EXCEPT !["ssend"] = "ss0"]
       /\ UNCHANGED << outchan, q, oldack_, oldrdy, rval, oldack >>

SSend == ss0 \/ ss1 \/ ss2

br0 == /\ pc["bufrcv"] = "br0"
       /\ pc' = [pc EXCEPT !["bufrcv"] = "br1"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

br1 == /\ pc["bufrcv"] = "br1"
       /\ inchan.rdy # inchan.ack /\ Len(q) < QueueSize
       /\ pc' = [pc EXCEPT !["bufrcv"] = "br2"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

br2 == /\ pc["bufrcv"] = "br2"
       /\ oldack_' = inchan.ack
       /\ inchan' = [inchan EXCEPT !.ack = 1 - inchan.ack]
       /\ q' = <<inchan'.val>> \o q
       /\ Assert((inchan'.val \in Message), 
                 "Failure of assertion at line 20, column 5 of macro called at line 58, column 13.")
       /\ Assert((inchan'.rdy \in {0,1}), 
                 "Failure of assertion at line 21, column 5 of macro called at line 58, column 13.")
       /\ Assert((inchan'.ack \in {0,1}), 
                 "Failure of assertion at line 22, column 5 of macro called at line 58, column 13.")
       /\ Assert((q' \in Seq(Message)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 58, column 13.")
       /\ Assert((QueueSize > 0), 
                 "Failure of assertion at line 24, column 5 of macro called at line 58, column 13.")
       /\ Assert((QueueSize \in Nat), 
                 "Failure of assertion at line 25, column 5 of macro called at line 58, column 13.")
       /\ Assert((Len(q') <= QueueSize), 
                 "Failure of assertion at line 26, column 5 of macro called at line 58, column 13.")
       /\ Assert((inchan'.ack # oldack_'), 
                 "Failure of assertion at line 59, column 13.")
       /\ Assert((inchan'.rdy = inchan'.ack), 
                 "Failure of assertion at line 60, column 13.")
       /\ pc' = [pc EXCEPT !["bufrcv"] = "br0"]
       /\ UNCHANGED << outchan, oldrdy_, oldrdy, rval, oldack >>

BufRcv == br0 \/ br1 \/ br2

bs0 == /\ pc["bufsend"] = "bs0"
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs1"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

bs1 == /\ pc["bufsend"] = "bs1"
       /\ outchan.rdy = outchan.ack  /\ q # << >>
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs2"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

bs2 == /\ pc["bufsend"] = "bs2"
       /\ oldrdy' = outchan.rdy
       /\ outchan' = [outchan EXCEPT !.rdy = 1 - outchan.rdy]
       /\ rval' = Head(q)
       /\ q' = Tail(q)
       /\ Assert((outchan'.val \in Message), 
                 "Failure of assertion at line 20, column 5 of macro called at line 74, column 13.")
       /\ Assert((outchan'.rdy \in {0,1}), 
                 "Failure of assertion at line 21, column 5 of macro called at line 74, column 13.")
       /\ Assert((outchan'.ack \in {0,1}), 
                 "Failure of assertion at line 22, column 5 of macro called at line 74, column 13.")
       /\ Assert((q' \in Seq(Message)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 74, column 13.")
       /\ Assert((QueueSize > 0), 
                 "Failure of assertion at line 24, column 5 of macro called at line 74, column 13.")
       /\ Assert((QueueSize \in Nat), 
                 "Failure of assertion at line 25, column 5 of macro called at line 74, column 13.")
       /\ Assert((Len(q') <= QueueSize), 
                 "Failure of assertion at line 26, column 5 of macro called at line 74, column 13.")
       /\ Assert((outchan'.rdy # oldrdy'), 
                 "Failure of assertion at line 75, column 13.")
       /\ Assert((outchan'.rdy # outchan'.ack), 
                 "Failure of assertion at line 76, column 13.")
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs3"]
       /\ UNCHANGED << inchan, oldrdy_, oldack_, oldack >>

bs3 == /\ pc["bufsend"] = "bs3"
       /\ outchan' = [outchan EXCEPT !.val = rval]
       /\ pc' = [pc EXCEPT !["bufsend"] = "bs0"]
       /\ UNCHANGED << inchan, q, oldrdy_, oldack_, oldrdy, rval, oldack >>

BufSend == bs0 \/ bs1 \/ bs2 \/ bs3

rr0 == /\ pc["rrcv"] = "rr0"
       /\ pc' = [pc EXCEPT !["rrcv"] = "rr1"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

rr1 == /\ pc["rrcv"] = "rr1"
       /\ outchan.rdy # outchan.ack
       /\ pc' = [pc EXCEPT !["rrcv"] = "rr2"]
       /\ UNCHANGED << inchan, outchan, q, oldrdy_, oldack_, oldrdy, rval, 
                       oldack >>

rr2 == /\ pc["rrcv"] = "rr2"
       /\ oldack' = outchan.ack
       /\ outchan' = [outchan EXCEPT !.ack = 1 - outchan.ack]
       /\ Assert((outchan'.val \in Message), 
                 "Failure of assertion at line 20, column 5 of macro called at line 95, column 13.")
       /\ Assert((outchan'.rdy \in {0,1}), 
                 "Failure of assertion at line 21, column 5 of macro called at line 95, column 13.")
       /\ Assert((outchan'.ack \in {0,1}), 
                 "Failure of assertion at line 22, column 5 of macro called at line 95, column 13.")
       /\ Assert((q \in Seq(Message)), 
                 "Failure of assertion at line 23, column 5 of macro called at line 95, column 13.")
       /\ Assert((QueueSize > 0), 
                 "Failure of assertion at line 24, column 5 of macro called at line 95, column 13.")
       /\ Assert((QueueSize \in Nat), 
                 "Failure of assertion at line 25, column 5 of macro called at line 95, column 13.")
       /\ Assert((Len(q) <= QueueSize), 
                 "Failure of assertion at line 26, column 5 of macro called at line 95, column 13.")
       /\ Assert((outchan'.ack # oldack'), 
                 "Failure of assertion at line 96, column 13.")
       /\ Assert((outchan'.rdy = outchan'.ack), 
                 "Failure of assertion at line 97, column 13.")
       /\ pc' = [pc EXCEPT !["rrcv"] = "rr0"]
       /\ UNCHANGED << inchan, q, oldrdy_, oldack_, oldrdy, rval >>

RRcv == rr0 \/ rr1 \/ rr2

Next == SSend \/ BufRcv \/ BufSend \/ RRcv

Spec == Init /\ [][Next]_vars

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Wed Mar 07 11:38:01 CET 2018 by jacob
\* Created Thu Mar 01 11:47:28 CET 2018 by jacob
