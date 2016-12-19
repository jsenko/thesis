----------------------- MODULE IncrementDecrementWithNetwork -------------------------
EXTENDS UnreliableNetwork, Integers
CONSTANT N

(*
--algorithm IncDec {

  variables net

  process (ProcInc = 1)
    variable i;
  {   
    start:   i := 0;
      s01:   while (i <= N) {
     send:     skip; \* send +1
      s02:     i := i + 1;
             }          
  }
  
  process (ProcDec = 2)
    variable i;
  {   
    start:   i := 0;
      s01:   while (i <= N) {
     send:     skip; \* send -1
      s02:     i := i + 1;
             }          
  }
  
  process (Counter = 3)
    variable r, total;
  {
     start:  r := 0;
       s01:  total := 0;
      loop:  while (TRUE) {
   receive:    skip; \* receive packet
   hasData:    if(TRUE) {
       s02:      total := total + r;
               }
             }          
  }
} \* end algorithm
*)

-------------------------------------------------------------------

\* BEGIN TRANSLATION
\* Label start of process ProcInc at line 13 col 14 changed to start_
\* Label s01 of process ProcInc at line 14 col 14 changed to s01_
\* Label send of process ProcInc at line 15 col 16 changed to send_
\* Label s02 of process ProcInc at line 16 col 16 changed to s02_
\* Label start of process ProcDec at line 23 col 14 changed to start_P
\* Label s01 of process ProcDec at line 24 col 14 changed to s01_P
\* Label s02 of process ProcDec at line 26 col 16 changed to s02_P
\* Process variable i of process ProcInc at line 11 col 14 changed to i_
CONSTANT defaultInitValue
VARIABLES net, pc, i_, i, r, total

vars == << net, pc, i_, i, r, total >>

ProcSet == {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ NInit(net)
        (* Process ProcInc *)
        /\ i_ = defaultInitValue
        (* Process ProcDec *)
        /\ i = defaultInitValue
        (* Process Counter *)
        /\ r = defaultInitValue
        /\ total = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "start_"
                                        [] self = 2 -> "start_P"
                                        [] self = 3 -> "start"]

start_ == /\ pc[1] = "start_"
          /\ i_' = 0
          /\ pc' = [pc EXCEPT ![1] = "s01_"]
          /\ UNCHANGED << net, i, r, total >>

s01_ == /\ pc[1] = "s01_"
        /\ IF i_ <= N
              THEN /\ pc' = [pc EXCEPT ![1] = "send_"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << net, i_, i, r, total >>

send_ == /\ pc[1] = "send_"
         /\ SendData(1, 3, 1, net, net')
         /\ pc' = [pc EXCEPT ![1] = "s02_"]
         /\ UNCHANGED << i_, i, r, total >>

s02_ == /\ pc[1] = "s02_"
        /\ i_' = i_ + 1
        /\ pc' = [pc EXCEPT ![1] = "s01_"]
        /\ UNCHANGED << net, i, r, total >>

ProcInc == start_ \/ s01_ \/ send_ \/ s02_

start_P == /\ pc[2] = "start_P"
           /\ i' = 0
           /\ pc' = [pc EXCEPT ![2] = "s01_P"]
           /\ UNCHANGED << net, i_, r, total >>

s01_P == /\ pc[2] = "s01_P"
         /\ IF i <= N
               THEN /\ pc' = [pc EXCEPT ![2] = "send"]
               ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
         /\ UNCHANGED << net, i_, i, r, total >>

send == /\ pc[2] = "send"
        /\ SendData(2, 3, -1, net, net')
        /\ pc' = [pc EXCEPT ![2] = "s02_P"]
        /\ UNCHANGED << i_, i, r, total >>

s02_P == /\ pc[2] = "s02_P"
         /\ i' = i + 1
         /\ pc' = [pc EXCEPT ![2] = "s01_P"]
         /\ UNCHANGED << net, i_, r, total >>

ProcDec == start_P \/ s01_P \/ send \/ s02_P

start == /\ pc[3] = "start"
         /\ r' = 0
         /\ pc' = [pc EXCEPT ![3] = "s01"]
         /\ UNCHANGED << net, i_, i, total >>

s01 == /\ pc[3] = "s01"
       /\ total' = 0
       /\ pc' = [pc EXCEPT ![3] = "loop"]
       /\ UNCHANGED << net, i_, i, r >>

loop == /\ pc[3] = "loop"
        /\ pc' = [pc EXCEPT ![3] = "receive"]
        /\ UNCHANGED << net, i_, i, r, total >>

receive == /\ pc[3] = "receive"
           /\ ReceiveData(3, r', net, net')
           /\ pc' = [pc EXCEPT ![3] = "hasData"]
           /\ UNCHANGED << i_, i, total >>

hasData == /\ pc[3] = "hasData"
           /\ IF r # NoData
                 THEN /\ pc' = [pc EXCEPT ![3] = "s02"]
                 ELSE /\ pc' = [pc EXCEPT ![3] = "loop"]
           /\ UNCHANGED << net, i_, i, r, total >>

s02 == /\ pc[3] = "s02"
       /\ total' = total + r
       /\ pc' = [pc EXCEPT ![3] = "loop"]
       /\ UNCHANGED << net, i_, i, r >>

Counter == start \/ s01 \/ loop \/ receive \/ hasData \/ s02

Next == ProcInc \/ ProcDec \/ Counter
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ /\ WF_vars(Next) (* prevent stuttering forever *)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

-------------------------------------------------------------------

C1 == []((pc[1] = "Done" /\ pc[2] = "Done") => <>(total = 0))

Correctness == C1\*[]((pc[1] = "Done" /\ pc[2] = "Done") => <>(total = 0))

===================================================================
