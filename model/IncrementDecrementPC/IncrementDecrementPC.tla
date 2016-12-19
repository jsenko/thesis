----------------------- MODULE IncrementDecrementPC -------------------------
EXTENDS Naturals, TLC
(* CONSTANT N*)

(*
--algorithm IncDec {

  variables x = 0,
            N = 3

  process (Proc1 = 1)
    variable i, p;
  {   
    start:   i := 0;
      s01:   while (i <= N) {
      s02:     p := x;
      s03:     p := p + 1;
      s04:     x := p;
      s05:     i := i + 1;
             }          
  }
  
  process (Proc2 = 2)
    variable i, p;
  {
    start:   i := 0;
      s01:   while (i <= N) {
      s02:     p := x;
      s03:     p := p - 1;
      s04:     x := p;
      s05:     i := i + 1;
             }          
  }
} \* end algorithm
*)

-------------------------------------------------------------------

\* BEGIN TRANSLATION
\* Label start of process Proc1 at line 14 col 14 changed to start_
\* Label s01 of process Proc1 at line 15 col 14 changed to s01_
\* Label s02 of process Proc1 at line 16 col 16 changed to s02_
\* Label s03 of process Proc1 at line 17 col 16 changed to s03_
\* Label s04 of process Proc1 at line 18 col 16 changed to s04_
\* Label s05 of process Proc1 at line 19 col 16 changed to s05_
\* Process variable i of process Proc1 at line 12 col 14 changed to i_
\* Process variable p of process Proc1 at line 12 col 17 changed to p_
CONSTANT defaultInitValue
VARIABLES x, N, pc, i_, p_, i, p

vars == << x, N, pc, i_, p_, i, p >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 0
        /\ N = 3
        (* Process Proc1 *)
        /\ i_ = defaultInitValue
        /\ p_ = defaultInitValue
        (* Process Proc2 *)
        /\ i = defaultInitValue
        /\ p = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "start_"
                                        [] self = 2 -> "start"]

start_ == /\ pc[1] = "start_"
          /\ i_' = 0
          /\ pc' = [pc EXCEPT ![1] = "s01_"]
          /\ UNCHANGED << x, N, p_, i, p >>

s01_ == /\ pc[1] = "s01_"
        /\ IF i_ <= N
              THEN /\ pc' = [pc EXCEPT ![1] = "s02_"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED << x, N, i_, p_, i, p >>

s02_ == /\ pc[1] = "s02_"
        /\ p_' = x
        /\ pc' = [pc EXCEPT ![1] = "s03_"]
        /\ UNCHANGED << x, N, i_, i, p >>

s03_ == /\ pc[1] = "s03_"
        /\ p_' = p_ + 1
        /\ pc' = [pc EXCEPT ![1] = "s04_"]
        /\ UNCHANGED << x, N, i_, i, p >>

s04_ == /\ pc[1] = "s04_"
        /\ x' = p_
        /\ pc' = [pc EXCEPT ![1] = "s05_"]
        /\ UNCHANGED << N, i_, p_, i, p >>

s05_ == /\ pc[1] = "s05_"
        /\ i_' = i_ + 1
        /\ pc' = [pc EXCEPT ![1] = "s01_"]
        /\ UNCHANGED << x, N, p_, i, p >>

Proc1 == start_ \/ s01_ \/ s02_ \/ s03_ \/ s04_ \/ s05_

start == /\ pc[2] = "start"
         /\ i' = 0
         /\ pc' = [pc EXCEPT ![2] = "s01"]
         /\ UNCHANGED << x, N, i_, p_, p >>

s01 == /\ pc[2] = "s01"
       /\ IF i <= N
             THEN /\ pc' = [pc EXCEPT ![2] = "s02"]
             ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
       /\ UNCHANGED << x, N, i_, p_, i, p >>

s02 == /\ pc[2] = "s02"
       /\ p' = x
       /\ pc' = [pc EXCEPT ![2] = "s03"]
       /\ UNCHANGED << x, N, i_, p_, i >>

s03 == /\ pc[2] = "s03"
       /\ p' = p - 1
       /\ pc' = [pc EXCEPT ![2] = "s04"]
       /\ UNCHANGED << x, N, i_, p_, i >>

s04 == /\ pc[2] = "s04"
       /\ x' = p
       /\ pc' = [pc EXCEPT ![2] = "s05"]
       /\ UNCHANGED << N, i_, p_, i, p >>

s05 == /\ pc[2] = "s05"
       /\ i' = i + 1
       /\ pc' = [pc EXCEPT ![2] = "s01"]
       /\ UNCHANGED << x, N, i_, p_, p >>

Proc2 == start \/ s01 \/ s02 \/ s03 \/ s04 \/ s05

Next == Proc1 \/ Proc2
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) (* prevent stuttering forever *)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

-------------------------------------------------------------------

Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
