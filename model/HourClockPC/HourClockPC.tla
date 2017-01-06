----------------------- MODULE HourClockPC -------------------------
EXTENDS Integers

\* Based on the HourClock TLA+ example in Ch. 2 of "Specifying Systems"

(*
--algorithm HourClock {
  variables 
    hr \in 1..12;  \* hr is a randomly chosen integer in range 1..12
  {
loop:  while(TRUE) {
s01:     hr := hr + 1;
cond:    if(hr > 12) {
s02:       hr := 1;
         } 
       }
  }
} 
*)

\* BEGIN TRANSLATION
VARIABLES hr, pc

vars == << hr, pc >>

Init == (* Global variables *)
        /\ hr \in 1..12
        /\ pc = "loop"

loop == /\ pc = "loop"
        /\ pc' = "s01"
        /\ hr' = hr

s01 == /\ pc = "s01"
       /\ hr' = hr + 1
       /\ pc' = "cond"

cond == /\ pc = "cond"
        /\ IF hr > 12
              THEN /\ pc' = "s02"
              ELSE /\ pc' = "loop"
        /\ hr' = hr

s02 == /\ pc = "s02"
       /\ hr' = 1
       /\ pc' = "loop"

Next == loop \/ s01 \/ cond \/ s02

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

------------------------------------------------------------------

C1 == [][(hr \geq 1) /\ (hr \leq 12)]_<<vars>> 

Correctness == C1

==================================================================
