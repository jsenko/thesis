----------------------- MODULE HourClockPC -------------------------
EXTENDS Integers, TLC  \* Only need Naturals unless doing the assert with "Int"

\* Based on the HourClock TLA+ example in Ch. 2 of "Specifying Systems"

(*
--algorithm HourClock {
  variables 
    hr \in 1..12;  \* hr is a randomly chosen integer in range 1..12
  {
    while (TRUE) {
      hr := (hr % 12) + 1;
      print <<hr>>;
      \* assert (hr \in Int) /\ (hr > 0) /\ (hr <= 12);
      assert (\E n \in 1..12: hr = n);
    };
  } \* end master code block
} \* end algorithm
*)

\* BEGIN TRANSLATION
VARIABLE hr

vars == << hr >>

Init == (* Global variables *)
        /\ hr \in 1..12

Next == /\ hr' = (hr % 12) + 1
        /\ PrintT(<<hr'>>)
        /\ Assert((\E n \in 1..12: hr' = n), 
                  "Failure of assertion at line 15, column 7.")

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

------------------------------------------------------------------

C1 == [][(hr \geq 1) /\ (hr \leq 12)]_<<vars>> 

Correctness == C1

==================================================================
