------------------ MODULE HourClock ---------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLES hr
---------------------------------------------------------------

Init == hr \in 1 .. 12

Next == \/ (hr < 12 /\ hr' = hr + 1)
        \/ (hr = 12 /\ hr' = 1)

Spec == Init /\ [][Next]_<<hr>> /\ WF_<<hr>>(Next) (* prevent stuttering forever *)

---------------------------------------------------------------

(*The clock MUST show 1-12 hours on the display*) 
Corr1 == hr \geq 1 /\ hr \leq 12

(*The clock MUST not stop*)
Corr2 == ((hr = 12) ~> (hr = 1)) /\ \A n \in 1 .. 11: (hr = n) ~> (hr = n + 1)

(*Corr3 == (hr = 12) ~> (hr = 1)*) 

Corr == Corr1 /\ Corr2 (*/\ Corr3*)

===============================================================
