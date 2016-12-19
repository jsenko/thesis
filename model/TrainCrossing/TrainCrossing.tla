------------------ MODULE TrainCrossing ---------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLE Trains

---------------------------------------------------------------
Position == 1 .. 5

TypeInvariant == \A train \in Trains: train \in [pos: Position]

Init == Trains = {}
        
TrainAppears == Trains' = IF \E train \in Trains: train.pos = 0
                            THEN Trains
                            ELSE Trains \cup { [pos: 1] }
                            
(*TrainMoves(train) == Trains' = IF*) 
        
Next == TrainAppears


(*
Pos == 0 .. 5

Bool == {TRUE, FALSE}

XOR(a, b) == (a /\ \neg b) \/ (\neg a /\ b)

TypeInvariant == /\ track \in [Pos -> Bool]
                 /\ crossingOpen \in Bool

Init == /\ TypeInvariant
        /\ \A n \in Pos: track[n] = FALSE
        /\ crossingOpen = TRUE
        
TrainAppears == /\ track' = IF \neg (track[0] \/ track[1])
                      THEN [track EXCEPT ![0] = TRUE]
                      ELSE track
                
               

TrainMoves(n) == /\ track' = IF n < 5
                      THEN [track EXCEPT ![n] = FALSE, ![n + 1] = TRUE]
                      ELSE [track EXCEPT ![n] = FALSE]
               
        (*         
TrainsMove == \A n \in Pos: TrainMoves(n)
                
DetectEnter == /\ crossingOpen' = IF track[1] THEN FALSE ELSE crossingOpen
               

DetectLeave == /\ crossingOpen' = IF track[3] THEN TRUE ELSE crossingOpen
          *)     
        
Next == (TrainAppears /\ TrainsMove)(* /\ DetectEnter /\ DetectLeave*)
*)
Spec == Init
          /\ [][Next]_<<Trains>> 
          (*/\ WF_<<track, crossingOpen>>(TrainAppears) (* prevent stuttering forever *)
          /\ WF_<<track, crossingOpen>>(TrainsMove)
*)
---------------------------------------------------------------

 (*
C1 == [](track[3] => \neg crossingOpen)
*)
Correctness == TRUE

===============================================================
