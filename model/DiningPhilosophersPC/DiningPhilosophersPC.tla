----------------------- MODULE DiningPhilosophersPC -------------------------
EXTENDS Integers, TLC
(* CONSTANT N*)

N == 5
PhilosopherId == 0 .. (N - 1)
None == -1
\*ForkOwner == PhilosopherId \cup { None }

(*
--algorithm DiningPhilosophers {

  variables forks = [i \in PhilosopherId |-> None]; \* Forks available

  process (Philosopher \in PhilosopherId)
    \* variable i, p;
  {   
    start:   while (TRUE) {
               \* Try picking right
      tryR:    if (forks[self] = None) { 
                 forks[self] := self;
               };
               \* Try picking left
      tryL:    if (forks[(self - 1) % N] = None) {
                   forks[(self - 1) % N] := self;
               };
               \* Try eating
      tryEat:         if (forks[self] = self /\ forks[(self - 1) % N] = self) {
      eat:         skip;
                   \* Put down both
      putBackR:    forks[self] := None;
      putBackL:    forks[(self - 1) % N] := None;
                 
      
               }          
             }          
  }
} \* end algorithm
*)

-------------------------------------------------------------------

\* BEGIN TRANSLATION
VARIABLES forks, pc

vars == << forks, pc >>

ProcSet == (PhilosopherId)

Init == (* Global variables *)
        /\ forks = [i \in PhilosopherId |-> None]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "tryR"]
               /\ forks' = forks

tryR(self) == /\ pc[self] = "tryR"
              /\ IF forks[self] = None
                    THEN /\ forks' = [forks EXCEPT ![self] = self]
                    ELSE /\ TRUE
                         /\ forks' = forks
              /\ pc' = [pc EXCEPT ![self] = "tryL"]

tryL(self) == /\ pc[self] = "tryL"
              /\ IF forks[(self - 1) % N] = None
                    THEN /\ forks' = [forks EXCEPT ![(self - 1) % N] = self]
                    ELSE /\ TRUE
                         /\ forks' = forks
              /\ pc' = [pc EXCEPT ![self] = "tryEat"]

tryEat(self) == /\ pc[self] = "tryEat"
                /\ IF forks[self] = self /\ forks[(self - 1) % N] = self
                      THEN /\ pc' = [pc EXCEPT ![self] = "eat"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
                /\ forks' = forks

eat(self) == /\ pc[self] = "eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "putBackR"]
             /\ forks' = forks

putBackR(self) == /\ pc[self] = "putBackR"
                  /\ forks' = [forks EXCEPT ![self] = None]
                  /\ pc' = [pc EXCEPT ![self] = "putBackL"]

putBackL(self) == /\ pc[self] = "putBackL"
                  /\ forks' = [forks EXCEPT ![(self - 1) % N] = None]
                  /\ pc' = [pc EXCEPT ![self] = "start"]

Philosopher(self) == start(self) \/ tryR(self) \/ tryL(self)
                        \/ tryEat(self) \/ eat(self) \/ putBackR(self)
                        \/ putBackL(self)

Next == (\E self \in PhilosopherId: Philosopher(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-------------------------------------------------------------------
\* /\ WF_vars(Next)
\* Eventually someone eats (no deadlock)
Correctness == <>(\E self \in PhilosopherId: pc[self] = "eat")

===================================================================
