------------------ MODULE Semaphore ---------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS permitCount\*,
          \*processIds

---------------------------------------------------------------

Init(sem) == sem = permitCount

\* this is true iff the acquire is successful,
\* process does not have to wait indefinitely,
TryWait(ret_success, sem, sem_next) == IF sem > 0
                                           THEN sem_next = sem - 1 /\ ret_success = TRUE
                                           ELSE sem_next = sem  /\ ret_success = FALSE

\* this is not a safe semaphore, therefore you may signal even if
\* you did not succesfully waited, also you may signal if there is no one waiting
Signal(sem, sem_next) == IF sem < permitCount
                           THEN sem_next = sem + 1
                           ELSE sem_next = sem
                           
---------------------------------------------------------------

(* This impl does not allow release by another process, lets call it "safe" semaphore
---------------------------------------------------------------

Init(sem, sem_next) == sem_next = {} 

Wait_try(self, sem, sem_next) == /\ self \notin sem
                                    /\ Cardinality(sem) < permitCount
                                    /\ sem_next = sem \union { self }

Signal(self, sem, sem_next) == sem_next = sem \ { self }  
---------------------------------------------------------------
*)


(**) 
C1 == TRUE

Corr == C1 /\ C1

===============================================================
