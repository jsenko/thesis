------------------ MODULE FairSemaphore ---------------------

CONSTANTS permitCount\*,
          \*processIds

---------------------------------------------------------------

LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

_Contains(s, e) == \E i \in DOMAIN s: s[i] = e

Init(this) == this = [p |-> permitCount, q |-> <<>>]

\* this is true iff the acquire is successful,
\* process does not have to wait indefinitely,

TryWait(self, ret_success, this, this_next) ==
  IF this.p > 0
  THEN IF _Contains(this.q, self)
       THEN IF Head(this.q) = self
            THEN /\ ret_success = TRUE
                 /\ this_next = [this EXCEPT !.p = this.p - 1, !.q = Tail(this.q)]
            ELSE /\ ret_success = FALSE
                 /\ this_next = this            
       ELSE IF Len(this.q) = 0
            THEN /\ ret_success = TRUE
                 /\ this_next = [this EXCEPT !.p = this.p - 1]
            ELSE /\ ret_success = FALSE
                 /\ this_next = [this EXCEPT !.q = Append(this.q, self)]
   ELSE IF _Contains(this.q, self)
        THEN /\ ret_success = FALSE
             /\ this_next = this            
        ELSE /\ ret_success = FALSE
             /\ this_next = [this EXCEPT !.q = Append(this.q, self)]


\* this is not a safe semaphore, therefore you may signal even if
\* you did not succesfully waited, also you may signal if there is no one waiting
Signal(this, this_next) == IF this.p < permitCount
                           THEN this_next = [this EXCEPT !.p = this.p + 1]
                           ELSE this_next = this
                           
---------------------------------------------------------------


CI1(this) == this.p >= 0 /\ this.p <= permitCount 

(* e.g. we do not use [] here, this must be true only after Init *)
CorrectnessInvariant(this) == CI1(this)

===============================================================
