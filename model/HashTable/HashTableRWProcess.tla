----------------------- MODULE HashTableRWProcess -------------------------
EXTENDS HashTable

(*
--algorithm HashTableRWProcess
{
  variables k = 0, v = 0, x = 0, y = 0;

  process (ProcId = 1)
    \* variable i, p;
  {   
    start:   while (TRUE) {               
      s01:     with (k0 \in KeyDomain; v0 \in ValueDomain) {
                  k := k0;
                  v := v0;
               };
    write:         assert Write(k, x);
      foo:         skip;
     read:         assert Read(k, y);
     test:         skip;              
             }          
  }
} \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES k, v, x, y, pc

vars == << k, v, x, y, pc, data >>

ProcSet == {1}

Init == (* Global variables *)
        /\ k = 0
        /\ v = 0
        /\ x = 0
        /\ y = 0
        /\ pc = [self \in ProcSet |-> "start"]
        /\ HT_Init

start == /\ pc[1] = "start"
         /\ pc' = [pc EXCEPT ![1] = "s01"]
         /\ UNCHANGED << k, v, x, y >>
         /\ UNCHANGED data

s01 == /\ pc[1] = "s01"
       /\ \E k0 \in KeyDomain:
            \E v0 \in ValueDomain:
              /\ k' = k0
              /\ v' = v0
       /\ pc' = [pc EXCEPT ![1] = "write"]
       /\ UNCHANGED << x, y >>
       /\ UNCHANGED data

write == /\ pc[1] = "write"
         /\ Write(k, x)
         /\ pc' = [pc EXCEPT ![1] = "foo"]
         /\ UNCHANGED << k, v, x, y >>

foo == /\ pc[1] = "foo"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "read"]
       /\ UNCHANGED << k, v, x, y >>
       /\ UNCHANGED data

read == /\ pc[1] = "read"
        /\ Read(k, y')
        /\ pc' = [pc EXCEPT ![1] = "test"]
        /\ UNCHANGED << k, v, x, y >>
        /\ UNCHANGED data

test == /\ pc[1] = "test"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![1] = "start"]
        /\ UNCHANGED << k, v, x, y >>
        /\ UNCHANGED data

ProcId == start \/ s01 \/ write \/ foo \/ read \/ test

Next == ProcId

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-------------------------------------------------------------------

-------------------------------------------------------------------

\* during 'test' step, readval = written val
Correctness == [](pc[1] = "test" => x = y)

===================================================================
