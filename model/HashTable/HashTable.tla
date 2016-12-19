----------------------- MODULE HashTable -------------------------
EXTENDS Naturals, TLC, HashTableInterface
(* CONSTANT N*)
VARIABLES data\*, ctl 
(*

*)

-------------------------------------------------------------------

HT_Init == /\ data = [k \in KeyDomain |-> None]
         \*/\ ctl = [p \in Proc |-> "rdy"] 
         \*/\ buf = [p \in Proc |-> NoVal] 
         \*/\ memInt \in InitMemInt


TypeInvariant == /\ data \in [KeyDomain -> (ValueDomain \cup None)]
  

Read(key, ret) == /\ ret = data[key]
                  /\ UNCHANGED data 

Write(key, val) == /\ data' = [data EXCEPT ![key] = val]
                    
\*INext == \E p \in Proc: Req(p) \/ Do(p) \/ Rsp(p)

-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
