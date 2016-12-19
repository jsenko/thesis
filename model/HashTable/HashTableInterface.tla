----------------------- MODULE HashTableInterface -------------------------
EXTENDS Naturals, TLC

CONSTANT KeyDomain,
         ValueDomain
 \*        None,
       \*  Read(_, _),
       \*  Write(_, _)
         

(*
*)

-------------------------------------------------------------------

Ops ==         [op : {"Read"}, key: KeyDomain, ret: ValueDomain] 
          \cup [op : {"Write"}, key: KeyDomain, val: ValueDomain]
          \cup [op : {"Delete"}, key: KeyDomain]

None == CHOOSE x : x \notin (KeyDomain \cup ValueDomain)

-------------------------------------------------------------------

\*Correctness == []((pc[1] = "Done" /\ pc[2] = "Done") => x = 0)

===================================================================
