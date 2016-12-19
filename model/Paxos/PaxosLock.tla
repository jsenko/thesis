----------------------- MODULE Paxos -------------------------
EXTENDS Naturals
CONSTANT ReadersCount,
         WritersCount,
         MaxSeq
         
Readers == 1 .. ReadersCount
Writers == (ReadersCount + 1) .. (ReadersCount + WritersCount)

Ops == {"propose"}

Vals == BOOLEAN

Protocol == [op: Ops, seq: 1..MaxSeq (*Must be final*), val: Vals]

NodeIds == {1, 2, 3}

LeaderNodeId == 1

netInstance == INSTANCE UnreliableNetwork WITH
                   AddressSpace <- NodeIds,
                   DataSpace <- Protocol
                   


(*
 Each process will read the shared value, or write 
 lock status is what the majority agrees with!
 
 majority must agree on:
    lock to current user (lock is free)
    unlock!
    if the current user has the lock + optional fairness
    -> implementing reader writer
    
 to ensure liveness:
   -ping/pong messages from coordinator who is responsible to keep track of
    views and is able to change group size, this is probably not possible,
    to verify concurrently
     
--algorithm alg {

  variables net = {}

  process (Proc \in NodeIds)
    variable data, seq, val, prop, highestAgreedProp;
  {   
    start:   while(TRUE) {
               skip; \* Receive(self, data, net, net_next)
               
               \*
               if(IsLeader(self)) {                
                 with(x \in Vals) { prop := x; };
                 responses = {}
                 \* Broadcast("propose", seq, x) 
                 response :=  \*wait, must succeed -> majority must respond, else?
                 if(timeout \/ MajorityAgreed(response)) {
                   send accept request with prop                                                    
                 } else {
                   do something else
                 }
               
                 
               if(data.op = "propose") {
                 if(resp.seq < highestAgreedSeq)
                    reject;
                 else
                    accept
                    highestAgreedSeq := resp.seq
               } 
               
               
               if(data.op = "accept") {
               
                 if(agrees and seq=highestagreedprop) {
                   response accept to leader 
                 }
               }
               
               if(data.op = "agree_to_prop") {
               }
               
               if(data.op = "reject_prop") {
               }
                             
                      
               if(data.op = "accept_request") {
               }
               
               \* Only one lader op may be in progress
               if(inProgressLock ok) {
                 
               }
             } 
               
               
                    
  }
  
} \* end algorithm
*)

-------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES net, seq, val, prop

vars == << net, seq, val, prop >>

ProcSet == (NodeIds)

Init == (* Global variables *)
        /\ net = {}
        (* Process Proc *)
        /\ seq = [self \in NodeIds |-> defaultInitValue]
        /\ val = [self \in NodeIds |-> defaultInitValue]
        /\ prop = [self \in NodeIds |-> defaultInitValue]

Proc(self) == /\ IF self = LeaderNodeId
                    THEN /\ TRUE
                    ELSE /\ TRUE
              /\ \E x \in Vals:
                   prop' = [prop EXCEPT ![self] = x]
              /\ UNCHANGED << net, seq, val >>

Next == (\E self \in NodeIds: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-------------------------------------------------------------------


(*
           
Fairness == /\ \A self \in Readers: WF_vars(Reader(self))
            /\ \A self \in Writers: WF_vars(Writer(self))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Fairness (* each process must be able to progress *)
(* TODO WF conjuction rule*)
*)






ReadSection == "s09"

WriteSection == "s17"

StartLabels == {"StartR", "StartL"}
(*
C1 == [](\A wr \in Writers: (pc[wr] = WriteSection) =>
                 /\ (\neg \E wr2 \in Writers \ { wr }: pc[wr2] = WriteSection) 
                 /\ (\neg \E r \in Readers: pc[r] = ReadSection)) 

C2 == [](\E r \in Readers: (pc[r] = ReadSection) =>
                 /\ (\neg \E wr \in Writers: pc[wr] = WriteSection))
                 
C3 == [](wInstance!CorrectnessInvariant(w) /\ mutexInstance!CorrectnessInvariant(mutex))
                  
Correctness == C1 /\ C2 /\ C3

L1 == \A wr \in Writers: []<>(pc[wr] = WriteSection)

L2 == \A r \in Readers: []<>(pc[r] = ReadSection)

Liveness == L1 /\ L2
*)
===================================================================
