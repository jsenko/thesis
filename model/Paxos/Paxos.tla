----------------------- MODULE Paxos -------------------------
EXTENDS Naturals
CONSTANT ReadersCount,
         WritersCount,
         MaxSeq
         
Readers == 1 .. ReadersCount
Writers == (ReadersCount + 1) .. (ReadersCount + WritersCount)

LOCAL INSTANCE FiniteSets

Vals == BOOLEAN



NodeIds == {1, 2, 3}

LeaderNodeId == 1



States == {
            \*"init",
            "propose",
            "waiting_for_proposal_responses",
            "waiting_for_accept_responses",
            "evaluate_proposal_responses",
            "evaluate_accept_responses",
            "done"
          }
          
Ops == {
         "propose",
         "accept_proposal",
         "reject_proposal"
       }


Protocol == [op: Ops, seq: 1..MaxSeq (*Must be final*), val: Vals]


netInstance == INSTANCE UnreliableNetwork WITH
                   AddressSpace <- NodeIds,
                   DataSpace <- Protocol

None == "None" \*CHOOSE x \notin Vals

DefaultT == 10

(*

*)

_Majority(positive, negative, responses, ret, ret_next) ==
  \E aSet, rSet \in responses:
    /\ aSet \in SUBSET responses
    /\ rSet \in SUBSET responses
    /\ responses = aSet \union rSet
    /\ \A a \in aSet: a.op = positive
    /\ \A r \in rSet: r.op = negative
    /\ ret_next = (Cardinality(aSet) > Cardinality(rSet))



MajorityAgrees(responses, ret, ret_next) ==
  _Majority("accept_proposal", "reject_proposal", responses, ret, ret_next)


MajorityAccepts(responses, ret, ret_next) ==
  _Majority("accept", "reject", responses, ret, ret_next)



_HighestSeqProposal(op, responses, ret, ret_next) ==
  IF \E r \in responses: r.op = op
  THEN \E r \in responses:
    /\ r.op = op
    /\ \A other \in (responses \ r): r.seq >= other
    /\ ret_next = r 
  ELSE ret_next = None
  

HighestSeqAcceptProposal(responses, ret, ret_next) ==
  _HighestSeqProposal("accept_proposal", responses, ret, ret_next)
  

HighestSeqAgreesProposal(responses, ret, ret_next) ==
  _HighestSeqProposal("accept", responses, ret, ret_next)
  


FilterAddressesInResponses(allAddresses, responses, ret, ret_next) ==
  \E aSet \in SUBSET allAddresses: \A a \in allAddresses: 
       IF a \in aSet
       THEN a \in ret_next
       ELSE a \notin ret_next


AcceptProposal(propVal, val, ret_next) ==
  ret_next = val


(*
    
     
--algorithm alg {

  variables net = {},
            

  process (Proc \in NodeIds)
    variable 
             seq,
             val = FALSE,
             propVal, 
             state = "done",
             hSeq = MaxSeq + 1,
             responses = {},
             packet = {};
             acceptedProps = {};
             x = None;
             y = None;
             t = DefaultT;
  {   
  start:     while(TRUE) { \* variable name
  s01:         packet := None; \*ReceivePacket(self, packet', net, net')
                                                                           
  s02:         if(packet.data.op = "propose") {
                 if(packet.data.seq < hSeq) {
                   skip; \*Send(self, packet.sender, [op |-> "reject", seq |-> hSeq, val |-> val], net, net');
                 }
                 else {
                   x := None; \* AcceptProposal(propVal, val, ret_next);               
                   if(TRUE) { \* valid proposal(old, new) from users point, current value taken into account,
                   \*not proposed, as if we were not a leader    
                   
                     if(state # "done") {
                       state := "done"; \* avoid trying the same seq
                     };                  
                     hSeq := packet.data.seq;
                     seq := hSeq; \* ok?
                     skip; \*Send(self, packet.sender, [op |-> "accept_proposal", seq |-> hSeq, val |-> val], net, net');
                     acceptedProps := acceptedProps \union [seq |-> hSeq, val |-> val] 
                   }
                 }
               }; 
               
               
  s03:         if(packet.data.op = "accept") {               
                 if(state = "waiting_for_accepts") {
                   responses := responses \union data                   
                 }
               };
               
  s04:         if(packet.data.op = "accept_proposal") {
                 if(state = "waiting_for_proposal_responses") {
                   responses := responses \union data
                 } 
               };
               
  s05:         if(packet.data.op = "reject_proposal") {
                 if(state = "waiting_for_proposal_responses") {
                   responses := responses \union data
                 }
               };
                             
                      
  s06:         if(packet.data.op = "accept_request") {                  
                 if(packet.data.seq > hSeq) {
                    val := packet.data.val;
                    state := "done";                    
                    skip; \*Broadcast(self, [op |-> "accept", seq |-> data.seq, val |-> val], net, net');
                    acceptedProps := {[seq |-> packet.data.seq, val |-> packet.data.val]};                    
                 }                 
               };
               
               
               \*********** User space
               
  s07:         if(val = FALSE /\ state = "done") {
                 propVal := TRUE;
                 state := "proposed";
               };
               
               
               
               
               \*********** Actions
               
               
  s08:         if(state = "waiting_for_accept_responses") {
                 if(t = 0)
                   state := "evaluate_accept_responses";                   
                 }
                 else {
                   t := t - 1              
                 }               
               };
               
               
  s09:         if(state = "evaluate_accept_responses") {
                 x := None; \*MajorityAccepts(responses, NodeIds)
                 if(x) {
                   y := None;\*Answer
                   val := x.val;
                 };
                 state := "done";
                 
               }; 
                              
                              
  s10:         if(state = "waiting_for_proposal_responses") {               
                 if(t = 0) {
                   state := "evaluate_proposal_responses";                   
                 }
                 else {
                   t := t - 1;              
                 }
               };
               
                              
               if(state = "evaluate_proposal_responses") {                  
                 x := None; \*MajorityAgrees(responses, NodeIds)
                 if(x) {
                   x := None; \*HighestSeqAcceptProposal(responses, ret, ret_next)
                   if(h = None) {
                     h := propVal;                     
                   };                 
                   y := None; \*FilterAddressesInResponses(allAddresses, responses, ret, ret_next)
                   skip; \*Multicast(self, n, [op |-> "accept_request", seq |-> h.seq, val |-> h.val], net, net')
                   state := "waiting_for_accept_responses";
                   t := DefaultT;
                   responses := {};
                 } 
                 else {
                   state := "done";
                 }
               };                         
               
               
               if(state = "propose") {
                 seq := seq + 1;
                 skip; \*Broadcast(self, [op |-> "propose", seq |-> seq, val |-> propVal], net, net')
                 state := "waiting_for_proposal_responses";  
                 t := DefaultT;
                 responses := {};
               }                
                        
             }                               
  }
  
} \* end algorithm
*)

(*
 
*)
Receive(paxos, paxos_next, packet, packet_next, net, net_next) == TRUE



Action(paxos, paxos_next, net, net_next) == TRUE
    


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
