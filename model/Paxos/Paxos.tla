----------------------- MODULE Paxos -------------------------
EXTENDS Naturals
CONSTANT NodeCount,         
         MaxSeq,
         DefaultTimeout,
         None
(*         
Readers == 1 .. ReadersCount
Writers == (ReadersCount + 1) .. (ReadersCount + WritersCount)
*)

LOCAL INSTANCE FiniteSets

Vals == BOOLEAN

NodeIds == 1 .. NodeCount


States == {            
            "propose",
            "waiting_for_proposal_responses",
            "waiting_for_accept_responses",
            "done"
          }
    (*      
Ops == {
         "propose",
         "accept_proposal",
         "reject_proposal"
       }
*)

AcceptedProposals == [seq: 1..MaxSeq, val: Vals]

(* Proposer sends to Acceptors *)
Protocol1 == [op: {"propose"}, seq: 1..MaxSeq]

(* Acceptor accepts proposal *)
Protocol2 == [op: {"accept_proposal"}, seq: 1..MaxSeq, acceptedProposals: SUBSET AcceptedProposals]

(* Acceptor rejects proposal *)
Protocol3 == [op: {"reject_proposal"}, seq: 1..MaxSeq]

(* Proposer sends to Acceptors *)
Protocol4 == [op: {"accept_value_request"}, seq: 1..MaxSeq, val: Vals]

(* Acceptor commits to the final value *)
Protocol5 == [op: {"accept_value"}, seq: 1..MaxSeq]

Protocol ==        Protocol1
            \union Protocol2
            \union Protocol3
            \union Protocol4
            \union Protocol5


netInstance == INSTANCE UnreliableNetwork WITH
                   AddressSpace <- NodeIds,
                   DataSpace <- Protocol,
                   None <- None,
                   maxNetSize <- 10


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

  variables net = {}, \* init net
            

  process (Proc \in NodeIds)
    variable 
             (*Every cycle a single packet is received and acted upon *)
             packet = {},
             (* Last proposal ID the proposer used *)
             lastUsedProposalId = self - 1,
             (* current value *)
             val = FALSE,
             (* proposed value *)
             propVal, 
             (* state of the protocol *)
             state = "done",
             (* acceptor must keep track of the highest received proposal number *)
             highestReceivedProposalId = 0,
             (* acceptor must keep track of pending proposals it accepted 
                [seq |-> highestReceivedProposalId, val |-> val]
             *)
             acceptedProps = {},
             (* timer for response timeout (steps) *)
             t = DefaultTimeout,
             (* set of responses from the acceptors (packet.data) *)
             responses = {},             
             (* helper vars... *)                          
             x = None,
             y = None,             
             h = None;
             \*data = None;
  {   
  start:     while(TRUE) { 
  s01:         packet := None; \* ReceivePacket(self, packet', net, net')
               
  s12:         if(packet # None) {    
               
               (*** Received proposal ***)                                                    
  s02:         if(packet.data.op = "propose") {
                 (*
                 If the proposal's number N is higher than any previous proposal number received from any
                 Proposer by the Acceptor, then the Acceptor must return a promise
                 to ignore all future proposals having a number less than N.
                  -- this is done by updating highestReceivedProposalId 
                 If the Acceptor accepted a proposal at some point in the past,
                  it must include the previous proposal number and previous value in its response to the Proposer.
                 *)
                 if(packet.data.seq > highestReceivedProposalId) {                  
                   
                   skip; \*Send(self, packet.sender, [op |-> "accept_proposal", seq |-> packet.data.seq, val |-> acceptedProps], net, net');
                   
                   highestReceivedProposalId := packet.data.seq;
                   \*lastUsedProposalId := highestReceivedProposalId; \* is this ok?
                 }
                 else {
                   (*
                      Otherwise, the Acceptor can ignore the received proposal. 
                      It does not have to answer in this case for Paxos to work.
                      However, for the sake of optimization, sending a denial (Nack)
                      response would tell the Proposer that it can stop its attempt to
                      create consensus with proposal N.
                   *)
                   skip; \*Send(self, packet.sender, [op |-> "reject_proposal", seq |-> packet.data.seq], net, net');
                 }                
                 
               }; 
               
              
               (* Receiving responses on our proposal *)
               
  s03:         if(packet.data.op = "accept_proposal") {
                 if(state = "waiting_for_proposal_responses" /\ packet.data.seq = lastUsedProposalId) {
                   responses := responses \union packet.data
                 } 
               };
               
  s04:         if(packet.data.op = "reject_proposal") {
                 if(state = "waiting_for_proposal_responses" /\ packet.data.seq = lastUsedProposalId) {
                   responses := responses \union packet.data
                 }
               };



  s05:         if(packet.data.op = "accept_value") {               
                 if(state = "waiting_for_accepts") {
                   responses := responses \union packet.data                   
                 }
               };                             
               
               (** we are receiving request to accept **)       
  s06:         if(packet.data.op = "accept_value_request") {    
                 (*                 
                 If an Acceptor receives an Accept Request message for a proposal N, 
                 it must accept it if and only if it has not already promised 
                 to any prepare proposals having an identifier greater than N. 
                 In this case, it should register the corresponding value v and send an 
                 Accepted message to the Proposer and every Learner.
                 Else, it can ignore the Accept Request.
                 *)               
                 if(packet.data.seq < highestReceivedProposalId) {
                 
                    \* save value
                    val := packet.data.val;
                    state := "done";                    
                    \* send back to proposer, and inform others
                    skip; \*Broadcast(self, [op |-> "accept", seq |-> data.seq, val |-> val], net, net');
                    \* reset accepted props
                    acceptedProps := {[seq |-> packet.data.seq, val |-> packet.data.val]};                    
                 }                 
               };
               
               
               };
               
               \*********** User space
               
  s07:         if(val = FALSE /\ state = "done") {
                 propVal := TRUE;
                 state := "propose";
               };
               
               
               
               
               \*********** Actions

                              
                      
                              
  s08:         if(state = "waiting_for_proposal_responses") {               
                 (*
                   If a Proposer receives enough promises from a Quorum of Acceptors,
                   it needs to set a value to its proposal.
                   If any Acceptors had previously accepted any proposal,
                   then they'll have sent their values to the Proposer, who now must set the value of its proposal
                   to the value associated with the highest proposal number reported by the Acceptors. 
                   If none of the Acceptors had accepted a proposal up to this point,
                   then the Proposer may choose any value for its proposal.
                   The Proposer sends an Accept Request message to a Quorum of Acceptors with the chosen value for its proposal.
                 *)
                 x := None; \*EnoughPromises(responses, NodeIds)
                 \* number of accept responses is greater that half, todo deal with rejects 
                 if(x) {
                   (*
                   must set the value of its proposal
                   to the value associated with the highest proposal number reported by the Acceptors
                   *)
                   h := None; \*HighestSeqAcceptProposal(responses, ret, ret_next)
                   if(h = None) {
                     (*
                     If none of the Acceptors had accepted a proposal up to this point,
                     then the Proposer may choose any value for its proposal.
                     *)
  s09:               h := propVal; (* we may set our value *)                     
                   };                 
                   (* Send the accept request to acceptors *)
  s11:             y := None; \*FilterAddressesInResponses(allAddresses, responses, ret, ret_next)
                   skip; \*Multicast(self, n, [op |-> "accept_request", seq |-> h.seq, val |-> h.val], net, net')
                   state := "waiting_for_accept_responses";
                   t := DefaultTimeout; \* reset timeout
                   responses := {}; \*reset responses
                   
                   (*
                   \* update
                   lastUsedProposalId := highestReceivedProposalId; \* is this ok?
                   *)
                   
                 } 
                 else {
                   if(t = 0) {
                     state := "done"; \*timeout                   
                   }
                   else {
                     t := t - 1;              
                   }
                 }             
                 
               };
               
               
               
  s10:         if(state = "waiting_for_accept_responses") {
                 (*                 
                 If an Acceptor receives an Accept Request message for a proposal N, 
                 it must accept it if and only if it has not already promised 
                 to any prepare proposals having an identifier greater than N. 
                 In this case, it should register the corresponding value v and send an 
                 Accepted message to the Proposer and every Learner.
                 Else, it can ignore the Accept Request.

                 Note that an Acceptor can accept multiple proposals.
                 These proposals may even have different values in the presence of certain failures. 
                 However, the Paxos protocol will guarantee that 
                 the Acceptors will ultimately agree on a single value.

                 Rounds fail when multiple Proposers send conflicting Prepare messages, 
                 or when the Proposer does not receive a Quorum of responses (Promise or Accepted). 
                 In these cases, another round must be started with a higher proposal number. 
                 
                 *)
                 x := None; \*MajorityAccepts(responses, NodeIds)
                 if(x) {
                   \*y := None;\*Answer
                   val := x.val; \* set the value
                 } else {                
                 
                   if(t = 0) {
                   
                   \*t := DefaultT; \* reset timeout
                   \*responses := {}; \*reset responses
                     state := "done";   
                                     
                   }
                   else {
                     t := t - 1              
                   }
                          
                 }        
               };
               
                                                            
               
               (* We are the Proposer *)
    s13:       if(state = "propose") {
                 lastUsedProposalId := lastUsedProposalId + 1;                 
                 skip; \* Broadcast(self, [op |-> "propose", seq |-> lastUsedProposalId], net, net')
                 state := "waiting_for_proposal_responses";  
                 t := DefaultTimeout;
                 responses := {};
               }                
                        
             }                               
  }
  
} \* end algorithm
*)


-------------------------------------------------------------------

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES net, pc, packet, lastUsedProposalId, val, propVal, state, 
          highestReceivedProposalId, acceptedProps, t, responses, x, y, h

vars == << net, pc, packet, lastUsedProposalId, val, propVal, state, 
           highestReceivedProposalId, acceptedProps, t, responses, x, y, h >>

ProcSet == (NodeIds)

Init == (* Global variables *)
        /\ net = {}
        (* Process Proc *)
        /\ packet = [self \in NodeIds |-> netInstance!NonePacket]
        /\ lastUsedProposalId = [self \in NodeIds |-> self - 1]
        /\ val = [self \in NodeIds |-> FALSE]
        /\ propVal = [self \in NodeIds |-> defaultInitValue]
        /\ state = [self \in NodeIds |-> "done"]
        /\ highestReceivedProposalId = [self \in NodeIds |-> 0]
        /\ acceptedProps = [self \in NodeIds |-> {}]
        /\ t = [self \in NodeIds |-> DefaultTimeout]
        /\ responses = [self \in NodeIds |-> {}]
        /\ x = [self \in NodeIds |-> None]
        /\ y = [self \in NodeIds |-> None]
        /\ h = [self \in NodeIds |-> None]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "s01"]
               /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                               state, highestReceivedProposalId, acceptedProps, 
                               t, responses, x, y, h >>

s01(self) == /\ pc[self] = "s01"
             /\ \E xx \in netInstance!PacketSpace:
                 /\ packet' = [packet EXCEPT ![self] = xx]
                 /\ netInstance!ReceivePacket(self, xx, net, net')
             \*/\ packet' = [packet EXCEPT ![self] = None] \* ReceivePacket(self, packet', net, net')
             /\ pc' = [pc EXCEPT ![self] = "s12"]
             /\ UNCHANGED << lastUsedProposalId, val, propVal, state, 
                             highestReceivedProposalId, acceptedProps, t, 
                             responses, x, y, h >>

s12(self) == /\ pc[self] = "s12"
             /\ IF packet[self] # netInstance!NonePacket
                   THEN /\ pc' = [pc EXCEPT ![self] = "s02"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s07"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             state, highestReceivedProposalId, acceptedProps, 
                             t, responses, x, y, h >>

s02(self) == /\ pc[self] = "s02"
             /\ IF packet[self].data.op = "propose"
                   THEN /\ IF packet[self].data.seq > highestReceivedProposalId[self]
                              THEN /\ netInstance!Send(self, packet[self].sender, [op |-> "accept_proposal", seq |-> packet.data.seq, val |-> acceptedProps[self]], net, net')
                                   /\ highestReceivedProposalId' = [highestReceivedProposalId EXCEPT ![self] = packet[self].data.seq]
                              ELSE /\ netInstance!Send(self, packet[self].sender, [op |-> "reject_proposal", seq |-> packet.data.seq], net, net')
                                   /\ UNCHANGED highestReceivedProposalId
                   ELSE /\ TRUE
                        /\ UNCHANGED << net, highestReceivedProposalId >>
             /\ pc' = [pc EXCEPT ![self] = "s03"]
             /\ UNCHANGED << packet, lastUsedProposalId, val, propVal, 
                             state, acceptedProps, t, responses, x, y, h >>

s03(self) == /\ pc[self] = "s03"
             /\ IF packet[self].data.op = "accept_proposal"
                   THEN /\ IF state[self] = "waiting_for_proposal_responses" /\ packet[self].data.seq = lastUsedProposalId[self]
                              THEN /\ responses' = [responses EXCEPT ![self] = responses[self] \union packet[self].data]
                              ELSE /\ TRUE
                                   /\ UNCHANGED responses
                   ELSE /\ TRUE
                        /\ UNCHANGED responses
             /\ pc' = [pc EXCEPT ![self] = "s04"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             state, highestReceivedProposalId, acceptedProps, 
                             t, x, y, h >>

s04(self) == /\ pc[self] = "s04"
             /\ IF packet[self].data.op = "reject_proposal"
                   THEN /\ IF state[self] = "waiting_for_proposal_responses" /\ packet[self].data.seq = lastUsedProposalId[self]
                              THEN /\ responses' = [responses EXCEPT ![self] = responses[self] \union packet[self].data]
                              ELSE /\ TRUE
                                   /\ UNCHANGED responses
                   ELSE /\ TRUE
                        /\ UNCHANGED responses
             /\ pc' = [pc EXCEPT ![self] = "s05"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             state, highestReceivedProposalId, acceptedProps, 
                             t, x, y, h >>

s05(self) == /\ pc[self] = "s05"
             /\ IF packet[self].data.op = "accept_value"
                   THEN /\ IF state[self] = "waiting_for_accepts"
                              THEN /\ responses' = [responses EXCEPT ![self] = responses[self] \union packet[self].data]
                              ELSE /\ TRUE
                                   /\ UNCHANGED responses
                   ELSE /\ TRUE
                        /\ UNCHANGED responses
             /\ pc' = [pc EXCEPT ![self] = "s06"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             state, highestReceivedProposalId, acceptedProps, 
                             t, x, y, h >>

s06(self) == /\ pc[self] = "s06"
             /\ IF packet[self].data.op = "accept_value_request"
                   THEN /\ IF packet[self].data.seq < highestReceivedProposalId[self]
                              THEN /\ val' = [val EXCEPT ![self] = packet[self].data.val]
                                   /\ state' = [state EXCEPT ![self] = "done"]
                                   /\ netInstance!Broadcast(self, [op |-> "accept", seq |-> data.seq, val |-> val], net, net')
                                   /\ acceptedProps' = [acceptedProps EXCEPT ![self] = {[seq |-> packet[self].data.seq, val |-> packet[self].data.val]}]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << net, val, state, acceptedProps >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << net, val, state, acceptedProps >>
             /\ pc' = [pc EXCEPT ![self] = "s07"]
             /\ UNCHANGED <<  packet, lastUsedProposalId, propVal, 
                             highestReceivedProposalId, t, responses, x, y, h >>

s07(self) == /\ pc[self] = "s07"
             /\ IF val[self] = FALSE /\ state[self] = "done"
                   THEN /\ propVal' = [propVal EXCEPT ![self] = TRUE]
                        /\ state' = [state EXCEPT ![self] = "propose"]
                   ELSE /\ TRUE
                        /\ UNCHANGED << propVal, state >>
             /\ pc' = [pc EXCEPT ![self] = "s08"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, 
                             highestReceivedProposalId, acceptedProps, t, 
                             responses, x, y, h >>

s08(self) == /\ pc[self] = "s08"
             /\ IF state[self] = "waiting_for_proposal_responses"
                   THEN /\ x' = [x EXCEPT ![self] = FALSE]
                        /\ IF x'[self]
                              THEN /\ h' = [h EXCEPT ![self] = None]
                                   /\ IF h'[self] = None
                                         THEN /\ pc' = [pc EXCEPT ![self] = "s09"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "s11"]
                                   /\ UNCHANGED << state, t >>
                              ELSE /\ IF t[self] = 0
                                         THEN /\ state' = [state EXCEPT ![self] = "done"]
                                              /\ t' = t
                                         ELSE /\ t' = [t EXCEPT ![self] = t[self] - 1]
                                              /\ state' = state
                                   /\ pc' = [pc EXCEPT ![self] = "s10"]
                                   /\ h' = h
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s10"]
                        /\ UNCHANGED << state, t, x, h >>
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             highestReceivedProposalId, acceptedProps, 
                             responses, y >>

s11(self) == /\ pc[self] = "s11"
             /\ y' = [y EXCEPT ![self] = None]
             /\ TRUE
             /\ state' = [state EXCEPT ![self] = "waiting_for_accept_responses"]
             /\ t' = [t EXCEPT ![self] = DefaultTimeout]
             /\ responses' = [responses EXCEPT ![self] = {}]
             /\ pc' = [pc EXCEPT ![self] = "s10"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             highestReceivedProposalId, acceptedProps, x, h >>

s09(self) == /\ pc[self] = "s09"
             /\ h' = [h EXCEPT ![self] = propVal[self]]
             /\ pc' = [pc EXCEPT ![self] = "s11"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, val, propVal, 
                             state, highestReceivedProposalId, acceptedProps, 
                             t, responses, x, y >>

s10(self) == /\ pc[self] = "s10"
             /\ IF state[self] = "waiting_for_accept_responses"
                   THEN /\ x' = [x EXCEPT ![self] = None]
                        /\ IF x'[self]
                              THEN /\ val' = [val EXCEPT ![self] = x'[self].val]
                                   /\ UNCHANGED << state, t >>
                              ELSE /\ IF t[self] = 0
                                         THEN /\ state' = [state EXCEPT ![self] = "done"]
                                              /\ t' = t
                                         ELSE /\ t' = [t EXCEPT ![self] = t[self] - 1]
                                              /\ state' = state
                                   /\ val' = val
                   ELSE /\ TRUE
                        /\ UNCHANGED << val, state, t, x >>
             /\ pc' = [pc EXCEPT ![self] = "s13"]
             /\ UNCHANGED << net, packet, lastUsedProposalId, propVal, 
                             highestReceivedProposalId, acceptedProps, 
                             responses, y, h >>

s13(self) == /\ pc[self] = "s13"
             /\ IF state[self] = "propose"
                   THEN /\ lastUsedProposalId' = [lastUsedProposalId EXCEPT ![self] = lastUsedProposalId[self] + 1]
                        /\ TRUE
                        /\ state' = [state EXCEPT ![self] = "waiting_for_proposal_responses"]
                        /\ t' = [t EXCEPT ![self] = DefaultTimeout]
                        /\ responses' = [responses EXCEPT ![self] = {}]
                   ELSE /\ TRUE
                        /\ UNCHANGED << lastUsedProposalId, state, t, 
                                        responses >>
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << net, packet, val, propVal, 
                             highestReceivedProposalId, acceptedProps, x, y, h >>

Proc(self) == start(self) \/ s01(self) \/ s12(self) \/ s02(self)
                 \/ s03(self) \/ s04(self) \/ s05(self) \/ s06(self)
                 \/ s07(self) \/ s08(self) \/ s11(self) \/ s09(self)
                 \/ s10(self) \/ s13(self)

Next == (\E self \in NodeIds: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

-------------------------------------------------------------------

(*
*)

(*
*)

===================================================================




