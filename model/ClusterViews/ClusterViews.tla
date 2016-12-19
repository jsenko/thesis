(*
 * 
 *)
----------------------- MODULE ClusterViews -------------------------
EXTENDS Integers, FiniteSets, Sequences
CONSTANT AddressSpace,
         net     
         
---------------------------------------------------------------------

(* Update view process, (should run continuously, if topology may change)
 * 1. send ping to all addresses
 * 2. wait for responses:
 *   receve:
 *     none -> // nobody responded yet vs no other node is reachable, we will emulate random
               // timeout by nondeterministically decide which one happened,
               // protocol must allow node to join later
               guess: no other node is reachable
                  - choose coordinator from responses, send to them "i'm coord!" packet.
               guess: nobody resp. yet, call receive again
                  - how to prevent deadlock? // forbid it using temp. formula, saying that
                    // node must eventually choose the first option, equivalent to
                    // timeout being finite
                    // can it happen that the node stays separate?
                    // should not because if there is someone else,
                    // they have to send ping, even if it arrives late
       i'm coord! -> no need to check, we trust the coord node, coord selected
       ping -> if coord is already selected, this means someone was too late,
               we will send the current leader to them "he's leader+current view"
       pong or join -> add node to pool of discovered nodes
                       
       he's leader -> compare if my id is bigger, if no, send "join" to
                      everyone
                      else send "i'm leader" to everyone
                      
 * Can we assume connection break (and restore! -> losing messages) during this protocol?
 * Byzantine problem
 *)

\* careful to use unique values within the entire network!
IamLeader == [type: {"IamLeader"}, view: AddressSpace]
Ping == [type: {"Ping"}]
PongOrJoin == [type: {"PongOrJoin"}]
HesLeaderSpace == [type: {"HesLeader"}, view: AddressSpace]
\*HesLeader == SUBSET HesLeaderSpace

ProtocolSpace == {IamLeader, Ping, PongOrJoin, HesLeaderSpace} \union HesLeaderSpace

\*include that in data space

---------------------------------------------------------------------

(*
--algorithm IncDec {

  variables res = {};            
  
  process (Proc = 1)
    variable allAddr, myaddr(*self*), addr, rec_data, coord, view;
    \* bydefault coor is nocoord
  {
    start:       allAddr := AddressSpace;
                 \* ping regularly!, but everytim is overkill?
                 
                 \*********** todo discovery lock when doing rebalance?
                 with (x \in {0, 1}) {
                   if(x = 0) {
                     goto receive; \* nondet. skip ping broadcast
                   }
                 };
                 
    broadcast:   while(allAddr # {}) {
    s01:           with(a \in allAddr) {
                     addr := a; \* send ping
                   };
    s02:           allAddr := allAddr \ {};
                 };     
    
    receive:     skip; \* receive rec_data
    
                 if (rec_data = NoData) {
                   with (x \in {0, 1}) {
    s03:             if(x = 1) {
                       skip; \* assume ping timeout TODO
                     };
                   }
                 };
    
    
    s04:         if (rec_data = PongOrJoin) {
    s05:           view := view \union {}; \* add sender to view
                   \*update coord?    
                 };
    
    s06:         if (rec_data = IamLeader) {
                   coord := coord;
                   view := view;
                 };
    
    s06:         if (rec_data = Ping) {
                   if (coord = NoCoord) {
    s07:             skip; \* send pong back
                   }
                   else {
    s08:             skip; \* send heisleader!
                   };
                 };
    
    s06:         if (rec_data = HeIsLeader) {
                   if (max(rec_data.view) = self) {
    s07:             skip; \* send join to view
                     view := rec_data.view;
                   }
                   else {
    s08:             skip; \* send iamleader to view
                     view := rec_data.view;
                   };
                 };
                 \* net event loop, go back? thread runs on network requests?
                 \* other ops, save, get, balance, etc.
                 
                 \* consistent hashing -> reads are always going to the right node(s)
                 
                 \* writes? lock on leader!
                 
                 \*where is userspace?
                 \*userspace may be "enabled" (i.e. not blocked)
                 \*when no read or write requests are pending
                 \*waiting to set data variable.
                 \*on failed operation it may contain special value
                 \* this may be tuned to availability or consistency (how?)
                 \*prompting discovery/rebalance?
                 \*how to do read/write timeout or fail
                 \*or discover or rebalance is not in progress,
                 \* must check for liveness!
    userspace:   skip;             
                 
                 goto receive;
                  
  }
} \* end algorithm
*)


\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES res, pc, allAddr, addr

vars == << res, pc, allAddr, addr >>

ProcSet == {1}

Init == (* Global variables *)
        /\ res = {}
        (* Process Proc *)
        /\ allAddr = defaultInitValue
        /\ addr = defaultInitValue
        /\ pc = [self \in ProcSet |-> "start"]

start == /\ pc[1] = "start"
         /\ allAddr' = AddressSpace
         /\ pc' = [pc EXCEPT ![1] = "broadcast"]
         /\ UNCHANGED << res, addr >>

broadcast == /\ pc[1] = "broadcast"
             /\ IF allAddr # {}
                   THEN /\ pc' = [pc EXCEPT ![1] = "s01"]
                   ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
             /\ UNCHANGED << res, allAddr, addr >>

s01 == /\ pc[1] = "s01"
       /\ \E a \in allAddr:
            addr' = a
       /\ allAddr' = allAddr \ {}
       /\ pc' = [pc EXCEPT ![1] = "broadcast"]
       /\ res' = res

Proc == start \/ broadcast \/ s01

Next == Proc
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


----------------------------------------------------------------------



(*         
KeySpace == 0 .. MaxKey
ValueSpace == 0 .. MaxValue
NodeIdSpace == 0 .. MaxNodeId      
         
TypeInvariant == 
  /\ MaxNodeId <= MaxKey
  /\ MaxKey <= MaxValue
  
             
hash(key, value) == key = value % (MaxKey + 1)
(* keys must be comparable, lastkey->firstKey, to avoid this problem,
assert that there is always at least single node that starts at the beginning

*)
SegmentSpace == [nodeId: NodeIdSpace, startIncl: KeySpace, endExcl: KeySpace \union {MaxKey+1}]

WheelSpace == SUBSET SegmentSpace

SegmentSpaceTypeInvariant(sspace) ==
  /\ Cardinality(sspace) > 0
  /\ \E segment \in sspace:
         segment.startIncl = 0
  /\ \E segment \in sspace:
         segment.endExcl = MaxKey  
  /\ \A segment \in sspace:
      /\ segment.startIncl < segment.endExcl  
      /\ (segment.endExcl = MaxKey
           \/ \E nextseg \in sspace:
                   segment.endExcl = nextseg.startIncl)

\* Find the correct segment
GetNodeForKey(sspace, key, ret_nodeId) ==
  \E seg \in sspace:
     /\ seg.startInc <= key
     /\ key < seg.endExcl
     /\ ret_nodeId = seg.nodeId

IsNodeUsed(sspace, nodeId) ==
  \E seg \in sspace:
     /\ seg.nodeId = nodeId

MaxSegment(sspace, ret_seg) ==
  \E seg \in sspace:
      /\ \A seg2 \in sspace:
            (seg.endExcl - seg.startIncl) >= (seg2.endExcl - seg2.startIncl)
      /\ ret_seg = seg  
      
SplitPint(startIncl, endExcl, ret_newStart) ==
  \E newStart \in KeySpace:
      /\ newStart = ((endExcl - startIncl) \div 2) + 1

\* EXCL not in keyspace?

\* careful, must not be already there
\* must be within nodeidspace
AddNode(newNodeId, sspace, sspace_next) ==
  \*Find (one of) the max segments and split
  \E max_seg \in sspace:
     /\ MaxSegment(sspace, max_seg)
     /\ \E newStart \in KeySpace:
           /\ SplitPint(max_seg.startIncl, max_seg.endExcl, newStart)
           /\ sspace_next = (sspace \ {max_seg}) \union {[nodeId |-> newNodeId, startIncl |-> max_seg.startIncl, endExcl |-> newStart], [nodeId |-> newNodeId, startIncl |-> newStart, endExcl |-> max_seg.endExcl]}
     
*)

-------------------------------------------------------------------

===================================================================
