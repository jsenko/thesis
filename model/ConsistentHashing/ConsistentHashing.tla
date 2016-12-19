(*
 * 
 *)
----------------------- MODULE ConsistentHashing -------------------------
EXTENDS Integers, FiniteSets
CONSTANT MaxKey,     
         MaxNodeId,    
         MaxValue,
         HashWheelSize \* max number of slots (nodes) that can be present on the wheel 
         
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
     


-------------------------------------------------------------------

===================================================================
