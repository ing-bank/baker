------------------------------ MODULE Cluster ------------------------------


VARIABLES
  nrOfOtherMembers,
  nodeA_amIMember,
  nodeA_otherNodes,
  nodeA_othersState,
  nodeB_amIMember,
  nodeB_otherNodes,
  nodeB_othersState,
  nodeC_amIMember,
  nodeC_otherNodes,
  nodeC_othersState


NodeA == INSTANCE Node WITH amIMember <- nodeA_amIMember, nrOfOtherMembers <- nrOfOtherMembers, otherNodes <- nodeA_otherNodes, othersState <- nodeA_othersState
NodeB == INSTANCE Node WITH amIMember <- nodeB_amIMember, nrOfOtherMembers <- nrOfOtherMembers, otherNodes <- nodeB_otherNodes, othersState <- nodeB_othersState
NodeC == INSTANCE Node WITH amIMember <- nodeC_amIMember, nrOfOtherMembers <- nrOfOtherMembers, otherNodes <- nodeC_otherNodes, othersState <- nodeC_othersState


Init ==
  /\ nrOfOtherMembers = 2
  /\ NodeA ! Init(nrOfOtherMembers)
  /\ NodeB ! Init(nrOfOtherMembers)
  /\ NodeC ! Init(nrOfOtherMembers)

NodeANext ==
  /\ NodeA ! Next
  /\ UNCHANGED <<nodeB_amIMember, nodeB_otherNodes, nodeB_othersState, nodeC_amIMember, nodeC_otherNodes, nodeC_othersState>>

NodeBNext ==
  /\ NodeB ! Next
  /\ UNCHANGED <<nodeA_amIMember, nodeA_otherNodes, nodeA_othersState, nodeC_amIMember, nodeC_otherNodes, nodeC_othersState>>

NodeCNext ==
  /\ NodeC ! Next
  /\ UNCHANGED <<nodeB_amIMember, nodeB_otherNodes, nodeB_othersState, nodeA_amIMember, nodeA_otherNodes, nodeA_othersState>>



Next ==
    \/ NodeANext
    \/ NodeBNext
    \/ NodeCNext




=============================================================================
\* Modification History
\* Last modified Thu Aug 23 15:54:40 CEST 2018 by se76ni
\* Created Thu Aug 23 10:58:32 CEST 2018 by se76ni
