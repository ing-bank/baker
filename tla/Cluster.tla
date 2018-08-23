------------------------------ MODULE Cluster ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT nodes \* Model variables like A, B, C

VARIABLES clusterState, \* Map<Node -> NodeStateRecord>
          nrOfOtherMembers,
          nodeInstances

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

Node(n) == INSTANCE Node WITH amIMember <- clusterState[n].amIMember, nrOfOtherMembers <- nrOfOtherMembers, otherNodes <- clusterState[n].otherNodes, othersState <- clusterState[n].othersState

Init ==
  /\ nrOfOtherMembers = Cardinality(nodes) - 1
  /\ PrintVal("nrOfOtherMembers", nrOfOtherMembers)
  /\ clusterState = [ n \in nodes |-> [amIMember |-> FALSE, nrOfOtherMembers |-> 0, otherNodes |-> {}, othersState |-> [otherNodes |-> {"unreachable"}]]]
  /\ PrintVal("clusterState", clusterState)
  /\ nodeInstances = [ n \in nodes |-> Node(n) ! Init(nrOfOtherMembers) ]
  /\ PrintVal("nodeInstances", nodeInstances)

NodeNext(n) ==  
  /\ Node(n) ! Next
  /\ UNCHANGED <<clusterState, nrOfOtherMembers, nodeInstances>>
  
Next == \E n \in nodes : NodeNext(n)

Invariants == \E n \in nodes : Node(n) ! Invariants

=============================================================================
\* Modification History
\* Last modified Thu Aug 23 17:10:30 CEST 2018 by bekiroguz
\* Last modified Thu Aug 23 16:04:26 CEST 2018 by se76ni
\* Created Thu Aug 23 10:58:32 CEST 2018 by se76ni
