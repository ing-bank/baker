------------------------------ MODULE Cluster ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT nodes \* Model variables like A, B, C

VARIABLES memberNodeState, \* perspectives of the individual Nodes as a Function[Node -> NodeState]
          memberSelf,
          memberSbrDecision
          

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

ClusterState == [n \in nodes |-> memberNodeState[n][n]] 

N(n) == INSTANCE Node WITH 
                            nodeState <- memberNodeState[n],
                            self <- memberSelf[n],
                            sbrDecision <- memberSbrDecision[n]
                            
CInit == /\ \E n \in nodes : N(n)!NInit(n)
         /\ PrintVal("ClusterView init ClusterState", ClusterState)

CNext == \E n \in nodes : N(n)!NNext

\*CInvariants == /\ CTypeOK
\*               /\ \A n \in nodes : N(n)!NInvariants

=============================================================================
\* Modification History
\* Last modified Fri Aug 31 17:29:49 CEST 2018 by bekiroguz
\* Last modified Thu Aug 23 16:04:26 CEST 2018 by se76ni
\* Created Thu Aug 23 10:58:32 CEST 2018 by se76ni
