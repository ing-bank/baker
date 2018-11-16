------------------------------ MODULE Cluster ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT nodes \* Model variables like A, B, C

VARIABLES \* substitute variables for each node instance (defined as a function) 
          memberNodeState, 
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
\* Last modified Fri Aug 31 17:42:04 CEST 2018 by bekiroguz
\* Last modified Thu Aug 23 16:04:26 CEST 2018 by se76ni
\* Created Thu Aug 23 10:58:32 CEST 2018 by se76ni
