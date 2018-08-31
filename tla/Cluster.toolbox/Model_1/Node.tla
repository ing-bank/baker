-------------------------------- MODULE Node --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT nodes

VARIABLE self,
         sbrDecision,
         nodeState

PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

Majority == ((Cardinality(nodes) + 1) \div 2) \* calculate the majority number of nodes of all participating cluster nodes (including myself)

TotalUp(nodeStateNew) == LET sum[S \in SUBSET nodes] ==
                                IF S = {} THEN 0
                                ELSE LET n == CHOOSE node \in S : TRUE
                                     IN (IF nodeStateNew[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                         IN sum[nodes]

NTypeOK == /\ self \in nodes
           /\ sbrDecision \in {"DownMyself", "DownUnreachables", "NoAction"}
           /\ \E n \in nodes : nodeState[n] \in {"up", "unreachable", "down"}

SbrDecision(newNodeStates) == IF TotalUp(newNodeStates) >= Majority THEN "DownUnreachables" ELSE "TerminateMyself"

NodesWithState(state) == {} \* TODO return set of nodes in that given state

SelfState == nodeState[self]

MarkMemberUp(n) == /\ self /= n
                   /\ nodeState[n] = "unreachable"
                   /\ nodeState' = [nodeState EXCEPT ![n] = "up"]
                   /\ sbrDecision' = SbrDecision(nodeState')
                   /\ UNCHANGED<<self>>

MarkMemberUnreachable(n) == /\ self /= n
                            /\ nodeState[n] = "up"
                            /\ nodeState' = [nodeState EXCEPT ![n] = "unreachable"]
                            /\ sbrDecision' = SbrDecision(nodeState')
                            /\ UNCHANGED<<self>>
                        
ActOnSbrDecision == \/ /\ sbrDecision = "TerminateMyself"
                       /\ sbrDecision' = "NoAction"
                       /\ nodeState' = [nodeState EXCEPT ![self] = "down"]
                       /\ UNCHANGED<<self>>
                    \/ /\ sbrDecision = "DownUnreachables"
                       /\ sbrDecision' = "NoAction"
                       \* mark all unreachables to DOWN, remaining unchanged
                       /\ nodeState' = [x \in NodesWithState("unreachable") |-> "down"] \cup 
                                       [x \in nodes \ NodesWithState("unreachable") |-> nodeState[x]]
                       /\ UNCHANGED<<self>>
                        
NInit(selfNode) == 
        /\ PrintVal("MemberView init nodes", nodes)
        /\ self = selfNode 
        /\ PrintVal("MemberView init self", self)
        /\ sbrDecision = "NoAction"
        /\ PrintVal("MemberView init sbrDecision", sbrDecision)
        /\ nodeState = [n \in nodes |-> "up"]
        /\ PrintVal("MemberView init nodeState", nodeState)

NNext ==  \E n \in nodes : \/ MarkMemberUp(n) 
                           \/ MarkMemberUnreachable(n) 
                           \/ /\ self = n 
                              /\ ActOnSbrDecision \* enabled only n = self
                           
=============================================================================
\* Modification History
\* Last modified Fri Aug 31 17:25:13 CEST 2018 by bekiroguz
\* Last modified Thu Aug 23 16:04:03 CEST 2018 by se76ni
\* Created Wed Aug 15 12:26:52 CEST 2018 by bekiroguz
