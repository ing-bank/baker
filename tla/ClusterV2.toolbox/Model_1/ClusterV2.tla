----------------------------- MODULE ClusterV2 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT NumNodes

Nodes == 1..NumNodes \* Set of all nodes
Channels == Nodes \X Nodes \* Set of all possible <<from, to>> communication

ASSUME NumNodes > 0

\*States == {"up", "down", "unreachable"}
\*SbrDecisions == {"DownMyself", "DownUnreachables", "NoAction"}

(* 
--algorithm ClusterV2 {
  variables nodeState = [n \in Nodes |-> 
                                         [m \in Nodes |-> "up"]],
            leader = 1, \* pick the first one as leader
            sbrDecision = [n \in Nodes |-> "NoAction"];

  define {
    TotalUp(oneNodePerspectiveState) == LET sum[S \in SUBSET Nodes] ==
                                IF S = {} THEN 0
                                ELSE LET n == CHOOSE node \in S : TRUE
                                     IN (IF oneNodePerspectiveState[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                         IN sum[Nodes]
                         
    Majority == ((NumNodes + 1) \div 2) \* calculate the majority number of nodes of all participating cluster nodes (including myself)

    InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE
        
  }
  
  macro decide(node) {
    sbrDecision := [sbrDecision EXCEPT ![node] = 
    
                     IF (node = leader) THEN {
                       IF(InMajority(nodeState[node])) THEN "DownUnreachables" ELSE "DownMyself"
                     } ELSE {
                       IF(InMajority(nodeState[node])) THEN "NoAction" ELSE "DownMyself"
                     }
                       
                   ];
  }
  
  macro receiveMemberUnreachable(from, to) {
    await from # to;

    nodeState[to] := [nodeState[to] EXCEPT ![from] = "unreachable"];
    decide(to);
    print <<to, "has seen member", from, "as unreachable", "nodeState", nodeState, "sbrDecision", sbrDecision[to]>>;
  }   
  
  macro receiveMemberUp(from, to) {
    await from # to;

    nodeState[to] := [nodeState[to] EXCEPT ![from] = "up"];
    decide(to);
    print <<to, "has seen member", from, "as up", "nodeState", nodeState, "sbrDecision", sbrDecision[to]>>;
  }   
  
  process (chan \in Channels)
  variables from = self[1], to = self[2];
  {
    Start: while(TRUE) {
               skip; \* skip the non critical section
      Receive: either { receiveMemberUnreachable(from, to); }
               or     { receiveMemberUp(from, to); }
           }  
  }

}
*)
\* BEGIN TRANSLATION
VARIABLES nodeState, leader, sbrDecision, pc

(* define statement *)
TotalUp(oneNodePerspectiveState) == LET sum[S \in SUBSET Nodes] ==
                            IF S = {} THEN 0
                            ELSE LET n == CHOOSE node \in S : TRUE
                                 IN (IF oneNodePerspectiveState[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                     IN sum[Nodes]

Majority == ((NumNodes + 1) \div 2)

InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE

VARIABLES from, to

vars == << nodeState, leader, sbrDecision, pc, from, to >>

ProcSet == (Channels)

Init == (* Global variables *)
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ leader = 1
        /\ sbrDecision = [n \in Nodes |-> "NoAction"]
        (* Process chan *)
        /\ from = [self \in Channels |-> self[1]]
        /\ to = [self \in Channels |-> self[2]]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Receive"]
               /\ UNCHANGED << nodeState, leader, sbrDecision, from, to >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ from[self] # to[self]
                       /\ nodeState' = [nodeState EXCEPT ![to[self]] = [nodeState[to[self]] EXCEPT ![from[self]] = "unreachable"]]
                       /\ sbrDecision' = [sbrDecision EXCEPT ![to[self]] =
                                         
                                           IF (to[self] = leader) THEN {
                                             IF(InMajority(nodeState'[to[self]])) THEN "DownUnreachables" ELSE "DownMyself"
                                           } ELSE {
                                             IF(InMajority(nodeState'[to[self]])) THEN "NoAction" ELSE "DownMyself"
                                           }
                                         
                                         ]
                       /\ PrintT(<<to[self], "has seen member", from[self], "as unreachable", "nodeState", nodeState', "sbrDecision", sbrDecision'[to[self]]>>)
                    \/ /\ from[self] # to[self]
                       /\ nodeState' = [nodeState EXCEPT ![to[self]] = [nodeState[to[self]] EXCEPT ![from[self]] = "up"]]
                       /\ sbrDecision' = [sbrDecision EXCEPT ![to[self]] =
                                         
                                           IF (to[self] = leader) THEN {
                                             IF(InMajority(nodeState'[to[self]])) THEN "DownUnreachables" ELSE "DownMyself"
                                           } ELSE {
                                             IF(InMajority(nodeState'[to[self]])) THEN "NoAction" ELSE "DownMyself"
                                           }
                                         
                                         ]
                       /\ PrintT(<<to[self], "has seen member", from[self], "as up", "nodeState", nodeState', "sbrDecision", sbrDecision'[to[self]]>>)
                 /\ pc' = [pc EXCEPT ![self] = "Start"]
                 /\ UNCHANGED << leader, from, to >>

chan(self) == Start(self) \/ Receive(self)

Next == (\E self \in Channels: chan(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Sep 06 17:18:50 CEST 2018 by bekiroguz
\* Created Mon Sep 03 15:16:19 CEST 2018 by bekiroguz
