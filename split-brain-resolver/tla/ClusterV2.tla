----------------------------- MODULE ClusterV2 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT NumNodes

Nodes == 1..NumNodes \* Set of all nodes

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
    
    SbrDecision(isLeader, state) ==
      IF (isLeader) THEN
        IF(InMajority(state)) THEN "DownUnreachables" ELSE "DownMyself"
      ELSE
        IF(InMajority(state)) THEN "NoAction" ELSE "DownMyself" 
      
  }
  
  macro receiveMemberState(me, other, newState) {
    print <<me, "received", other, "as", newState, "previous nodeState", nodeState[me], "previous sbrDecision", sbrDecision[me]>>;

    nodeState[me] := [nodeState[me] EXCEPT ![other] = newState];

    sbrDecision := [x \in Nodes |-> SbrDecision(x = leader, nodeState[x])];
    
    print <<me, "marked", other, "as", newState, "new nodeState", nodeState[me], "new sbrDecision", sbrDecision[me]>>;
  }
  
  macro actOnSbrDecision(node) {
    await nodeState[node][node] # "down";
    
    print <<node, "before acting on the sbr decision", sbrDecision[node], "nodeState", nodeState[node]>>;

    nodeState := [n \in Nodes |-> IF n # node 
                                    THEN nodeState[n] 
                                    ELSE [m \in Nodes |->
                                      IF sbrDecision[n] = "DownUnreachables" /\ nodeState[n][m] = "unreachable" 
                                        THEN "down"
                                        ELSE IF sbrDecision[n] = "DownMyself" /\ n = m
                                          THEN "down"
                                          ELSE nodeState[n][m]
                                    ]
                 ];

    sbrDecision := [x \in Nodes |-> IF x = node /\ sbrDecision[x] = "DownUnreachables" THEN "NoAction" ELSE sbrDecision[x]];
    
    print <<node, "after acting on the sbr decision", sbrDecision[node], "nodeState", nodeState[node]>>;
  }
  
  fair process (P \in Nodes \X Nodes)
  variables me = self[1], other = self[2];
  {
      Check: while(nodeState[me][me] # "down" /\ me # other) {
               Receive: either { receiveMemberState(me, other, "unreachable"); }
                        or     { receiveMemberState(me, other, "up"); };
               Act:     actOnSbrDecision(me);
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

SbrDecision(isLeader, state) ==
  IF (isLeader) THEN
    IF(InMajority(state)) THEN "DownUnreachables" ELSE "DownMyself"
  ELSE
    IF(InMajority(state)) THEN "NoAction" ELSE "DownMyself"

VARIABLES me, other

vars == << nodeState, leader, sbrDecision, pc, me, other >>

ProcSet == (Nodes \X Nodes)

Init == (* Global variables *)
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ leader = 1
        /\ sbrDecision = [n \in Nodes |-> "NoAction"]
        (* Process P *)
        /\ me = [self \in Nodes \X Nodes |-> self[1]]
        /\ other = [self \in Nodes \X Nodes |-> self[2]]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF nodeState[me[self]][me[self]] # "down" /\ me[self] # other[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << nodeState, leader, sbrDecision, me, other >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ PrintT(<<me[self], "received", other[self], "as", "unreachable", "previous nodeState", nodeState[me[self]], "previous sbrDecision", sbrDecision[me[self]]>>)
                       /\ nodeState' = [nodeState EXCEPT ![me[self]] = [nodeState[me[self]] EXCEPT ![other[self]] = "unreachable"]]
                       /\ sbrDecision' = [x \in Nodes |-> SbrDecision(x = leader, nodeState'[x])]
                       /\ PrintT(<<me[self], "marked", other[self], "as", "unreachable", "new nodeState", nodeState'[me[self]], "new sbrDecision", sbrDecision'[me[self]]>>)
                    \/ /\ PrintT(<<me[self], "received", other[self], "as", "up", "previous nodeState", nodeState[me[self]], "previous sbrDecision", sbrDecision[me[self]]>>)
                       /\ nodeState' = [nodeState EXCEPT ![me[self]] = [nodeState[me[self]] EXCEPT ![other[self]] = "up"]]
                       /\ sbrDecision' = [x \in Nodes |-> SbrDecision(x = leader, nodeState'[x])]
                       /\ PrintT(<<me[self], "marked", other[self], "as", "up", "new nodeState", nodeState'[me[self]], "new sbrDecision", sbrDecision'[me[self]]>>)
                 /\ pc' = [pc EXCEPT ![self] = "Act"]
                 /\ UNCHANGED << leader, me, other >>

Act(self) == /\ pc[self] = "Act"
             /\ nodeState[me[self]][me[self]] # "down"
             /\ PrintT(<<me[self], "before acting on the sbr decision", sbrDecision[me[self]], "nodeState", nodeState[me[self]]>>)
             /\ nodeState' = [n \in Nodes |-> IF n # me[self]
                                                THEN nodeState[n]
                                                ELSE [m \in Nodes |->
                                                  IF sbrDecision[n] = "DownUnreachables" /\ nodeState[n][m] = "unreachable"
                                                    THEN "down"
                                                    ELSE IF sbrDecision[n] = "DownMyself" /\ n = m
                                                      THEN "down"
                                                      ELSE nodeState[n][m]
                                                ]
                             ]
             /\ sbrDecision' = [x \in Nodes |-> IF x = me[self] /\ sbrDecision[x] = "DownUnreachables" THEN "NoAction" ELSE sbrDecision[x]]
             /\ PrintT(<<me[self], "after acting on the sbr decision", sbrDecision'[me[self]], "nodeState", nodeState'[me[self]]>>)
             /\ pc' = [pc EXCEPT ![self] = "Check"]
             /\ UNCHANGED << leader, me, other >>

P(self) == Check(self) \/ Receive(self) \/ Act(self)

Next == (\E self \in Nodes \X Nodes: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes \X Nodes : WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Fri Sep 14 10:12:14 CEST 2018 by bekiroguz
\* Created Mon Sep 03 15:16:19 CEST 2018 by bekiroguz
