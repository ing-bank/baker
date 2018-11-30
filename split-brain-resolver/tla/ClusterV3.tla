----------------------------- MODULE ClusterV3 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT NumNodes

ASSUME NumNodes > 0

Nodes == 1..NumNodes \* Set of all nodes

(* 
--algorithm ClusterV3 { 
  variables nodeState = [n \in Nodes |-> 
                                         [m \in Nodes |-> "up"]],
            leader = [n \in Nodes |-> 1], \* all nodes see the first one as leader
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
    await me # other;
  
\*    print <<me, "received", other, "as", newState, "previous nodeState", nodeState[me], "previous sbrDecision", sbrDecision[me]>>;

    nodeState[me] := [nodeState[me] EXCEPT ![other] = newState];

    sbrDecision := [sbrDecision EXCEPT ![me] = SbrDecision(me = leader[me], nodeState[me])];
        
\*    print <<me, "marked", other, "as", newState, "new nodeState", nodeState[me], "new sbrDecision", sbrDecision[me]>>;
  }
  
  macro actOnSbrDecision(me) {

    if (sbrDecision[me] # "NoAction") {
\*      print <<me, "before acting on the sbr decision", sbrDecision[me], "nodeState", nodeState[me]>>;
  
      nodeState := [n \in Nodes |-> IF n # me 
                                      THEN nodeState[n] 
                                      ELSE [m \in Nodes |->
                                        IF sbrDecision[me] = "DownUnreachables" /\ nodeState[n][m] = "unreachable" 
                                          THEN "down"
                                          ELSE IF sbrDecision[me] = "DownMyself" /\ m = me
                                            THEN "down"
                                            ELSE nodeState[n][m]
                                      ]
                   ];
    
      \* reset the sbr decision
      sbrDecision := [sbrDecision EXCEPT ![me] = "NoAction"];
\*      
\*      \* re-elect a new leader if the previous was DOWN
\*      leader[me] := IF nodeState[leader[me]][leader[me]] = "down"
\*                      THEN CHOOSE x \in Nodes \ {leader[me]} : TRUE
\*                      ELSE leader[me]
\*      
  
\*      print <<me, "after acting on the sbr decision", sbrDecision[me], "nodeState", nodeState[me]>>;
    };
        
  }
  
  process (P \in Nodes \X Nodes)
\*  variables me = self[1], 
\*            other = self[2];
  {
\*      Debug: print <<"Starting process", self>>;
      Check: while(self[1] # self[2] /\ nodeState[self[1]][self[1]] = "up") {
               Receive: either { 
                          if (nodeState[self[1]][self[2]] = "up") 
                            receiveMemberState(self[1], self[2], "unreachable"); 
                        }
                        or { 
                          if (nodeState[self[1]][self[2]] = "unreachable") 
                            receiveMemberState(self[1], self[2], "up"); 
                        };
               Act:     actOnSbrDecision(self[1]);
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


vars == << nodeState, leader, sbrDecision, pc >>

ProcSet == (Nodes \X Nodes)

Init == (* Global variables *)
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ leader = [n \in Nodes |-> 1]
        /\ sbrDecision = [n \in Nodes |-> "NoAction"]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF self[1] # self[2] /\ nodeState[self[1]][self[1]] = "up"
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << nodeState, leader, sbrDecision >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ IF nodeState[self[1]][self[2]] = "up"
                             THEN /\ (self[1]) # (self[2])
                                  /\ nodeState' = [nodeState EXCEPT ![(self[1])] = [nodeState[(self[1])] EXCEPT ![(self[2])] = "unreachable"]]
                                  /\ sbrDecision' = [sbrDecision EXCEPT ![(self[1])] = SbrDecision((self[1]) = leader[(self[1])], nodeState'[(self[1])])]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << nodeState, sbrDecision >>
                    \/ /\ IF nodeState[self[1]][self[2]] = "unreachable"
                             THEN /\ (self[1]) # (self[2])
                                  /\ nodeState' = [nodeState EXCEPT ![(self[1])] = [nodeState[(self[1])] EXCEPT ![(self[2])] = "up"]]
                                  /\ sbrDecision' = [sbrDecision EXCEPT ![(self[1])] = SbrDecision((self[1]) = leader[(self[1])], nodeState'[(self[1])])]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << nodeState, sbrDecision >>
                 /\ pc' = [pc EXCEPT ![self] = "Act"]
                 /\ UNCHANGED leader

Act(self) == /\ pc[self] = "Act"
             /\ IF sbrDecision[(self[1])] # "NoAction"
                   THEN /\ nodeState' = [n \in Nodes |-> IF n # (self[1])
                                                           THEN nodeState[n]
                                                           ELSE [m \in Nodes |->
                                                             IF sbrDecision[(self[1])] = "DownUnreachables" /\ nodeState[n][m] = "unreachable"
                                                               THEN "down"
                                                               ELSE IF sbrDecision[(self[1])] = "DownMyself" /\ m = (self[1])
                                                                 THEN "down"
                                                                 ELSE nodeState[n][m]
                                                           ]
                                        ]
                        /\ sbrDecision' = [sbrDecision EXCEPT ![(self[1])] = "NoAction"]
                   ELSE /\ TRUE
                        /\ UNCHANGED << nodeState, sbrDecision >>
             /\ pc' = [pc EXCEPT ![self] = "Check"]
             /\ UNCHANGED leader

P(self) == Check(self) \/ Receive(self) \/ Act(self)

Next == (\E self \in Nodes \X Nodes: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* Check the types OK in each state *)
TypeOK == /\ \A n \in Nodes : leader[n] \in Nodes
          /\ \A n \in Nodes : sbrDecision[n] \in {"DownMyself", "DownUnreachables", "NoAction"}
          /\ \A n1 \in Nodes : \A n2 \in Nodes : nodeState[n1][n2] \in {"up", "down", "unreachable"}
          
\*(* At least one node must be UP and this node is the leader *)          
\*Availability == \E n \in Nodes : nodeState[n][n] = "up" /\ leader[n] = n

(* At least one node must be UP *)          
Availability == \E n \in Nodes : nodeState[n][n] = "up"

(* Leader is same in all the nodes *)
ConsistentLeader == \A n1 \in Nodes : \A n2 \in Nodes: leader[n1] = leader[n2]

(* One invariant combining all others *)
Invariants == /\ TypeOK    
              /\ Availability
              /\ ConsistentLeader 

          
\*Liveliness == /\ Spec
\*              /\ SF_vars(Next)
          
=============================================================================
\* Modification History
\* Last modified Tue Sep 18 16:21:17 CEST 2018 by bekiroguz
\* Created Fri Sep 14 10:25:09 CEST 2018 by bekiroguz
