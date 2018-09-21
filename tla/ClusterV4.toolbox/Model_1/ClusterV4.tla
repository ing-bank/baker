----------------------------- MODULE ClusterV4 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT NumNodes

ASSUME NumNodes > 0

Nodes == 1..NumNodes \* Set of all nodes

(* 
--algorithm ClusterV4 { 
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
  
  process (N \in Nodes)
  {
      Check: while(nodeState[self][self] = "up") {
               Receive: either {
                          with (other \in Nodes \ {self}) { \* pick one node from Nodes except me
                            if (nodeState[self][other] = "up") 
                              receiveMemberState(self, other, "unreachable");
                          } 
                        }
                        or { 
                          with (other \in Nodes \ {self}) {
                            if (nodeState[self][other] = "unreachable") 
                              receiveMemberState(self, other, "up");
                          } 
                        };
               Act:     actOnSbrDecision(self);
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

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ leader = [n \in Nodes |-> 1]
        /\ sbrDecision = [n \in Nodes |-> "NoAction"]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF nodeState[self][self] = "up"
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << nodeState, leader, sbrDecision >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ \E other \in Nodes \ {self}:
                            IF nodeState[self][other] = "up"
                               THEN /\ self # other
                                    /\ nodeState' = [nodeState EXCEPT ![self] = [nodeState[self] EXCEPT ![other] = "unreachable"]]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(self = leader[self], nodeState'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << nodeState, sbrDecision >>
                    \/ /\ \E other \in Nodes \ {self}:
                            IF nodeState[self][other] = "unreachable"
                               THEN /\ self # other
                                    /\ nodeState' = [nodeState EXCEPT ![self] = [nodeState[self] EXCEPT ![other] = "up"]]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(self = leader[self], nodeState'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << nodeState, sbrDecision >>
                 /\ pc' = [pc EXCEPT ![self] = "Act"]
                 /\ UNCHANGED leader

Act(self) == /\ pc[self] = "Act"
             /\ IF sbrDecision[self] # "NoAction"
                   THEN /\ nodeState' = [n \in Nodes |-> IF n # self
                                                           THEN nodeState[n]
                                                           ELSE [m \in Nodes |->
                                                             IF sbrDecision[self] = "DownUnreachables" /\ nodeState[n][m] = "unreachable"
                                                               THEN "down"
                                                               ELSE IF sbrDecision[self] = "DownMyself" /\ m = self
                                                                 THEN "down"
                                                                 ELSE nodeState[n][m]
                                                           ]
                                        ]
                        /\ sbrDecision' = [sbrDecision EXCEPT ![self] = "NoAction"]
                   ELSE /\ TRUE
                        /\ UNCHANGED << nodeState, sbrDecision >>
             /\ pc' = [pc EXCEPT ![self] = "Check"]
             /\ UNCHANGED leader

N(self) == Check(self) \/ Receive(self) \/ Act(self)

Next == (\E self \in Nodes: N(self))
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
\* Last modified Fri Sep 21 17:35:03 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
