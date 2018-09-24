----------------------------- MODULE ClusterV4 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT NumNodes

ASSUME NumNodes > 0

Nodes == 1..NumNodes \* Set of all nodes

(* 
--algorithm ClusterV4 { 
  variables nodeState = [n \in Nodes |-> 
                                         [m \in Nodes |-> "up"]],
            sbrDecision = [n \in Nodes |-> "NoAction"];
            

  define {
    Min(S) == CHOOSE x \in S : \A y \in S : x <= y
    
    TotalUp(state) == LET sum[S \in SUBSET Nodes] ==
                            IF S = {} THEN 0
                            ELSE LET n == CHOOSE node \in S : TRUE
                                 IN (IF state[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                      IN sum[Nodes]
                         
    Majority == ((NumNodes + 1) \div 2) \* calculate the majority number of nodes of all participating cluster nodes (including myself)

    InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE
    
    SbrDecision(amILeader, myState) ==
      IF (amILeader) THEN
        IF(InMajority(myState)) THEN "DownUnreachables" ELSE "DownMyself"
      ELSE
        IF(InMajority(myState)) THEN "NoAction" ELSE "DownMyself" 
              
  }
  
  macro receiveMemberState(member, newState) {
    nodeState[self] := [nodeState[self] EXCEPT ![member] = newState];
    sbrDecision := [sbrDecision EXCEPT ![self] = SbrDecision(isLeader, nodeState[self])];
  }
  
  macro actOnSbrDecision() {
    if (sbrDecision[self] # "NoAction") {
      nodeState := [n \in Nodes |-> IF n # self 
                                      THEN nodeState[n] 
                                      ELSE [m \in Nodes |->
                                        IF sbrDecision[self] = "DownUnreachables" /\ nodeState[n][m] = "unreachable" 
                                          THEN "down"
                                          ELSE IF sbrDecision[self] = "DownMyself" /\ m = self
                                            THEN "down"
                                            ELSE nodeState[n][m]
                                      ]
                   ];
      \* reset the sbr decision
      sbrDecision := [sbrDecision EXCEPT ![self] = "NoAction"];
    };
        
  }
  
  process (N \in Nodes)
  variables isLeader = self = Min(Nodes); \* first node (Min node) is elected as leader in the beginning
  {
\*      Check: while(TRUE) {
      Check: while(nodeState[self][self] = "up") {
               Receive: either {
                          with (member \in Nodes \ {self}) { \* pick one node from Nodes except me
                            if (nodeState[self][member] = "up") receiveMemberState(member, "unreachable");
                          } 
                        }
                        or {
                          with (member \in Nodes \ {self}) {
                            if (nodeState[self][member] = "unreachable") receiveMemberState(member, "up");
                          } 
                        }
                        or { 
                          with (newLeader \in Nodes) { \* receive leader changed message
                            isLeader := self = newLeader;
                          }  
                        };
               Act:     actOnSbrDecision();
             }  
  }

}
*)
\* BEGIN TRANSLATION
VARIABLES nodeState, sbrDecision, pc

(* define statement *)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

TotalUp(state) == LET sum[S \in SUBSET Nodes] ==
                        IF S = {} THEN 0
                        ELSE LET n == CHOOSE node \in S : TRUE
                             IN (IF state[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                  IN sum[Nodes]

Majority == ((NumNodes + 1) \div 2)

InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE

SbrDecision(amILeader, myState) ==
  IF (amILeader) THEN
    IF(InMajority(myState)) THEN "DownUnreachables" ELSE "DownMyself"
  ELSE
    IF(InMajority(myState)) THEN "NoAction" ELSE "DownMyself"

VARIABLE isLeader

vars == << nodeState, sbrDecision, pc, isLeader >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ sbrDecision = [n \in Nodes |-> "NoAction"]
        (* Process N *)
        /\ isLeader = [self \in Nodes |-> self = Min(Nodes)]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF nodeState[self][self] = "up"
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << nodeState, sbrDecision, isLeader >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ \E member \in Nodes \ {self}:
                            IF nodeState[self][member] = "up"
                               THEN /\ nodeState' = [nodeState EXCEPT ![self] = [nodeState[self] EXCEPT ![member] = "unreachable"]]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(isLeader[self], nodeState'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << nodeState, sbrDecision >>
                       /\ UNCHANGED isLeader
                    \/ /\ \E member \in Nodes \ {self}:
                            IF nodeState[self][member] = "unreachable"
                               THEN /\ nodeState' = [nodeState EXCEPT ![self] = [nodeState[self] EXCEPT ![member] = "up"]]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(isLeader[self], nodeState'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << nodeState, sbrDecision >>
                       /\ UNCHANGED isLeader
                    \/ /\ \E newLeader \in Nodes:
                            isLeader' = [isLeader EXCEPT ![self] = self = newLeader]
                       /\ UNCHANGED <<nodeState, sbrDecision>>
                 /\ pc' = [pc EXCEPT ![self] = "Act"]

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
             /\ UNCHANGED isLeader

N(self) == Check(self) \/ Receive(self) \/ Act(self)

Next == (\E self \in Nodes: N(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


(* Check the types OK in each state *)
TypeOK == /\ \A n \in Nodes : isLeader[n] \in BOOLEAN
          /\ \A n \in Nodes : sbrDecision[n] \in {"DownMyself", "DownUnreachables", "NoAction"}
          /\ \A n1 \in Nodes : \A n2 \in Nodes : nodeState[n1][n2] \in {"up", "down", "unreachable"}
          
(* At least one node must be UP and this node is the leader *)          
Availability == \E n \in Nodes : nodeState[n][n] = "up" /\ isLeader[n] = TRUE

(* There is only one leader*)
ConsistentLeader == \E n \in Nodes : isLeader[n] = TRUE 
                                     /\ \A other \in Nodes \ {n} : isLeader[other] = FALSE

(* One invariant combining all others *)
Invariants == /\ TypeOK    
              /\ Availability
              /\ ConsistentLeader 

          
\*Liveliness == /\ Spec
\*              /\ SF_vars(Next)
          
=============================================================================
\* Modification History
\* Last modified Mon Sep 24 15:06:47 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
