----------------------------- MODULE ClusterV4 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes

ASSUME Cardinality(Nodes) > 0

(* 
--algorithm ClusterV4 { 

  define {
    Min(S) == CHOOSE x \in S : \A y \in S : x <= y
    
    TotalUp(state) == LET sum[S \in SUBSET Nodes] ==
                            IF S = {} THEN 0
                            ELSE LET n == CHOOSE node \in S : TRUE
                                 IN (IF state[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                      IN sum[Nodes]
                         
    Majority == ((Cardinality(Nodes) + 1) \div 2) \* calculate the majority number of nodes of all participating cluster nodes (including myself)

    InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE
    
    SbrDecision(amILeader, myState) ==
      IF (amILeader) THEN
        IF(InMajority(myState)) THEN "DownUnreachables" ELSE "DownMyself"
      ELSE
        IF(InMajority(myState)) THEN "NoAction" ELSE "DownMyself" 
              
  }
  
  macro receiveMemberState(member, newState) {
    state[member] := newState;
    sbrDecision := SbrDecision(isLeader, state);
  }
  
  macro actOnSbrDecision() {
    if (sbrDecision # "NoAction") {
      state := [member \in Nodes |->
                 IF sbrDecision = "DownUnreachables" /\ state[member] = "unreachable"
                 THEN "down"
                 ELSE IF sbrDecision = "DownMyself" /\ member = self
                      THEN "down"
                      ELSE state[member]
               ];
               
      \* reset the sbr decision
      sbrDecision := "NoAction";
    };
        
  }
  
  process (N \in Nodes)
  variables isLeader = self = CHOOSE x \in Nodes: TRUE, \* choose one random node as leader in the beginning
            sbrDecision = "NoAction",
            state = [x \in Nodes |-> "up"];
  {
\*      Check: while(TRUE) {
      Check: while(state[self] = "up") {
               Receive: either {
                          with (member \in Nodes \ {self}) { \* pick one node from Nodes except me
                            if (state[member] = "up") receiveMemberState(member, "unreachable");
                          }
                        }
                        or {
                          with (member \in Nodes \ {self}) {
                            if (state[member] = "unreachable") receiveMemberState(member, "up");
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
VARIABLE pc

(* define statement *)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

TotalUp(state) == LET sum[S \in SUBSET Nodes] ==
                        IF S = {} THEN 0
                        ELSE LET n == CHOOSE node \in S : TRUE
                             IN (IF state[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                  IN sum[Nodes]

Majority == ((Cardinality(Nodes) + 1) \div 2)

InMajority(oneNodePerspectiveState) == IF TotalUp(oneNodePerspectiveState) >= Majority THEN TRUE ELSE FALSE

SbrDecision(amILeader, myState) ==
  IF (amILeader) THEN
    IF(InMajority(myState)) THEN "DownUnreachables" ELSE "DownMyself"
  ELSE
    IF(InMajority(myState)) THEN "NoAction" ELSE "DownMyself"

VARIABLES isLeader, sbrDecision, state

vars == << pc, isLeader, sbrDecision, state >>

ProcSet == (Nodes)

Init == (* Process N *)
        /\ isLeader = [self \in Nodes |-> self = CHOOSE x \in Nodes: TRUE]
        /\ sbrDecision = [self \in Nodes |-> "NoAction"]
        /\ state = [self \in Nodes |-> [x \in Nodes |-> "up"]]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF state[self][self] = "up"
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << isLeader, sbrDecision, state >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ \E member \in Nodes \ {self}:
                            IF state[self][member] = "up"
                               THEN /\ state' = [state EXCEPT ![self][member] = "unreachable"]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(isLeader[self], state'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << sbrDecision, state >>
                       /\ UNCHANGED isLeader
                    \/ /\ \E member \in Nodes \ {self}:
                            IF state[self][member] = "unreachable"
                               THEN /\ state' = [state EXCEPT ![self][member] = "up"]
                                    /\ sbrDecision' = [sbrDecision EXCEPT ![self] = SbrDecision(isLeader[self], state'[self])]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << sbrDecision, state >>
                       /\ UNCHANGED isLeader
                    \/ /\ \E newLeader \in Nodes:
                            isLeader' = [isLeader EXCEPT ![self] = self = newLeader]
                       /\ UNCHANGED <<sbrDecision, state>>
                 /\ pc' = [pc EXCEPT ![self] = "Act"]

Act(self) == /\ pc[self] = "Act"
             /\ IF sbrDecision[self] # "NoAction"
                   THEN /\ state' = [state EXCEPT ![self] = [member \in Nodes |->
                                                              IF sbrDecision[self] = "DownUnreachables" /\ state[self][member] = "unreachable"
                                                              THEN "down"
                                                              ELSE IF sbrDecision[self] = "DownMyself" /\ member = self
                                                                   THEN "down"
                                                                   ELSE state[self][member]
                                                            ]]
                        /\ sbrDecision' = [sbrDecision EXCEPT ![self] = "NoAction"]
                   ELSE /\ TRUE
                        /\ UNCHANGED << sbrDecision, state >>
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
          /\ \A n1 \in Nodes : \A n2 \in Nodes : state[n1][n2] \in {"up", "down", "unreachable"}
          
(* At least one node must be UP and this node is the leader *)          
Availability == \E n \in Nodes : state[n][n] = "up" /\ isLeader[n] = TRUE

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
\* Last modified Mon Sep 24 16:01:36 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
