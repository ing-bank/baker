----------------------------- MODULE ClusterV4 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes

ASSUME Cardinality(Nodes) > 0

(* 
--algorithm ClusterV4 { 
  
  define {
  
    Majority(S) == ((Cardinality(S) + 1) \div 2) \* calculate the majority number of nodes of all participating cluster nodes (including myself)

    InMajority(members, unreachables) == IF Cardinality(members \ unreachables) >= Majority(members) THEN TRUE ELSE FALSE

    InMinority(members, unreachables) == ~ InMajority(members, unreachables)
    
    NodesToDown(members, unreachables) == 
      IF Cardinality(members) = 0 
      THEN Nodes \* Down all known nodes since I am not a member and I do not know any members
      ELSE IF Cardinality(unreachables) * 2 = Cardinality(members) \* cannot decide minority or majority? equal size?
           THEN unreachables \* Decide to down unreachables in this case (could also pick the group with oldest member)
           ELSE IF Cardinality(unreachables) * 2 < Cardinality(members) \* am I in minority?
                THEN unreachables
                ELSE members \ unreachables \* down reachables      
  }
  
  fair process (N \in Nodes)
  variables leader = self = CHOOSE x \in Nodes: TRUE, \* choose one random node as leader in the beginning
            unreachables = {},
            members = Nodes;
  {
\*      Check: while(\E m \in members : m = self) {
      Check: while(TRUE) {
               Receive: either with (n \in Nodes \ {self}) { \* receive unreachable member message
                                 unreachables := unreachables \cup {n};
                                 members := members \cup {n};
                               }
                            or with (m \in members \ {self}) { \* receive reachable member message
                                 unreachables := unreachables \ {m};
                               } 
                            or with (n \in Nodes) { \* receive member up
                                 members := members \cup {n};
                               }
                            or with (n \in Nodes) { \* receive member removed
                                 members := members \ {n};
                                 unreachables := unreachables \ {n};
                               } 
                            or with (newLeader \in Nodes) { \* receive leader changed message
                                 leader := self = newLeader;
                               };
                 Sbr: if (leader /\ Cardinality(unreachables) # 0) {
                        with (nodesToDown = NodesToDown(members, unreachables)) {
                          if (Cardinality(nodesToDown) # 0) {
                            members := members \ nodesToDown;
                            unreachables := unreachables \ nodesToDown;
                          }
                        }
                      }  
             }  
  }

}
*)
\* BEGIN TRANSLATION
VARIABLE pc

(* define statement *)
Majority(S) == ((Cardinality(S) + 1) \div 2)

InMajority(members, unreachables) == IF Cardinality(members \ unreachables) >= Majority(members) THEN TRUE ELSE FALSE

InMinority(members, unreachables) == ~ InMajority(members, unreachables)

NodesToDown(members, unreachables) ==
  IF Cardinality(members) = 0
  THEN Nodes
  ELSE IF Cardinality(unreachables) * 2 = Cardinality(members)
       THEN unreachables
       ELSE IF Cardinality(unreachables) * 2 < Cardinality(members)
            THEN unreachables
            ELSE members \ unreachables

VARIABLES leader, unreachables, members

vars == << pc, leader, unreachables, members >>

ProcSet == (Nodes)

Init == (* Process N *)
        /\ leader = [self \in Nodes |-> self = CHOOSE x \in Nodes: TRUE]
        /\ unreachables = [self \in Nodes |-> {}]
        /\ members = [self \in Nodes |-> Nodes]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ pc' = [pc EXCEPT ![self] = "Receive"]
               /\ UNCHANGED << leader, unreachables, members >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ \E n \in Nodes \ {self}:
                            /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \cup {n}]
                            /\ members' = [members EXCEPT ![self] = members[self] \cup {n}]
                       /\ UNCHANGED leader
                    \/ /\ \E m \in members[self] \ {self}:
                            unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {m}]
                       /\ UNCHANGED <<leader, members>>
                    \/ /\ \E n \in Nodes:
                            members' = [members EXCEPT ![self] = members[self] \cup {n}]
                       /\ UNCHANGED <<leader, unreachables>>
                    \/ /\ \E n \in Nodes:
                            /\ members' = [members EXCEPT ![self] = members[self] \ {n}]
                            /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {n}]
                       /\ UNCHANGED leader
                    \/ /\ \E newLeader \in Nodes:
                            leader' = [leader EXCEPT ![self] = self = newLeader]
                       /\ UNCHANGED <<unreachables, members>>
                 /\ pc' = [pc EXCEPT ![self] = "Sbr"]

Sbr(self) == /\ pc[self] = "Sbr"
             /\ IF leader[self] /\ Cardinality(unreachables[self]) # 0
                   THEN /\ LET nodesToDown == NodesToDown(members[self], unreachables[self]) IN
                             IF Cardinality(nodesToDown) # 0
                                THEN /\ members' = [members EXCEPT ![self] = members[self] \ nodesToDown]
                                     /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ nodesToDown]
                                ELSE /\ TRUE
                                     /\ UNCHANGED << unreachables, members >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << unreachables, members >>
             /\ pc' = [pc EXCEPT ![self] = "Check"]
             /\ UNCHANGED leader

N(self) == Check(self) \/ Receive(self) \/ Sbr(self)

Next == (\E self \in Nodes: N(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(N(self))

\* END TRANSLATION


(* Check the types OK in each state *)
TypeOK == /\ \A node \in Nodes : leader[node] \in BOOLEAN
          /\ \A node \in Nodes : \A member \in members[node] : member \in Nodes
          /\ \A node \in Nodes : \A member \in unreachables[node] : member \in Nodes
          
(* There is only one leader *)
ConsistentLeader == \E node \in Nodes : leader[node] = TRUE 
                                     /\ \A other \in Nodes \ {node} : leader[other] = FALSE

(* There is no situation like members_A \intersect members_B is empty set. i.e. state_A={A,B} state_B={A,B} state_C={C}*)                     
NoSplitBrain == ~ \E n1 \in Nodes : 
                    \E n2 \in Nodes \ {n1} : 
                      members[n1] \cap members[n2] = {}

(* One invariant combining all others *)
Invariants == /\ TypeOK    
              /\ ConsistentLeader
              /\ NoSplitBrain
          
=============================================================================
\* Modification History
\* Last modified Tue Sep 25 17:08:27 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
