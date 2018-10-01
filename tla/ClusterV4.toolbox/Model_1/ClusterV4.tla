----------------------------- MODULE ClusterV4 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes

ASSUME Cardinality(Nodes) > 1

(* 
--algorithm ClusterV4 { 
  
  define {
  
    \* Does set S contain given element x or not, returns a boolean result
    Contains(S, x) == Cardinality(S \cap {x}) = 1
    
    \* Picks an arbitrary element from a given non-empty Set
    ChooseOne(S) == CHOOSE x \in S : TRUE
    
    NodesToDown(members, unreachables, oldestNode) == 
      IF Cardinality(members) = 0 
      THEN Nodes \* Down all known nodes since I am not a member and I do not know any members
      ELSE IF Cardinality(unreachables) * 2 = Cardinality(members) \* cannot decide minority or majority? equal size?
           THEN IF Contains(unreachables, oldestNode) \* Check if the oldest node is unreachable, and let the group with oldest member survives
                THEN members \ unreachables \* down reachables
                ELSE unreachables
           ELSE IF Cardinality(unreachables) * 2 < Cardinality(members) \* am I in majority?
                THEN unreachables
                ELSE members \ unreachables \* down reachables      
  }
  
  process (N \in Nodes)
  variables leader = ChooseOne(Nodes), \* choose one random node as leader in the beginning
            unreachables = {},
            members = Nodes, \* start with a healthy cluster state
            oldestNode = ChooseOne(Nodes); \* pick one node as oldest
  {
      Check: while(Contains(members, self)) {
               Receive: either with (n \in Nodes \ {self}) { \* receive unreachable member message
                                 unreachables := unreachables \cup {n};
                                 members := members \cup {n};
                               }
                            or with (m \in unreachables \ {self}) { \* receive reachable member message
                                 unreachables := unreachables \ {m};
                               } 
                            or with (n \in Nodes \ {members}) { \* receive member up
                                 members := members \cup {n};
                               }
                            or with (n \in members \ {self}) { \* receive member removed
                                 if (n = oldestNode) { \* choose another node as oldest node if oldest is not a member anymore. /TODO maybe this should be a global variable as well, like leader.
                                   oldestNode := ChooseOne(Nodes \ {oldestNode});
                                 };
                                 members := members \ {n};
                                 unreachables := unreachables \ {n};
                               }
                            or with (newLeader \in Nodes) { \* receive leader changed message
                                 leader := newLeader;
                               };
                 Sbr: if (leader = self /\ Cardinality(unreachables) > 0) {
                        with (nodesToDown = NodesToDown(members, unreachables, oldestNode)) {
                          if(Contains(nodesToDown, self)) { \* choose a new leader if leader is going down /TODO make this a global variable instead of a local process variable.
                            leader := ChooseOne(Nodes \ {self});
                          };
                          if (self = oldestNode) { \* choose another node as oldest node if it goes down. /TODO maybe this should be a global variable as well, like leader.
                            oldestNode := ChooseOne(Nodes \ {oldestNode}); 
                          };
                          members := members \ nodesToDown;
                          unreachables := unreachables \ nodesToDown;
                        }
                      }  
             }  
  }

}
*)
\* BEGIN TRANSLATION
VARIABLE pc

(* define statement *)
Contains(S, x) == Cardinality(S \cap {x}) = 1


ChooseOne(S) == CHOOSE x \in S : TRUE

NodesToDown(members, unreachables, oldestNode) ==
  IF Cardinality(members) = 0
  THEN Nodes
  ELSE IF Cardinality(unreachables) * 2 = Cardinality(members)
       THEN IF Contains(unreachables, oldestNode)
            THEN members \ unreachables
            ELSE unreachables
       ELSE IF Cardinality(unreachables) * 2 < Cardinality(members)
            THEN unreachables
            ELSE members \ unreachables

VARIABLES leader, unreachables, members, oldestNode

vars == << pc, leader, unreachables, members, oldestNode >>

ProcSet == (Nodes)

Init == (* Process N *)
        /\ leader = [self \in Nodes |-> ChooseOne(Nodes)]
        /\ unreachables = [self \in Nodes |-> {}]
        /\ members = [self \in Nodes |-> Nodes]
        /\ oldestNode = [self \in Nodes |-> ChooseOne(Nodes)]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF Contains(members[self], self)
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << leader, unreachables, members, oldestNode >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ \E n \in Nodes \ {self}:
                            /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \cup {n}]
                            /\ members' = [members EXCEPT ![self] = members[self] \cup {n}]
                       /\ UNCHANGED <<leader, oldestNode>>
                    \/ /\ \E m \in unreachables[self] \ {self}:
                            unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {m}]
                       /\ UNCHANGED <<leader, members, oldestNode>>
                    \/ /\ \E n \in Nodes \ {members[self]}:
                            members' = [members EXCEPT ![self] = members[self] \cup {n}]
                       /\ UNCHANGED <<leader, unreachables, oldestNode>>
                    \/ /\ \E n \in members[self] \ {self}:
                            /\ IF n = oldestNode[self]
                                  THEN /\ oldestNode' = [oldestNode EXCEPT ![self] = ChooseOne(Nodes \ {oldestNode[self]})]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED oldestNode
                            /\ members' = [members EXCEPT ![self] = members[self] \ {n}]
                            /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {n}]
                       /\ UNCHANGED leader
                    \/ /\ \E newLeader \in Nodes:
                            leader' = [leader EXCEPT ![self] = newLeader]
                       /\ UNCHANGED <<unreachables, members, oldestNode>>
                 /\ pc' = [pc EXCEPT ![self] = "Sbr"]

Sbr(self) == /\ pc[self] = "Sbr"
             /\ IF leader[self] = self /\ Cardinality(unreachables[self]) > 0
                   THEN /\ LET nodesToDown == NodesToDown(members[self], unreachables[self], oldestNode[self]) IN
                             /\ IF Contains(nodesToDown, self)
                                   THEN /\ leader' = [leader EXCEPT ![self] = ChooseOne(Nodes \ {self})]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED leader
                             /\ IF self = oldestNode[self]
                                   THEN /\ oldestNode' = [oldestNode EXCEPT ![self] = ChooseOne(Nodes \ {oldestNode[self]})]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED oldestNode
                             /\ members' = [members EXCEPT ![self] = members[self] \ nodesToDown]
                             /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ nodesToDown]
                   ELSE /\ TRUE
                        /\ UNCHANGED << leader, unreachables, members, 
                                        oldestNode >>
             /\ pc' = [pc EXCEPT ![self] = "Check"]

N(self) == Check(self) \/ Receive(self) \/ Sbr(self)

Next == (\E self \in Nodes: N(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


(* Check the types OK in each state *)
TypeOK == /\ \A node \in Nodes : leader[node] \in Nodes
          /\ \A node \in Nodes : oldestNode[node] \in Nodes
          /\ \A node \in Nodes : \A member \in members[node] : member \in Nodes
          /\ \A node \in Nodes : \A member \in unreachables[node] : member \in Nodes
          
(* There is only one leader *)
ConsistentLeader == \A n1 \in Nodes : 
                      \A n2 \in Nodes \ {n1} : 
                        leader[n1] = leader[n2]

(* There is no situation like members_A \intersect members_B is empty set. i.e. state_A={A,B} state_B={A,B} state_C={C}*)                     
NoSplitBrain == \A n1 \in Nodes : 
                  \A n2 \in Nodes \ {n1} : 
                    members[n1] \cap members[n2] # {}

\*(* One invariant combining all others *)
\*Invariants == /\ TypeOK    
\*              /\ ConsistentLeader
\*              /\ NoSplitBrain
          
=============================================================================
\* Modification History
\* Last modified Mon Oct 01 16:22:25 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
