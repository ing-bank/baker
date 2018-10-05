----------------------------- MODULE ClusterV6 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANT Nodes \* Set of model values representing the nodes

ASSUME Cardinality(Nodes) > 1

(* 
--algorithm ClusterV6 { 
  variables leader = LET a == ChooseOne(Nodes) \* choose one random node as leader in the beginning
                     IN [n \in Nodes |-> a],
            oldestNode = ChooseOne(Nodes), \* choose one random node as oldest node in the beginning                         
            
            \* start with a healthy cluster state, no unreachables and all nodes already member
            unreachables = [n \in Nodes |-> {}],
            members = [n \in Nodes |-> Nodes],
            deadNodes = {}, \* When a node is terminated, it cannot come back again. (For this version of the algorithm)
            debug = [n \in Nodes |-> <<"init=", n>>]; 

  define {
  
    \* Picks an arbitrary element from a given non-empty Set
    ChooseOne(S) == CHOOSE x \in S : TRUE
    
    \* Does set S contain given element x or not, returns a boolean result
    Contains(S, x) == Cardinality(S \cap {x}) = 1
    
    \* Is node still a member of the cluster
    IsMember(node) == Contains(members[node], node)
    
    \* Is the node leader
    IsLeader(node) == leader[node] = node
    
    Reachables(node) == members[node] \ unreachables[node]
    
    NodesToDown(n) == 
      IF Cardinality(members[n]) = 0 
      THEN Nodes \* Down all known nodes since I am not a member and I do not know any members
      ELSE IF Cardinality(unreachables[n]) * 2 = Cardinality(members[n]) \* cannot decide minority or majority? equal size?
           THEN IF Contains(unreachables[n], oldestNode) \* Check if the oldest node is unreachable, and let the group with oldest member survives
                THEN Reachables(n) \* down reachables
                ELSE unreachables[n] \* down unreachables
           ELSE IF Cardinality(unreachables[n]) * 2 < Cardinality(members[n]) \* am I in majority?
                THEN unreachables[n] \* down unreachables
                ELSE Reachables(n) \* down reachables      
  }
  
  \* a member may become unreachable or an unreachable message may be received by a non-member node which then becomes a member 
  macro ReceiveUnreachable() {
    if (IsMember(self)) {
      with (n \in Nodes \ ({self} \cup deadNodes)) {
        debug[self] := <<"receive unreachable=", n>>;
        unreachables[self] := unreachables[self] \cup {n}; \* add 'n' to the unreachables set
        members[self] := members[self] \cup {n}; \* add 'n' to the members set
      }
    }
  }
  
  \* an unreachable member may become reachable again
  macro ReceiveReachable() {
    if (IsMember(self)) {
      with (n \in unreachables[self] \  ({self} \cup deadNodes)) {
        debug[self] := <<"receive reachable=", n>>;
        unreachables[self] := unreachables[self] \ {n}; \* remove 'n' from the unreachables set
        members[self] := members[self] \cup {n}; \* add 'n' to the members set
      }
    }
  }
  
  \* a node joins cluster
  \* skipped for now, terminated nodes do not become UP again in this version.
  macro ReceiveMemberUp() {
    if (IsMember(self)) {
      \* members already up and members which were up but died cannot appear as new members again
      with (newMember \in Nodes \ (members[self] \cup deadNodes)) {
        debug[self] := <<"receive member up. newMember=", newMember>>;
    
        \* add new node to the members set
        members[self] := members[self] \cup {newMember};
        
\*        \* what is the initial state of the new member? It should know at least itself
\*        members := [n \in Nodes |-> IF n = self \/ n = newNode 
\*                                      \* new node should be already up and knows at least itself as member
\*                                      \* add node to my members set
\*                                      THEN members[n] \cup {newNode}
\*                                      ELSE members[n]
\*                   ];
      }
    }
  }
  
  \* a member leaves cluster
  macro ReceiveMemberRemoved() {
    if (IsMember(self) /\ Cardinality(members[self]) > 1) {
      with (memberToRemove \in members[self] \ {self}) {
        debug[self] := <<"receive member removed. memberToRemove=", memberToRemove>>;
    
        \* remove that node from my state and also make sure the state of that node is already updated
        members := [n \in Nodes |-> IF n = self 
                                      THEN members[self] \ {memberToRemove} \* remove node from my members set
                                      ELSE IF n = memberToRemove
                                             THEN {} \* members set of that node should be empty because it is down
                                             ELSE members[n]];
      
        \* remove node from unreachables set since it is down
        unreachables[self] := unreachables[self] \ {memberToRemove};
        
        \* mark this node as dead so it does not come back again
        deadNodes := deadNodes \cup {memberToRemove};
                                 
        \* choose another node as oldest node if oldest is down.
        if (memberToRemove = oldestNode) {
          oldestNode := ChooseOne(Nodes \ {memberToRemove});
        }                                 
      }
    }
  }
  
  \* Leader may change at any time
  macro ReceiveLeaderChanged() {
    if (IsMember(self) /\ ~IsLeader(self)) {
      with (newLeader \in Nodes \ ({leader[self]} \cup deadNodes), oldLeader = leader[self]) {
        debug[self] := <<"receive leader changed. newLeader=", newLeader>>;
      
        \* If the leader is changed, then the oldLeader must be either already unreachable or removed. Then we receive the new leader.
        if (Contains(unreachables[self], oldLeader) \/ ~Contains(members[self], oldLeader)) {
          \* assign the new leader 
          leader[self] := newLeader;        
        }
        
      }
    }
  }
  
  macro SbrDecision() {
    if (IsMember(self) /\ IsLeader(self) /\ Cardinality(unreachables[self]) > 0) {
      with (nodesToDown = NodesToDown(self)) {
        debug[self] := <<"sbr decision. nodesToDown=", nodesToDown>>;
        
        if (Contains(nodesToDown, self)) {
          \* leader going down
          members[self] := {};
          unreachables[self] := {};
          
          \* mark this node as dead so it does not come back again
          deadNodes := deadNodes \cup {self};      
          
          \* choose another node as oldest node if I am the oldest and going down.
          if(oldestNode = self) {
            oldestNode := ChooseOne(Nodes \ {self}); 
          }
        } else {
          members[self] := members[self] \ nodesToDown;
          unreachables[self] := unreachables[self] \ nodesToDown;
        }
      }
    }
  }
  
  fair process (N \in Nodes)            
  {
      Check: while(IsMember(self)) {
               Receive: either ReceiveUnreachable()
                            or ReceiveReachable() 
                            or ReceiveMemberRemoved()
                            or ReceiveLeaderChanged();
               Sbr: SbrDecision()  
             }  
  }

}
*)
\* BEGIN TRANSLATION
VARIABLES leader, oldestNode, unreachables, members, deadNodes, debug, pc

(* define statement *)
ChooseOne(S) == CHOOSE x \in S : TRUE


Contains(S, x) == Cardinality(S \cap {x}) = 1


IsMember(node) == Contains(members[node], node)


IsLeader(node) == leader[node] = node

Reachables(node) == members[node] \ unreachables[node]

NodesToDown(n) ==
  IF Cardinality(members[n]) = 0
  THEN Nodes
  ELSE IF Cardinality(unreachables[n]) * 2 = Cardinality(members[n])
       THEN IF Contains(unreachables[n], oldestNode)
            THEN Reachables(n)
            ELSE unreachables[n]
       ELSE IF Cardinality(unreachables[n]) * 2 < Cardinality(members[n])
            THEN unreachables[n]
            ELSE Reachables(n)


vars == << leader, oldestNode, unreachables, members, deadNodes, debug, pc >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ leader = (LET a == ChooseOne(Nodes)
                     IN [n \in Nodes |-> a])
        /\ oldestNode = ChooseOne(Nodes)
        /\ unreachables = [n \in Nodes |-> {}]
        /\ members = [n \in Nodes |-> Nodes]
        /\ deadNodes = {}
        /\ debug = [n \in Nodes |-> <<"init=", n>>]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ IF IsMember(self)
                     THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << leader, oldestNode, unreachables, members, 
                               deadNodes, debug >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ \/ /\ IF IsMember(self)
                             THEN /\ \E n \in Nodes \ ({self} \cup deadNodes):
                                       /\ debug' = [debug EXCEPT ![self] = <<"receive unreachable=", n>>]
                                       /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \cup {n}]
                                       /\ members' = [members EXCEPT ![self] = members[self] \cup {n}]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << unreachables, members, debug >>
                       /\ UNCHANGED <<leader, oldestNode, deadNodes>>
                    \/ /\ IF IsMember(self)
                             THEN /\ \E n \in unreachables[self] \  ({self} \cup deadNodes):
                                       /\ debug' = [debug EXCEPT ![self] = <<"receive reachable=", n>>]
                                       /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {n}]
                                       /\ members' = [members EXCEPT ![self] = members[self] \cup {n}]
                             ELSE /\ TRUE
                                  /\ UNCHANGED << unreachables, members, debug >>
                       /\ UNCHANGED <<leader, oldestNode, deadNodes>>
                    \/ /\ IF IsMember(self) /\ Cardinality(members[self]) > 1
                             THEN /\ \E memberToRemove \in members[self] \ {self}:
                                       /\ debug' = [debug EXCEPT ![self] = <<"receive member removed. memberToRemove=", memberToRemove>>]
                                       /\ members' = [n \in Nodes |-> IF n = self
                                                                        THEN members[self] \ {memberToRemove}
                                                                        ELSE IF n = memberToRemove
                                                                               THEN {}
                                                                               ELSE members[n]]
                                       /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ {memberToRemove}]
                                       /\ deadNodes' = (deadNodes \cup {memberToRemove})
                                       /\ IF memberToRemove = oldestNode
                                             THEN /\ oldestNode' = ChooseOne(Nodes \ {memberToRemove})
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED oldestNode
                             ELSE /\ TRUE
                                  /\ UNCHANGED << oldestNode, unreachables, 
                                                  members, deadNodes, debug >>
                       /\ UNCHANGED leader
                    \/ /\ IF IsMember(self) /\ ~IsLeader(self)
                             THEN /\ \E newLeader \in Nodes \ ({leader[self]} \cup deadNodes):
                                       LET oldLeader == leader[self] IN
                                         /\ debug' = [debug EXCEPT ![self] = <<"receive leader changed. newLeader=", newLeader>>]
                                         /\ IF Contains(unreachables[self], oldLeader) \/ ~Contains(members[self], oldLeader)
                                               THEN /\ leader' = [leader EXCEPT ![self] = newLeader]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED leader
                             ELSE /\ TRUE
                                  /\ UNCHANGED << leader, debug >>
                       /\ UNCHANGED <<oldestNode, unreachables, members, deadNodes>>
                 /\ pc' = [pc EXCEPT ![self] = "Sbr"]

Sbr(self) == /\ pc[self] = "Sbr"
             /\ IF IsMember(self) /\ IsLeader(self) /\ Cardinality(unreachables[self]) > 0
                   THEN /\ LET nodesToDown == NodesToDown(self) IN
                             /\ debug' = [debug EXCEPT ![self] = <<"sbr decision. nodesToDown=", nodesToDown>>]
                             /\ IF Contains(nodesToDown, self)
                                   THEN /\ members' = [members EXCEPT ![self] = {}]
                                        /\ unreachables' = [unreachables EXCEPT ![self] = {}]
                                        /\ deadNodes' = (deadNodes \cup {self})
                                        /\ IF oldestNode = self
                                              THEN /\ oldestNode' = ChooseOne(Nodes \ {self})
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED oldestNode
                                   ELSE /\ members' = [members EXCEPT ![self] = members[self] \ nodesToDown]
                                        /\ unreachables' = [unreachables EXCEPT ![self] = unreachables[self] \ nodesToDown]
                                        /\ UNCHANGED << oldestNode, deadNodes >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << oldestNode, unreachables, members, 
                                        deadNodes, debug >>
             /\ pc' = [pc EXCEPT ![self] = "Check"]
             /\ UNCHANGED leader

N(self) == Check(self) \/ Receive(self) \/ Sbr(self)

Next == (\E self \in Nodes: N(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(N(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


(* Check the types OK in each state *)
TypeOK == /\ oldestNode \in Nodes
          /\ \A n \in Nodes : leader[n] \in Nodes
          /\ \A n \in Nodes : members[n] \in SUBSET Nodes
          /\ \A n \in Nodes : unreachables[n] \in SUBSET Nodes
          /\ deadNodes \in SUBSET Nodes
          
(* There is only one leader *)
ConsistentLeader == \A n1 \in Nodes : 
                      \A n2 \in Nodes \ {n1} : 
                        \* Check leader equality if and only if the nodes are still a member 
                        IF Contains(members[n1], n1) /\ Contains(members[n2], n2)
                          THEN leader[n1] = leader[n2]
                          ELSE TRUE

(* At any moment this split brain state may happen which should be resolved at later steps. see SplitBrainRecovery temporal formula *)
SplitBrain == \E n1 \in Nodes : 
                \E n2 \in Nodes \ {n1} :
                     \* empty members set means that node is not part of the cluster
                     IF Cardinality(members[n1]) > 0 /\ Cardinality(members[n2]) > 0 
                       THEN members[n1] \cap members[n2] = {} \* Intersection of two sets is empty set (they have commons members)
                       ELSE FALSE

(* No splits detected in the cluster *)                       
NoSplitBrain == ~SplitBrain
                       
(* Temporal formula which gives the guarantee of the eventual resolution of the SplitBrain situation *)
SplitBrainRecovery == SplitBrain ~> (NoSplitBrain /\ ConsistentLeader)
          
=============================================================================
\* Modification History
\* Last modified Fri Oct 05 15:54:15 CEST 2018 by bekiroguz
\* Created Fri Sep 21 14:45:57 CEST 2018 by bekiroguz
