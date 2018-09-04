----------------------------- MODULE ClusterV2 -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC
CONSTANT NumNodes
Nodes == 1..NumNodes
\*States == {"up", "down", "unreachable"}
\*SbrDecisions == {"DownMyself", "DownUnreachables", "NoAction"}

(* 
--algorithm ClusterV2 {
  variables chan = [n \in Nodes |-> <<>>],
            nodeState = [n \in Nodes |-> 
                                         [m \in Nodes |-> "up"]],
            leader = CHOOSE n \in Nodes : TRUE;
\*            sbrDecision = [n \in Nodes |-> "NoAction"];

  define {
    PickOne(S) == CHOOSE i \in S: TRUE
  }
  
  macro memberUnreachable(m) {
    nodeState[self] := [nodeState[self] EXCEPT ![m] = "unreachable"];
    print <<self, "marked member", m, "unreachable", "nodeState", nodeState>>
  }   

  process (n \in Nodes)
  variables someMember;
  {
    Node: while(TRUE) {
            someMember := PickOne(Nodes \ {self});
            either { memberUnreachable(someMember); }
            or     { print "booo"; }
          }  
  }

}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES chan, nodeState, leader

(* define statement *)
PickOne(S) == CHOOSE i \in S: TRUE

VARIABLE someMember

vars == << chan, nodeState, leader, someMember >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ chan = [n \in Nodes |-> <<>>]
        /\ nodeState = [n \in Nodes |->
                                        [m \in Nodes |-> "up"]]
        /\ leader = (CHOOSE n \in Nodes : TRUE)
        (* Process n *)
        /\ someMember = [self \in Nodes |-> defaultInitValue]

n(self) == /\ someMember' = [someMember EXCEPT ![self] = PickOne(Nodes \ {self})]
           /\ \/ /\ nodeState' = [nodeState EXCEPT ![self] = [nodeState[self] EXCEPT ![someMember'[self]] = "unreachable"]]
                 /\ PrintT(<<self, "marked member", someMember'[self], "unreachable", "nodeState", nodeState'>>)
              \/ /\ PrintT("booo")
                 /\ UNCHANGED nodeState
           /\ UNCHANGED << chan, leader >>

Next == (\E self \in Nodes: n(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Sep 04 17:27:39 CEST 2018 by bekiroguz
\* Created Mon Sep 03 15:16:19 CEST 2018 by bekiroguz
