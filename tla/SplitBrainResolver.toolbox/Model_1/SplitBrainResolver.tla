-------------------------------- MODULE SplitBrainResolver --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT otherNodes \* other participating nodes in the cluster (except myself)

VARIABLE othersState, \* current known state of others (my knowledge)
         myState \* I can be either 'up' or 'down'

Majority == ((Cardinality(otherNodes) + 1) \div 2) + 1 \* calculate the majority number of nodes of all participating cluster nodes (including myself)

NrOfUp == Cardinality([n \in otherNodes |-> othersState[n] = "up"]) + 1 \* Count the number of "up" nodes (including myself)

TypeOK == /\ othersState \in [otherNodes -> {"up", "unreachable"}]
          /\ myState \in {"up", "down"}

\* TypeOK == nodeState \in [nodes -> {"joining", "up", "leaving", "exiting", "removed", "down", "unreachable"}]
          
\* ASSUME /\ selfNode \in nodes          
          
UpdateMyState == IF NrOfUp < Majority THEN "down" ELSE "up"

SetUp(n) == /\ othersState' = [othersState EXCEPT ![n] = "up"]
            /\ myState' = UpdateMyState

SetUnreachable(n) == /\ othersState' = [othersState EXCEPT ![n] = "unreachable"]
                     /\ myState' = UpdateMyState

Init == /\ othersState \in [otherNodes -> {"up"}]
        /\ myState = "up"

Next == \E n \in otherNodes : SetUp(n) \/ SetUnreachable(n)
        
\* OneNodeIsAlwaysRunning == \E n \in nodes : nodeState[n] = "up"

=============================================================================
\* Modification History
\* Last modified Mon Aug 20 17:37:04 CEST 2018 by bekiroguz
\* Created Wed Aug 15 12:26:52 CEST 2018 by bekiroguz
