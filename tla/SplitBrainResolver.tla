-------------------------------- MODULE SplitBrainResolver --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT otherNodes \* other participating nodes in the cluster (except myself)

VARIABLE othersState, \* current known state of others (my knowledge)
         amIMember, \* TRUE/FALSE
         nrOfUp
         
Majority == ((Cardinality(otherNodes) + 1) \div 2) + 1 \* calculate the majority number of nodes of all participating cluster nodes (including myself)

TotalUp(newState) == LET sum[S \in SUBSET otherNodes] == 
                     IF S = {} THEN 0
                     ELSE LET n == CHOOSE node \in S : TRUE
                          IN (IF newState[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                     IN sum[otherNodes] + 1

TypeOK == /\ othersState \in [otherNodes -> {"up", "unreachable"}]
          /\ amIMember \in {TRUE, FALSE}

\* TypeOK == nodeState \in [nodes -> {"joining", "up", "leaving", "exiting", "removed", "down", "unreachable"}]
          
\* ASSUME /\ selfNode \in nodes          
          
UpdateMyState(newState) == IF TotalUp(newState) < Majority THEN FALSE ELSE TRUE

SetUp(n) == /\ othersState' = [othersState EXCEPT ![n] = "up"]
            /\ amIMember' = UpdateMyState(othersState')
            /\ nrOfUp' = TotalUp(othersState')

SetUnreachable(n) == /\ othersState' = [othersState EXCEPT ![n] = "unreachable"]
                     /\ amIMember' = UpdateMyState(othersState')
                     /\ nrOfUp' = TotalUp(othersState')

Init == /\ othersState \in [otherNodes -> {"up"}]
        /\ amIMember = TRUE
        /\ nrOfUp = 0

Next == \E n \in otherNodes : SetUp(n) \/ SetUnreachable(n)

MyStateIsConsistent == amIMember = UpdateMyState(othersState)
        
\*OneNodeIsAlwaysRunning == \/ \E n \in otherNodes : othersState[n] = "up"
\*                          \/ myState = "up"

=============================================================================
\* Modification History
\* Last modified Tue Aug 21 14:06:10 CEST 2018 by bekiroguz
\* Created Wed Aug 15 12:26:52 CEST 2018 by bekiroguz
