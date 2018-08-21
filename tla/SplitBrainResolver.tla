-------------------------------- MODULE SplitBrainResolver --------------------------------
EXTENDS Naturals, FiniteSets, TLC

VARIABLE othersState, \* current known state of others (my knowledge)
         amIMember, \* TRUE/FALSE
         nrOfOtherMembers,
         otherNodes
         
PrintVal(id, exp) == Print(<<id, exp>>, TRUE)

Majority == ((Cardinality(otherNodes) + 1) \div 2) + 1 \* calculate the majority number of nodes of all participating cluster nodes (including myself)

TotalUp(newState) == LET sum[S \in SUBSET otherNodes] == 
                     IF S = {} THEN 0
                     ELSE LET n == CHOOSE node \in S : TRUE
                          IN (IF newState[n] = "up" THEN 1 ELSE 0) + sum[S \ {n}]
                     IN sum[otherNodes] + 1

TypeOK == /\ othersState \in [otherNodes -> {"up", "unreachable"}]
          /\ amIMember \in {TRUE, FALSE}

UpdateMyState(newState) == IF TotalUp(newState) < Majority THEN FALSE ELSE TRUE

SetUp(n) == /\ othersState' = [othersState EXCEPT ![n] = "up"]
            /\ amIMember' = UpdateMyState(othersState')
            /\ UNCHANGED<<nrOfOtherMembers, otherNodes>>
            /\ PrintVal("NrOfUp SetUp", TotalUp(othersState'))

SetUnreachable(n) == /\ othersState' = [othersState EXCEPT ![n] = "unreachable"]
                     /\ amIMember' = UpdateMyState(othersState')
                     /\ UNCHANGED<<nrOfOtherMembers, otherNodes>>
                     /\ PrintVal("NrOfUp SetUnreachable", TotalUp(othersState'))

Init == /\ nrOfOtherMembers \in 1..2 \* excluding myself. I am always a member.
        /\ otherNodes = 1..nrOfOtherMembers \cup {} \* union with an empty set prints the set values like {1,2,3} instead of 1..3
        /\ othersState \in [otherNodes -> {"unreachable"}]
        /\ amIMember = FALSE
        /\ PrintVal("nrOfOtherMembers Init", nrOfOtherMembers)
        /\ PrintVal("NrOfUp members Init", TotalUp(othersState))
        /\ PrintVal("otherNodes Init", otherNodes)

Next == \E n \in otherNodes : SetUp(n) \/ SetUnreachable(n)

MyStateIsConsistent == amIMember = UpdateMyState(othersState)
        
\*OneNodeIsAlwaysRunning == \/ \E n \in otherNodes : othersState[n] = "up"
\*                          \/ myState = "up"

=============================================================================
\* Modification History
\* Last modified Tue Aug 21 17:22:22 CEST 2018 by bekiroguz
\* Created Wed Aug 15 12:26:52 CEST 2018 by bekiroguz
