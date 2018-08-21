---- MODULE MC ----
EXTENDS SplitBrainResolver, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B, C, D, E
----

\* MV CONSTANT definitions otherNodes
const_1534853422160341000 == 
{B, C, D, E}
----

\* INIT definition @modelBehaviorInit:0
init_1534853422160342000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1534853422160343000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534853422160344000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534853422160345000 ==
MyStateIsConsistent
----
=============================================================================
\* Modification History
\* Created Tue Aug 21 14:10:22 CEST 2018 by bekiroguz
