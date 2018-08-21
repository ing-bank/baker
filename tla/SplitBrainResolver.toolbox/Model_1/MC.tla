---- MODULE MC ----
EXTENDS SplitBrainResolver, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B, C
----

\* MV CONSTANT definitions otherNodes
const_1534855550901376000 == 
{B, C}
----

\* INIT definition @modelBehaviorInit:0
init_1534855550901377000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_1534855550901378000 ==
Next
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1534855550901379000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1534855550901380000 ==
MyStateIsConsistent
----
=============================================================================
\* Modification History
\* Created Tue Aug 21 14:45:50 CEST 2018 by bekiroguz
