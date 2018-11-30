---- MODULE MC ----
EXTENDS ClusterV6, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C
----

\* MV CONSTANT definitions Nodes
const_153874711598218000 == 
{A, B, C}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_153874711598219000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_153874711598220000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_153874711598221000 ==
NoSplitBrain
----
=============================================================================
\* Modification History
\* Created Fri Oct 05 15:45:15 CEST 2018 by bekiroguz
