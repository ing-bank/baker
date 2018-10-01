---- MODULE MC ----
EXTENDS ClusterV4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C
----

\* MV CONSTANT definitions Nodes
const_1538403885192266000 == 
{A, B, C}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1538403885192267000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1538403885192268000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1538403885192269000 ==
NoSplitBrain
----
=============================================================================
\* Modification History
\* Created Mon Oct 01 16:24:45 CEST 2018 by bekiroguz
