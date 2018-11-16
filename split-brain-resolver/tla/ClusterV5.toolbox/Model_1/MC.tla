---- MODULE MC ----
EXTENDS ClusterV5, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C
----

\* MV CONSTANT definitions Nodes
const_1538455027147122000 == 
{A, B, C}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1538455027147123000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1538455027147124000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1538455027147125000 ==
NoSplitBrain
----
=============================================================================
\* Modification History
\* Created Tue Oct 02 06:37:07 CEST 2018 by bekiroguz
