---- MODULE MC ----
EXTENDS ClusterV6, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C
----

\* MV CONSTANT definitions Nodes
const_1538491739080336000 == 
{A, B, C}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1538491739080337000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1538491739080338000 ==
TypeOK
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1538491739080339000 ==
SplitBrainRecovery
----
=============================================================================
\* Modification History
\* Created Tue Oct 02 16:48:59 CEST 2018 by bekiroguz
