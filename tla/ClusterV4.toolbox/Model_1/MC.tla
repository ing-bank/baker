---- MODULE MC ----
EXTENDS ClusterV4, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D, E
----

\* MV CONSTANT definitions Nodes
const_1537797834876123000 == 
{A, B, C, D, E}
----

\* SYMMETRY definition
symm_1537797834876124000 == 
Permutations(const_1537797834876123000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1537797834876125000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1537797834876126000 ==
Invariants
----
=============================================================================
\* Modification History
\* Created Mon Sep 24 16:03:54 CEST 2018 by bekiroguz
