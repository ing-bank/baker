---- MODULE MC ----
EXTENDS SplitBrainResolver, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B, C
----

\* MV CONSTANT definitions otherNodes
const_153478015650421000 == 
{B, C}
----

\* SYMMETRY definition
symm_153478015650422000 == 
Permutations(const_153478015650421000)
----

\* Constant expression definition @modelExpressionEval
const_expr_153478015650423000 == 
Majority
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153478015650423000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_153478015650424000 ==
FALSE/\othersState = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_153478015650425000 ==
FALSE/\othersState' = othersState
----
=============================================================================
\* Modification History
\* Created Mon Aug 20 17:49:16 CEST 2018 by bekiroguz
