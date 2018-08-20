---- MODULE MC ----
EXTENDS SplitBrainResolver, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
B, C
----

\* MV CONSTANT definitions otherNodes
const_153478013934911000 == 
{B, C}
----

\* SYMMETRY definition
symm_153478013934912000 == 
Permutations(const_153478013934911000)
----

\* Constant expression definition @modelExpressionEval
const_expr_153478013934913000 == 
Majority
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_153478013934913000>>)
----

\* INIT definition @modelBehaviorInit:0
init_153478013935014000 ==
Init
----
\* NEXT definition @modelBehaviorNext:0
next_153478013935015000 ==
Next
----
=============================================================================
\* Modification History
\* Created Mon Aug 20 17:48:59 CEST 2018 by bekiroguz
