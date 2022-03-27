---- MODULE MC ----
EXTENDS raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Value
const_16477643536468000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_16477643536469000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164776435364610000 == 
Permutations(const_16477643536468000) \union Permutations(const_16477643536469000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 20 16:19:13 CST 2022 by wego
