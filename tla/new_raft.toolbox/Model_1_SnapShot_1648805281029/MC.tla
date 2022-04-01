---- MODULE MC ----
EXTENDS new_raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2, v3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Value
const_164880521848830000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164880521848831000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164880521848832000 == 
Permutations(const_164880521848830000) \union Permutations(const_164880521848831000)
----

=============================================================================
\* Modification History
\* Created Fri Apr 01 17:26:58 CST 2022 by wego
