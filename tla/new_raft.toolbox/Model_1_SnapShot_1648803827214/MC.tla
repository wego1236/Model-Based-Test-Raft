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
const_164880381964026000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164880381964027000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164880381964028000 == 
Permutations(const_164880381964026000) \union Permutations(const_164880381964027000)
----

=============================================================================
\* Modification History
\* Created Fri Apr 01 17:03:39 CST 2022 by wego
