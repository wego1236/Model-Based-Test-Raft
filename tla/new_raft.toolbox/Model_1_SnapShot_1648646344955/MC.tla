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
const_164864632740678000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164864632740679000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164864632740680000 == 
Permutations(const_164864632740678000) \union Permutations(const_164864632740679000)
----

=============================================================================
\* Modification History
\* Created Wed Mar 30 21:18:47 CST 2022 by wego
