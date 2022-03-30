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
const_164864736155982000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164864736155983000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164864736155984000 == 
Permutations(const_164864736155982000) \union Permutations(const_164864736155983000)
----

=============================================================================
\* Modification History
\* Created Wed Mar 30 21:36:01 CST 2022 by wego
