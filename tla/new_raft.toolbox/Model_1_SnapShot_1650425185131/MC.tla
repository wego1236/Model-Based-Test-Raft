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
const_165042518309910000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_165042518309911000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_165042518309912000 == 
Permutations(const_165042518309910000) \union Permutations(const_165042518309911000)
----

=============================================================================
\* Modification History
\* Created Wed Apr 20 11:26:23 CST 2022 by wego
