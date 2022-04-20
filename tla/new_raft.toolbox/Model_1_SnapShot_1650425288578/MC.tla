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
const_165042528200914000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_165042528200915000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_165042528200916000 == 
Permutations(const_165042528200914000) \union Permutations(const_165042528200915000)
----

=============================================================================
\* Modification History
\* Created Wed Apr 20 11:28:02 CST 2022 by wego
