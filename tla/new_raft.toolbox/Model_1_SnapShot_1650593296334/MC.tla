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
const_16505927665942000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_16505927665943000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_16505927665944000 == 
Permutations(const_16505927665942000) \union Permutations(const_16505927665943000)
----

=============================================================================
\* Modification History
\* Created Fri Apr 22 09:59:26 CST 2022 by wego
