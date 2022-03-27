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
const_164834831549930000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164834831549931000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164834831549932000 == 
Permutations(const_164834831549930000) \union Permutations(const_164834831549931000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 27 10:31:55 CST 2022 by wego
