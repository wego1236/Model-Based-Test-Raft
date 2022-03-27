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
const_164835207888163000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164835207888164000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164835207888165000 == 
Permutations(const_164835207888163000) \union Permutations(const_164835207888164000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 27 11:34:38 CST 2022 by wego
