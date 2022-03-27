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
const_164834958876147000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164834958876148000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164834958876149000 == 
Permutations(const_164834958876147000) \union Permutations(const_164834958876148000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 27 10:53:08 CST 2022 by wego
