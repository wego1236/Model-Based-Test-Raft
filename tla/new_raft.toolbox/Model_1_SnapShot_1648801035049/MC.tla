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
const_164880095046314000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_164880095046315000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164880095046316000 == 
Permutations(const_164880095046314000) \union Permutations(const_164880095046315000)
----

=============================================================================
\* Modification History
\* Created Fri Apr 01 16:15:50 CST 2022 by wego
