---- MODULE MC ----
EXTENDS raft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT definitions Value
const_164774705165611000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_164774705165612000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164774705165613000 == 
Permutations(const_164774705165611000) \union Permutations(const_164774705165612000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 20 11:30:51 CST 2022 by wego
