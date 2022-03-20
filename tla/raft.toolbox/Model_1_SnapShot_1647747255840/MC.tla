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
const_164774725382114000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_164774725382115000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164774725382116000 == 
Permutations(const_164774725382114000) \union Permutations(const_164774725382115000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 20 11:34:13 CST 2022 by wego
