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
const_16477456787008000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_16477456787009000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164774567870010000 == 
Permutations(const_16477456787008000) \union Permutations(const_16477456787009000)
----

=============================================================================
\* Modification History
\* Created Sun Mar 20 11:07:58 CST 2022 by wego
