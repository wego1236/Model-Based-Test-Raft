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
const_16504251610676000 == 
{v1, v2, v3}
----

\* MV CONSTANT definitions Server
const_16504251610677000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_16504251610678000 == 
Permutations(const_16504251610676000) \union Permutations(const_16504251610677000)
----

=============================================================================
\* Modification History
\* Created Wed Apr 20 11:26:01 CST 2022 by wego
