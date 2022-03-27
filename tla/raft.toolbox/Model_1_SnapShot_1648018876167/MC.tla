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
const_164801887414314000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_164801887414315000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164801887414316000 == 
Permutations(const_164801887414314000) \union Permutations(const_164801887414315000)
----

=============================================================================
\* Modification History
\* Created Wed Mar 23 15:01:14 CST 2022 by wego
