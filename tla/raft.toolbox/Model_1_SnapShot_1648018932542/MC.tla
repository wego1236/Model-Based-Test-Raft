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
const_164801893051117000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_164801893051118000 == 
{s1, s2, s3}
----

\* SYMMETRY definition
symm_164801893051119000 == 
Permutations(const_164801893051117000) \union Permutations(const_164801893051118000)
----

=============================================================================
\* Modification History
\* Created Wed Mar 23 15:02:10 CST 2022 by wego
