---- MODULE MC_tlc_check ----
EXTENDS ERC20, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A_Alice, A_Bob, A_Eve
----

\* MV CONSTANT definitions ADDR
const_165365715019242000 == 
{A_Alice, A_Bob, A_Eve}
----

\* SYMMETRY definition
symm_165365715019243000 == 
Permutations(const_165365715019242000)
----

\* CONSTANT definitions @modelParameterConstants:0AMOUNTS
const_165365715019244000 == 
0..19
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_165365715019245000 ==
\A a \in ADDR: balanceOf[a] \in AMOUNTS
----
=============================================================================
\* Modification History
\* Created Fri May 27 15:12:30 CEST 2022 by igor
