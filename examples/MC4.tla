------------------------------ MODULE MC4 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)
EXTENDS Integers

CHAINS == { "A", "B" }
ACCOUNTS == { "reserve", "anna", "boris" }
AMOUNTS == 0..5
GENESIS_SUPPLY == [ c \in CHAINS |-> 5 ]

\* introduce the global variables
VARIABLES
    \* @type: <<Str, Str>> -> Int;
    banks

\* we have 3 accounts per chain, so SumAdresses has to be unrolled up to 3 times
UNROLL_TIMES_SumAddresses == 3
\* when the recursive operator is unrolled UNROLL_TIMES_SumAddresses times,
\* use UNROLL_DEFAULT_SumAddresses as a default
UNROLL_DEFAULT_SumAddresses == 0

INSTANCE TokenTransfer4
===============================================================================
