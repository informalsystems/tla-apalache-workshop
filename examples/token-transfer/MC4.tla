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

INSTANCE TokenTransfer4
===============================================================================
