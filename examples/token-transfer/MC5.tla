------------------------------ MODULE MC5 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)

CHAINS == { "A", "B" }
ACCOUNTS == { "reserve", "anna", "boris" }
GENESIS_SUPPLY == [ c \in CHAINS |-> 100 ]

\* introduce the global variables
VARIABLES
    \* @type: ADDR -> Int;
    banks

INSTANCE TokenTransfer5
===============================================================================
