------------------------------ MODULE MC1 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)

CHAINS == { "A", "B" }
ACCOUNTS == { "reserve", "anna", "boris" }

\* introduce the global variables
VARIABLES
    \* @type: ADDR -> Int;
    banks

INSTANCE TokenTransfer1
===============================================================================
