------------------------------ MODULE MC2 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)

CHAINS == { "A", "B" }
ACCOUNTS == { "reserve", "anna", "boris" }

\* introduce the global variables
VARIABLES
    \* @type: <<Str, Str>> -> Int;
    banks

INSTANCE TokenTransfer2
===============================================================================
