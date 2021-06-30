------------------------------ MODULE MC3 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)
CHAINS == { "A", "B" }
ACCOUNTS == { "reserve", "anna", "boris" }
\* We fix the initial supply.
\* Alternatively, we could introduce a constant initializer ConstInit
\* and call apalache with --cinit=ConstInit
GENESIS_SUPPLY == [ c \in CHAINS |-> 100 ]

\* introduce the global variables
VARIABLES
    \* @type: ADDR -> Int;
    banks

INSTANCE TokenTransfer3
===============================================================================
