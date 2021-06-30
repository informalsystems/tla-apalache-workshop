------------------------------ MODULE MC6 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)

EXTENDS Integers

CHAINS == { "A", "B" }
CHANNELS ==
    LET \* @type: (Str, Str) => <<Str, Str>>;
        pair(i, j) == <<i, j>>
    IN
    { pair("A", "B") }
ACCOUNTS == { "reserve", "escrow", "anna", "boris" }
GENESIS_SUPPLY == [ c \in CHAINS |-> 100 ]

\* introduce the global variables
VARIABLES
    \* @type: <<CHAIN, ACCOUNT>> -> Int;
    banks,
    \* @type: Set([src: CHAIN, dest: CHAIN, data: [sender: ACCOUNT, receiver: ACCOUNT, amount: Int]]);
    sentPackets

INSTANCE TokenTransfer6
===============================================================================
