------------------------------ MODULE MC7 -------------------------------------
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
    \* @type: <<Str, Str>> -> Int;
    banks,
    \* @type: Set([seqno: Int, src: Str, dest: Str, data: [sender: Str, receiver: Str, amount: Int]]);
    sentPackets,
    \* The sequence numbers of delivered packets
    \* @type: Set(Int);
    deliveredNums,
    \* An imaginary global counter that we use to assign unique sequence numbers
    \* @type: Int;
    seqno

INSTANCE TokenTransfer7
===============================================================================
