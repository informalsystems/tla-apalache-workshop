------------------------------ MODULE MC10 -------------------------------------
(* Fix the CONSTANTS to run a model checker *)

EXTENDS Integers

CHAINS == { "A", "B" }
CHANNELS ==
    LET \* @type: (Str, Str) => <<Str, Str>>;
        pair(i, j) == <<i, j>>
    IN
    { pair("A", "B") }
ACCOUNTS == { "reserve", "escrow", "anna", "boris" }
DENOMS == { "A", "B", "B/A", "A/B" }
GENESIS_SUPPLY == [ c \in CHAINS |-> 100 ]
MK_DENOM == [
    c \in CHAINS, d \in DENOMS |->
        IF c = "A" /\ d = "B"
        THEN "A/B"
        ELSE IF c = "B" /\ d = "A"
        THEN "B/A"
        ELSE "invalid"
]
UNMK_DENOM == [
    c \in CHAINS, d \in DENOMS |->
        IF c = "A" /\ d = "A/B"
        THEN "B"
        ELSE IF c = "B" /\ d = "B/A"
        THEN "A"
        ELSE "invalid"
]

\* introduce the global variables
VARIABLES
    \* @type: <<Str, Str, Str>> -> Int;
    banks,
    \* @type: Set([seqno: Int, src: Str, dest: Str, data: [sender: Str, receiver: Str, denom: Str, amount: Int]]);
    sentPackets,
    \* The sequence numbers of delivered packets
    \* @type: Set(Int);
    deliveredNums,
    \* The sequence numbers of the packets that timed out, registered on destination
    \* @type: Set(Int);
    dstTimeoutNums,
    \* The sequence numbers of the packets that timed out, registered on source
    \* @type: Set(Int);
    srcTimeoutNums,
    \* An imaginary global counter that we use to assign unique sequence numbers
    \* @type: Int;
    seqno

INSTANCE TokenTransfer10
===============================================================================
