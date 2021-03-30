------------------------------ MODULE MC8 -------------------------------------
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
AMOUNTS == Nat \*0..5 \* you can use Nat in Apalache
GENESIS_SUPPLY == [ c \in CHAINS |-> 100 ]
MK_DENOM == [
    c \in CHAINS, d \in DENOMS |->
        IF c = "A" /\ d = "B"
        THEN "A/B"
        ELSE IF c = "B" /\ d = "A"
        THEN "B/A"
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
    \* An imaginary global counter that we use to assign unique sequence numbers
    \* @type: Int;
    seqno

\* we have 3 accounts per chain, so SumAdresses has to be unrolled up to 3 times
UNROLL_TIMES_SumAddresses == 4
\* when the recursive operator is unrolled UNROLL_TIMES_SumAddresses times,
\* use UNROLL_DEFAULT_SumAddresses as a default
UNROLL_DEFAULT_SumAddresses == 0

INSTANCE TokenTransfer8
===============================================================================
