----------------------- MODULE TokenTransfer6 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
 * Version 6: introducing basic packet send from source
 * Version 5: introducing an inductive invariant for Apalache
 * Version 4: bounding the amounts to help the model checkers
 * Version 3: fixing the invariants and introducing more
 * Version 2: let the banks do the local banking
 * Version 1: introducing data structures
 *
 * Igor Konnov, 2021
 *)
EXTENDS Integers

CONSTANT
    \* A set of blockchains, i.e., their names
    \* @type: Set(Str);
    CHAINS,
    \* A set of channels, that is, pairs of chains
    \* @type: Set(<<Str, Str>>);
    CHANNELS,
    \* A set of accounts, i.e., their names
    \* @type: Set(Str);
    ACCOUNTS,
    \* A set of all possible amounts
    \* @type: Set(Int);
    AMOUNTS,
    \* Initial supply for every chain
    \* @type: Str -> Int;
    GENESIS_SUPPLY


VARIABLES
    \* For every chain and account, store the amount of tokens in the account
    \* @type: <<Str, Str>> -> Int;
    banks,
    \* Packets that are sent by one chain to another (e.g., via an IBC channel)
    \* @type: Set([src: Str, dest: Str, data: [sender: Str, receiver: Str, amount: Int]]);
    sentPackets

(*************************** OPERATORS ***************************************)
\* For simplicity, we fix the name of the escrow account.
\* In ICS20, one introduces one escrow account per channel.
Escrow == "escrow"

RECURSIVE SumAddresses(_)
SumAddresses(Addrs) ==
    IF Addrs = {}
    THEN 0
    ELSE LET addr == CHOOSE a \in Addrs: TRUE IN
         banks[addr] + SumAddresses(Addrs \ {addr})

ChainSupply(chain) ==
    SumAddresses({chain} \X ACCOUNTS)

(**************************** SYSTEM *****************************************)

\* Initialize the world, e.g., from the last upgrade
Init ==
    /\ sentPackets = {}
    /\ \E b \in [ CHAINS \X ACCOUNTS -> AMOUNTS ]:
        /\ \A chain \in CHAINS:
            b[chain, "reserve"] > 0
        /\ banks = b
        /\ \A c \in CHAINS:
             ChainSupply(c) = GENESIS_SUPPLY[c]

\* Transfer the tokens from on account to another (on the same chain)
LocalTransfer(chain, from, to, amount) ==
    /\ banks[chain, from] >= amount
    /\ from /= to
    /\ banks' = [banks EXCEPT
            ![chain, from] = banks[chain, from] - amount,
            ![chain, to]   = banks[chain, to]   + amount
        ]

\* A computation on the local chain
LocalStep ==
    /\ \E chain \in CHAINS, from, to \in ACCOUNTS, amount \in AMOUNTS:
        /\ from /= Escrow
        /\ to /= Escrow
        /\ LocalTransfer(chain, from, to, amount)
    /\ UNCHANGED sentPackets

\* Send a packet to transfer tokens
SendPacketFromSource ==
    \E chan \in CHANNELS, sender, receiver \in ACCOUNTS, amount \in AMOUNTS:
        /\ sender /= Escrow /\ receiver /= Escrow
        \* the source direction: escrow source tokens
        /\ LocalTransfer(chan[1], sender, Escrow, amount)
        /\ LET data == [sender |-> sender,
                        receiver |-> receiver,
                        amount |-> amount]
               packet == [src |-> chan[1], dest |-> chan[2], data |-> data]
           IN
           sentPackets' = sentPackets \union { packet }
        \* TODO: add the case ~isSource, that is, the other direction   

\* Update the world        
Next ==
    \/ LocalStep
    \/ SendPacketFromSource

(************************** PROPERTIES ***************************************)

\* every bank always has reserves
ReservesInv ==
    \A chain \in CHAINS:
        banks[chain, "reserve"] > 0

\* no bank account goes negative
NoNegativeAccounts ==
    \A address \in DOMAIN banks:
        banks[address] >= 0

\* the supply remains constant
ChainSupplyUnchanged ==
    \A chain \in CHAINS:
        LET supply == ChainSupply(chain) IN
        supply = GENESIS_SUPPLY[chain]

\* for each in-fly packet, there is enough money in the escrow account
InFlyPacketIsSecured ==
    \A p \in sentPackets:
        banks[p.src, Escrow] >= p.amount


(***************** INDUCTIVE INVARIANT ***************************************)
(*

TODO: update the inductive invariant

TypeOK ==
    banks \in [ CHAINS \X ACCOUNTS -> AMOUNTS ]

IndInv ==
    /\ TypeOK
    /\ \A c \in CHAINS:
        ChainSupply(c) = GENESIS_SUPPLY[c]
 *)        

===============================================================================
