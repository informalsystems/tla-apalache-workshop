----------------------- MODULE TokenTransfer8 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
 * Version 8: introducing basic denominations
 * Version 7: introducing basic packet receive from source
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
    GENESIS_SUPPLY,
    \* A set of denominations
    \* @type: Set(Str);
    DENOMS,
    \* A function that produces a new denomination for a chain a denomination
    \* @type: <<Str, Str>> -> Str;
    MK_DENOM

VARIABLES
    \* For every chain and account, store the amount of tokens in the account
    \* for each denomination
    \* @type: <<Str, Str, Str>> -> Int;
    banks,
    \* Packets that are sent by one chain to another (e.g., via an IBC channel)
    \* @type: Set([seqno: Int, src: Str, dest: Str, data: [sender: Str, receiver: Str, denom: Str, amount: Int]]);
    sentPackets,
    \* The sequence numbers of delivered packets
    \* @type: Set(Int);
    deliveredNums,
    \* An imaginary global counter that we use to assign unique sequence numbers
    \* @type: Int;
    seqno

(*************************** OPERATORS ***************************************)
\* For simplicity, we fix the name of the escrow account.
\* In ICS20, one introduces one escrow account per channel.
Escrow == "escrow"

\* For simplicity, we call the coin native if it has the same name as the chain
Native(chain) == chain

RECURSIVE SumAddresses(_)
SumAddresses(Addrs) ==
    IF Addrs = {}
    THEN 0
    ELSE LET addr == CHOOSE a \in Addrs: TRUE IN
         banks[addr] + SumAddresses(Addrs \ {addr})

ChainSupply(chain) ==
    SumAddresses({ chain } \X ACCOUNTS \X { Native(chain) })

(**************************** SYSTEM *****************************************)

\* Initialize the world, e.g., from the last upgrade
Init ==
    /\ seqno = 0
    /\ sentPackets = {}
    /\ deliveredNums = {}
    /\ \E b \in [ CHAINS \X ACCOUNTS \X DENOMS -> AMOUNTS ]:
        /\ \A chain \in CHAINS:
            /\ b[chain, "reserve", chain] > 0
            /\ \A a \in ACCOUNTS, d \in DENOMS:
                \* no tokens in foreign denominations
                d /= Native(chain) => b[chain, a, d] = 0
        /\ banks = b
        /\ \A c \in CHAINS:
             ChainSupply(c) = GENESIS_SUPPLY[c]

\* Transfer the tokens from on account to another (on the same chain)
LocalTransfer(chain, from, to, denom, amount) ==
    /\ banks[chain, from, denom] >= amount
    /\ from /= to
    /\ banks' = [banks EXCEPT
            ![chain, from, denom] = banks[chain, from, denom] - amount,
            ![chain, to, denom]   = banks[chain, to, denom]   + amount
        ]

\* A computation on the local chain
LocalStep ==
    /\ \E chain \in CHAINS, from, to \in ACCOUNTS,
                denom \in DENOMS, amount \in AMOUNTS:
        /\ from /= Escrow
        /\ to /= Escrow
        /\ LocalTransfer(chain, from, to, denom, amount)
    /\ UNCHANGED <<seqno, sentPackets, deliveredNums>>

\* Send a packet to transfer tokens (from the source)
SendPacketFromSource ==
    \E chan \in CHANNELS, sender, receiver \in ACCOUNTS,
            denom \in DENOMS, amount \in AMOUNTS:
        /\ sender /= Escrow /\ receiver /= Escrow
        /\ amount > 0
        \* the source direction: escrow source tokens
        /\ LocalTransfer(chan[1], sender, Escrow, denom, amount)
        /\ LET data == [seqno    |-> seqno,
                        sender   |-> sender,
                        receiver |-> receiver,
                        denom    |-> denom,
                        amount   |-> amount]
               packet == [src |-> chan[1], dest |-> chan[2], data |-> data]
           IN
           /\ sentPackets' = sentPackets \union { packet }
           /\ seqno' = seqno + 1
           /\ UNCHANGED deliveredNums
        \* TODO: add the case ~isSource, that is, the other direction   

\* Produce `amount` coins in the receiver's account (out of thin air!)

MintCoins(chain, receiver, denom, amount) ==
    \* do not mint native coins
    /\ denom /= Native(chain)
    /\ banks' = [banks EXCEPT ![chain, receiver, denom] =
                    banks[chain, receiver, denom] + amount]
    
\* Receive a packet on a non-source chain (note that ICS20 does more than that)
ReceivePacketFromSource ==
    \E packet \in sentPackets:
        /\ packet.seqno \notin deliveredNums
        \* In the implementation, we produce a new denomination.
        \* Mint coins that are different from native.
        /\ LET foreignDenom == MK_DENOM[packet.dest, packet.data.denom] IN
             MintCoins(packet.dest,
                     packet.data.receiver, foreignDenom, packet.data.amount)
        /\ deliveredNums' = deliveredNums \union { packet.seqno }
        /\ UNCHANGED <<sentPackets, seqno>>

\* Update the world        
Next ==
    \/ LocalStep
    \/ SendPacketFromSource
    \/ ReceivePacketFromSource

(************************** PROPERTIES ***************************************)

\* every bank always has reserves
ReservesInv ==
    \A chain \in CHAINS:
        banks[chain, "reserve", Native(chain)] > 0

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
        banks[p.src, Escrow, p.data.denom] >= p.data.amount

\* This property should produce a counterexample that demonstrates
\* that a foreign denomination can reach a blockchain
NoForeignCoins ==
    \A chain \in CHAINS, acc \in ACCOUNTS, d \in DENOMS:
            d /= Native(chain) => banks[chain, acc, d] = 0


(***************** INDUCTIVE INVARIANT ***************************************)
(*

TODO: update the inductive invariant by following the pattern

TypeOK ==
    banks \in [ CHAINS \X ACCOUNTS -> AMOUNTS ]

IndInv ==
    /\ TypeOK
    /\ \A c \in CHAINS:
        ChainSupply(c) = GENESIS_SUPPLY[c]
 *)        

===============================================================================
