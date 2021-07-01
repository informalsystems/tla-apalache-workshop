----------------------- MODULE TokenTransfer10 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
 * Version 10: timeouts
 * Version 9: receive and send in the backward direction
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
EXTENDS Integers, Apalache, typedefs

CONSTANT
    \* A set of blockchains, i.e., their names
    \* @type: Set(CHAIN);
    CHAINS,
    \* A set of channels, that is, pairs of chains
    \* @type: Set(<<CHAIN, CHAIN>>);
    CHANNELS,
    \* A set of accounts, i.e., their names
    \* @type: Set(ACCOUNT);
    ACCOUNTS,
    \* A set of all possible amounts
    \* @type: Set(Int);
    GENESIS_SUPPLY,
    \* A set of denominations
    \* @type: Set(DENOM);
    DENOMS,
    \* A function that produces a new denomination for a chain a denomination
    \* @type: <<CHAIN, DENOM>> -> DENOM;
    MK_DENOM,
    \* A function that should work as an inverse of MK_DENOM
    \* @type: <<CHAIN, DENOM>> -> DENOM;
    UNMK_DENOM

VARIABLES
    \* For every chain and account, store the amount of tokens in the account
    \* for each denomination
    \* @type: DADDR -> Int;
    banks,
    \* Packets that are sent by one chain to another (e.g., via an IBC channel)
    \* @type: Set([seqno: Int, src: CHAIN, dest: CHAIN, data: [sender: ACCOUNT, receiver: ACCOUNT, denom: DENOM, amount: Int]]);
    sentPackets,
    \* The sequence numbers of delivered packets
    \* @type: Set(Int);
    deliveredNums,
    \* The sequence numbers of the packets that timed out
    \* @type: Set(Int);
    dstTimeoutNums,
    \* The sequence numbers of the packets that timed out, registered on source
    \* @type: Set(Int);
    srcTimeoutNums,
    \* An imaginary global counter that we use to assign unique sequence numbers
    \* @type: Int;
    seqno

(*************************** OPERATORS ***************************************)
\* For simplicity, we fix the name of the escrow account.
\* In ICS20, one introduces one escrow account per channel.
Escrow == "escrow"

\* For simplicity, we call the coin native if it has the same name as the chain
Native(chain) == chain

\* Compute the sum of tokens over addresses.
\* @type: (DADDR -> Int, Set(DADDR)) => Int;
SumAddresses(amounts, Addrs) ==
    LET Add(sum, addr) == sum + amounts[addr] IN
    FoldSet(Add, 0, Addrs)

\* Compute token supply in one chain.
\* @type: (DADDR -> Int, CHAIN) => Int;
ChainSupply(amounts, chain) ==
    SumAddresses(amounts, {chain} \X ACCOUNTS \X { Native(chain) })

\* Compute token supply across all chains.
\* @type: (CHAIN => Int) => Int;
AllChainsSupply(GetChainSupply(_)) ==
    LET Add(sum, chain) == sum + GetChainSupply(chain) IN
    FoldSet(Add, 0, CHAINS)

\* Compute chain supply in the genesis block.
AllChainsGenesisSupply ==
    LET Get(c) == GENESIS_SUPPLY[c] IN
    AllChainsSupply(Get)

\* Compute chain supply given an "amounts" function
\* @type: (DADDR -> Int) => Int;
AllChainsAmountsSupply(amounts) ==
    LET Get(c) == ChainSupply(amounts, c) IN
    AllChainsSupply(Get)

(**************************** SYSTEM *****************************************)

\* Initialize the world, e.g., from the last upgrade
Init ==
    /\ seqno = 0
    /\ sentPackets = {}
    /\ deliveredNums = {}
    /\ dstTimeoutNums = {}
    /\ srcTimeoutNums = {}
    /\ \E b \in [ CHAINS \X ACCOUNTS \X DENOMS -> Nat ]:
        /\ \A chain \in CHAINS:
            /\ b[chain, "reserve", chain] > 0
            /\ ChainSupply(b, chain) = GENESIS_SUPPLY[chain]
            /\ \A a \in ACCOUNTS, d \in DENOMS:
                \* no tokens in foreign denominations
                d /= Native(chain) => b[chain, a, d] = 0
        /\ banks = b

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
                denom \in DENOMS, amount \in Nat:
        /\ from /= Escrow
        /\ to /= Escrow
        /\ LocalTransfer(chain, from, to, denom, amount)
    /\ UNCHANGED <<seqno, sentPackets, deliveredNums,
                   dstTimeoutNums, srcTimeoutNums>>

\* send a packet over a channel
\* @type: (<<Str, Str>>, Str, Str, Str, Str, Int) => Bool;
SendPacket(chan, dir, sender, receiver, denom, amount) ==
   LET data == [seqno    |-> seqno,
                sender   |-> sender,
                receiver |-> receiver,
                denom    |-> denom,
                amount   |-> amount]
       src == IF dir = "forward" THEN chan[1] ELSE chan[2]
       dst == IF dir = "forward" THEN chan[2] ELSE chan[1]
       packet == [src |-> src, dest |-> dst, data |-> data]
   IN
   /\ sentPackets' = sentPackets \union { packet }
   /\ seqno' = seqno + 1
   /\ UNCHANGED <<deliveredNums, dstTimeoutNums, srcTimeoutNums>>

\* Send a packet to transfer tokens (from the source)
SendPacketFromSource ==
    \E chan \in CHANNELS, sender, receiver \in ACCOUNTS,
            denom \in DENOMS, amount \in Nat:
        /\ sender /= Escrow /\ receiver /= Escrow
        /\ amount > 0
        \* the source direction: escrow source tokens
        /\ LocalTransfer(chan[1], sender, Escrow, denom, amount)
        /\ SendPacket(chan, "forward", sender, receiver, denom, amount)

\* Burn `amount` coins in the sender's account
BurnCoins(chain, sender, denom, amount) ==
    \* do not burn native coins
    /\ denom /= Native(chain)
    \* do not let to burn more coins than we have
    /\ LET newAmount == banks[chain, sender, denom] - amount IN
       /\ newAmount >= 0
       /\ banks' = [banks EXCEPT ![chain, sender, denom] = newAmount]

\* Send a packet to return tokens (to the source)
SendPacketToSource ==
    \E chan \in CHANNELS, sender, receiver \in ACCOUNTS,
            denom \in DENOMS, amount \in Nat:
        /\ sender /= Escrow /\ receiver /= Escrow
        /\ amount > 0
        \* in the direction of the source: burn coins
        /\ BurnCoins(chan[2], sender, denom, amount)
        /\ SendPacket(chan, "backward", sender, receiver, denom, amount)

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
        /\ packet.seqno \notin dstTimeoutNums
        \* In the implementation, we produce a new denomination.
        \* Mint coins that are different from native.
        /\ LET foreignDenom == MK_DENOM[packet.dest, packet.data.denom] IN
             MintCoins(packet.dest,
                     packet.data.receiver, foreignDenom, packet.data.amount)
        /\ deliveredNums' = deliveredNums \union { packet.seqno }
        /\ UNCHANGED <<sentPackets, dstTimeoutNums, srcTimeoutNums, seqno>>

\* Receive a packet on the source chain
ReceivePacketOnSource ==
    \E packet \in sentPackets:
        /\ packet.seqno \notin deliveredNums
        /\ packet.seqno \notin dstTimeoutNums
        \* translate the coin denomination, e.g., by pruning the prefix
        /\  LET sourceDenom == UNMK_DENOM[packet.denom] IN
            /\ sourceDenom /= "invalid" 
            /\ LocalTransfer(packet.dst, packet.receiver, Escrow,
                             sourceDenom, packet.amount)
            /\ deliveredNums' = deliveredNums \union { packet.seqno }
            /\ UNCHANGED <<sentPackets, dstTimeoutNums, srcTimeoutNums, seqno>>

\* A non-determinstic timeout.
\* Note that the timeout should be registered first on the destination chain.
RegisterTimeout ==
    \E packet \in sentPackets:
        /\ packet.seqno \notin deliveredNums
        /\ packet.seqno \notin dstTimeoutNums
        /\ dstTimeoutNums' = dstTimeoutNums \union { packet.seqno }
        /\ UNCHANGED <<banks, sentPackets, deliveredNums, srcTimeoutNums, seqno>>

\* Observe a timeout on the destination chain and refund the coins on the source.
\* Note that this cannot be simply done by measuring time.
\* We need a confirmation on the destination chain that the timeout has occured.
ApplyTimeout ==
    \E packet \in sentPackets:
        /\ packet.seqno \in dstTimeoutNums
        /\ srcTimeoutNums' = srcTimeoutNums \union { packet.seqno }
        /\ IF Native(packet.src) = packet.denom
           THEN LocalTransfer(packet.src, packet.data.sender, Escrow,
                              packet.data.denom, packet.data.amount)
           ELSE  MintCoins(packet.dest, packet.data.receiver,
                           packet.data.denom, packet.data.amount)
        /\ UNCHANGED <<banks, sentPackets, deliveredNums, dstTimeoutNums, seqno>>
    

\* Update the world        
Next ==
    \/ LocalStep
    \/ SendPacketFromSource
    \/ ReceivePacketFromSource
    \/ SendPacketToSource
    \/ ReceivePacketOnSource
    \/ RegisterTimeout
    \/ ApplyTimeout

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
        LET supply == ChainSupply(banks, chain) IN
        supply = GENESIS_SUPPLY[chain]

\* for each in-fly packet, there is enough money in the escrow account
InFlyPacketIsSecured ==
    \A p \in sentPackets:
        (p.seqno \notin deliveredNums /\ p.seqno \notin srcTimeoutNums)
            =>
            banks[p.src, Escrow, p.data.denom] >= p.data.amount

\* the supply over all chains remains constant
AllChainsSupplyUnchanged ==
    AllChainsGenesisSupply = AllChainsAmountsSupply(banks)

(************* PROPERTIES TO PRODUCE COUNTEREXAMPLES *************************)

\* This property should produce a counterexample that demonstrates
\* that a foreign denomination can reach a blockchain
NoForeignCoins ==
    \A chain \in CHAINS, acc \in ACCOUNTS, d \in DENOMS:
            d /= Native(chain) => banks[chain, acc, d] = 0

===============================================================================
