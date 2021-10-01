----------------------- MODULE TokenTransfer3 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
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
    \* A set of accounts, i.e., their names
    \* @type: Set(ADDR);
    ACCOUNTS,
    \* Initial coin supply for every chain
    \* @type: CHAIN -> Int;
    GENESIS_SUPPLY

VARIABLES
    \* For every chain and account, store the amount of tokens in the account
    \* @type: ADDR -> Int;
    banks

(*************************** OPERATORS ***************************************)
\* @type: (ADDR -> Int, Set(ADDR)) => Int;
SumAddresses(amounts, Addrs) ==
    LET Add(sum, addr) == sum + amounts[addr] IN
    FoldSet(Add, 0, Addrs)

\* @type: (ADDR -> Int, CHAIN) => Int;
ChainSupply(amounts, chain) ==
    SumAddresses(amounts, {chain} \X ACCOUNTS)

(*
\* If you know TLA+, this is the de-facto way of writing SumAddresses:
RECURSIVE SumAddresses(_, _)
SumAddresses(amounts, Addrs) ==
    IF Addrs = {}
    THEN 0
    ELSE LET addr == CHOOSE a \in Addrs: TRUE IN
         amounts[addr] + SumAddresses(amounts, Addrs \ {addr})
 *)        

(**************************** SYSTEM *****************************************)

\* Initialize the world, e.g., from the last upgrade
Init ==
    \E b \in [ CHAINS \X ACCOUNTS -> Nat ]:
        /\ \A chain \in CHAINS:
            /\ b[chain, "reserve"] > 0
            /\ ChainSupply(b, chain) = GENESIS_SUPPLY[chain]
        /\ banks = b


\* Transfer the tokens from on account to another (on the same chain)
LocalTransfer(chain, from, to, amount) ==
    /\ banks[chain, from] >= amount
    /\ from /= to
    /\ banks' = [banks EXCEPT
            ![chain, from] = banks[chain, from] - amount,
            ![chain, to]   = banks[chain, to]   + amount
        ]

\* Update the world        
Next ==
    \E chain \in CHAINS, from, to \in ACCOUNTS, amount \in Nat:
        LocalTransfer(chain, from, to, amount)

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
        ChainSupply(banks, chain) = GENESIS_SUPPLY[chain]

===============================================================================
