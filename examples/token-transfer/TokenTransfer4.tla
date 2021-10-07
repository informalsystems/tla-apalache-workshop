----------------------- MODULE TokenTransfer4 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
 * Version 4: bounding the amounts to help TLC
 * Version 3: fixing the invariants and introducing more
 * Version 2: let the banks do the local banking
 * Version 1: introducing data structures
 *
 * Igor Konnov, 2021
 *)
EXTENDS Integers, Apalache

CONSTANT
    \* A set of blockchains, i.e., their names
    \* @type: Set(Str);
    CHAINS,
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
    banks

(*************************** OPERATORS ***************************************)
\* @type: (ADDR -> Int, Set(ADDR)) => Int;
SumAddresses(amounts, Addrs) ==
    LET Add(sum, addr) == sum + amounts[addr] IN
    FoldSet(Add, 0, Addrs)

ChainSupply(chain) ==
    SumAddresses({chain} \X ACCOUNTS)

(**************************** SYSTEM *****************************************)

\* Initialize the world, e.g., from the last upgrade
Init ==
    \E b \in [ CHAINS \X ACCOUNTS -> AMOUNTS ]:
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

\* Update the world        
Next ==
    \E chain \in CHAINS, from, to \in ACCOUNTS, amount \in AMOUNTS:
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
        LET supply == ChainSupply(chain) IN
        supply = GENESIS_SUPPLY[chain]


===============================================================================
