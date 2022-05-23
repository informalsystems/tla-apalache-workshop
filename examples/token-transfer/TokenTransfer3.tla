----------------------- MODULE TokenTransfer3 ---------------------------------
EXTENDS Integers, Apalache, typedefs

(*(* Below, we attach the comments to definitions. Otherwise, our tool
     would not be able to extract them to a markdown document. *)*)

CONSTANT
    (*
This is an example of a very simplistic token transfer for presentation
purposes. Do not use it in production, as it may lead to loss of tokens.
 
 - Version 3: fixing the invariants and introducing more
 - Version 2: let the banks do the local banking
 - Version 1: introducing data structures
 
 **author:** Igor Konnov, 2021
     *)

     (*
## Protocol constants

     *)

    (*
A real blockchain creates user accounts dynamically. However, to reason
about the token transfer protocol, it is sufficient to fix a predefined
set of accounts.  We can imagine that all accounts
exist from the beginning of times and carry zero balance.  In a real
blockchains, accounts are associated with private keys.  These are
usually either unreadable sequences of letters and digits or sequences of
24 words. In our specification, they do not have to be that verbose. We
can give normal readable names to the accounts such as Anna and Boris.

The constant `ACCOUNTS` stores the set of account names.

@type: Set(ADDR);
     *)
    ACCOUNTS,

    (*
The protocol works for a system of blockchains. Their unique names
are relevant for our specification. We consider fixed a set of names.

@type: Set(CHAIN);
    *)
    CHAINS,
    (* 
Every blockchain has some initial supply of coins, e.g.,
set in the genesis block. The constant `GENESIS_SUPPLY` stores this supply.
   
@type: CHAIN -> Int;
    *)  
    GENESIS_SUPPLY

VARIABLES
    (*

## Variables of the state machine

     *)

    (*
For every chain and account, `banks` stores the amount of tokens in the account.

      @type: ADDR -> Int;
    *)  
    banks

(*
 -----------------------------------------------------------------------------
## Auxiliary definitions

Before diving into the transitions of the protocol, we introduce auxiliary
definitions.

 *)

(*
  `SumAddresses` computes the amount of coins held by a collection of addresses.

  @type: (ADDR -> Int, Set(ADDR)) => Int;
 *)
SumAddresses(amounts, Addrs) ==
    LET Add(sum, addr) == sum + amounts[addr] IN
    ApaFoldSet(Add, 0, Addrs)

(*
  `ChainSupply` computes the supply of every chain in the current state.
  
  @type: (ADDR -> Int, CHAIN) => Int;
 *) 
ChainSupply(amounts, chain) ==
    SumAddresses(amounts, {chain} \X ACCOUNTS)

(*
 -----------------------------------------------------------------------------
 ## Protocol initialization

 *)

(*
  Initialize the global state of our system. We can imagine that this is the
  state right after the genesis initialization or after an upgrade.

  Since the protocol parameters can be set to arbitrary values, the initial
  state can also be a snapshot of the blockchains that was made at some point.
 *) 
Init ==
    \E b \in [ CHAINS \X ACCOUNTS -> Nat ]:
        /\ \A chain \in CHAINS:
            /\ b[chain, "reserve"] > 0
            /\ ChainSupply(b, chain) = GENESIS_SUPPLY[chain]
        /\ banks = b

(*
 -----------------------------------------------------------------------------
 ## Protocol transitions

 *)

(*
  `LocalTransfer` specifies how `amount` coins could be transferred from an
  account `from` to an account `to` on the same chain `chain`.  Note that the
  actual implementation of `LocalTransfer` is much more complex than that. But
  those details are not important for our specification.
 *) 
LocalTransfer(chain, from, to, amount) ==
    /\ banks[chain, from] >= amount
    /\ from /= to
    /\ banks' = [banks EXCEPT
            ![chain, from] = banks[chain, from] - amount,
            ![chain, to]   = banks[chain, to]   + amount
        ]

(*
  The predicate `Next` captures all possible transitions that could be
  made by the system. In this version, we can only do local transfers.
 *)
Next ==
    \E chain \in CHAINS, from, to \in ACCOUNTS, amount \in Nat:
        LocalTransfer(chain, from, to, amount)

(*
 -----------------------------------------------------------------------------
 ## Protocol properties

 *)

(*
  The invariant `ReservesInv` states that every chain should have coins
  on the account `reserve`.
 *) 
ReservesInv ==
    \A chain \in CHAINS:
        banks[chain, "reserve"] > 0

(*
  The invariant `NoNegativeAccounts` states that every account never goes
  below zero.
 *)
NoNegativeAccounts ==
    \A address \in DOMAIN banks:
        banks[address] >= 0

(*
  The invariant `ChainSupplyUnchanged` is probably the most crucial one.
  It states that no coins are lost or created out of thin air.
 *)
ChainSupplyUnchanged ==
    \A chain \in CHAINS:
        ChainSupply(banks, chain) = GENESIS_SUPPLY[chain]

===============================================================================
