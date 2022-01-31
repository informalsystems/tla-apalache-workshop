# Specification 00_OutParser

```Extends Integers, Sequences, FiniteSets, TLC, Apalache```


This is an example of a very simplistic token transfer for presentation
purposes. Do not use it in production, as it may lead to loss of tokens.
 
 - Version 3: fixing the invariants and introducing more
 - Version 2: let the banks do the local banking
 - Version 1: introducing data structures
 
 **author:** Igor Konnov, 2021
     

## Protocol constants

     

A real blockchain creates user accounts dynamically. However, to reason
about the token transfer protocol, it is sufficient to fix a predefined
set of accounts.  We can imagine that all accounts
exist from the beginning of times and carry zero balance.  In a real
blockchains, accounts are associated with private keys.  These are
usually either unreadable sequences of letters and digits or sequences of
24 words. In our specification, they do not have to be that verbose. We
can give normal readable names to the accounts such as Anna and Boris.

The constant `ACCOUNTS` stores the set of account names.

```@type:  Set(ADDR);```

```
Given constant ACCOUNTS
```


Every blockchain has some initial supply of coins, e.g.,
set in the genesis block. The constant `GENESIS_SUPPLY` stores this supply.

```@type:  CHAIN -> Int;```

```
Given constant GENESIS_SUPPLY
```


The protocol works for a system of blockchains. Their unique names
are relevant for our specification. We consider fixed a set of names.

```@type:  Set(CHAIN);```

```
Given constant CHAINS
```


## Variables of the state machine

     

For every chain and account, `banks` stores the amount of tokens in the account.

```@type:  ADDR -> Int;```

```
Introduce state variable banks
```


## Type aliases

  We introduce the following aliases for the types that are used in this
  specification.

```@typeAlias:  CHAIN = Str;```

```@typeAlias:  ACCOUNT = Str;```

```@typeAlias:  ADDR = <<CHAIN, ACCOUNT>>;```

```@typeAlias:  BANK = (ADDR -> Int);```

```@typeAlias:  DENOM = Str;```

```@typeAlias:  DADDR = <<CHAIN, ACCOUNT, DENOM>>;```

```
Define typedefs_included as TRUE
```


-----------------------------------------------------------------------------
## Auxiliary definitions

Before diving into the transitions of the protocol, we introduce auxiliary
definitions.

 

  `SumAddresses` computes the amount of coins held by a collection of addresses.

```@type:  (ADDR -> Int, Set(ADDR)) => Int;```

```
Define SumAddresses(amounts, Addrs) as
  Let Add(sum, addr) be sum + amounts[addr] in FoldSet(Add, 0, Addrs)
```


`ChainSupply` computes the supply of every chain in the current state.

```@type:  (ADDR -> Int, CHAIN) => Int;```

```
Define ChainSupply(amounts, chain) as
  SumAddresses(amounts, {Cross product of {Set of chain}, ACCOUNTS})
```


-----------------------------------------------------------------------------
 ## Protocol transitions

 

  `LocalTransfer` specifies how `amount` coins could be transferred from an
  account `from` to an account `to` on the same chain `chain`.  Note that the
  actual implementation of `LocalTransfer` is much more complex than that. But
  those details are not important for our specification.

```
Define LocalTransfer(chain, from, to, amount) as
  banks[chain, from] >= amount
    and from /= to
    and banks'
      = [Copy function
        banks except
          at (chain, from) set banks[chain, from] - amount,
          at (chain, to) set banks[chain, to] + amount]
```


-----------------------------------------------------------------------------
 ## Protocol properties

 

  The invariant `ReservesInv` states that every chain should have coins
  on the account `reserve`.

```
Define ReservesInv as For each chain in CHAINS holds banks[chain, "reserve"] > 0
```


The invariant `NoNegativeAccounts` states that every account never goes
  below zero.

```
Define NoNegativeAccounts as
  For each address in DOMAIN banks holds banks[address] >= 0
```


-----------------------------------------------------------------------------
 ## Protocol initialization

 

  Initialize the global state of our system. We can imagine that this is the
  state right after the genesis initialization or after an upgrade.

  Since the protocol parameters can be set to arbitrary values, the initial
  state can also be a snapshot of the blockchains that was made at some point.

```
Define Init as
  Exists b in Set of functions
    from {Cross product of CHAINS, ACCOUNTS}
    to Nat such that
    (For each chain in CHAINS holds
        b[chain, "reserve"] > 0
          and ChainSupply(b, chain) = GENESIS_SUPPLY[chain])
      and banks = b
    holds
```


The predicate `Next` captures all possible transitions that could be
  made by the system. In this version, we can only do local transfers.

```
Define Next as
  Exists chain in CHAINS such that
    Exists from in ACCOUNTS such that
      Exists to in ACCOUNTS such that
        Exists amount in Nat such that
          LocalTransfer(chain, from, to, amount)
          holds
        holds
      holds
    holds
```


The invariant `ChainSupplyUnchanged` is probably the most crucial one.
  It states that no coins are lost or created out of thin air.

```
Define ChainSupplyUnchanged as
  For each chain in CHAINS holds
    ChainSupply(banks, chain) = GENESIS_SUPPLY[chain]
```

--------------------------------------------------------------------------------
