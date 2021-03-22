----------------------- MODULE TokenTransfer1 ---------------------------------
(*
 * This is an example of a very simplistic token transfer
 * for presentation purposes.
 * Do not use it in production, as it may lead to loss of tokens.
 *
 * Version 1: introducing data structures
 *
 * Igor Konnov, 2021
 *)
EXTENDS Integers

CONSTANT
    \* A set of blockchains, i.e., their names
    \* @type: Set(Str);
    CHAINS,
    \* A set of accounts, i.e., their names
    \* @type: Set(Str);
    ACCOUNTS

VARIABLES
    \* For every chain and account, store the amount of tokens in the account
    \* @type: <<Str, Str>> -> Int;
    banks

\* Initialize the world, e.g., from the last upgrade
Init ==
    \E b \in [ CHAINS \X ACCOUNTS -> Int ]:
        banks = b

\* Update the world
Next ==
    UNCHANGED banks

===============================================================================
