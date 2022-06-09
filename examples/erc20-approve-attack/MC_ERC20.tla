----------------------------- MODULE MC_ERC20 ---------------------------------
\* an instance for model checking ERC20.tla with Apalache
EXTENDS Integers, ERC20_typedefs

\* Use the set of three addresses.
\* We are using uninterpreted values, similar to TLC's model values.
\* See: https://apalache.informal.systems/docs/HOWTOs/uninterpretedTypes.html
ADDR10 == {
    "Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR", "Charlie_OF_ADDR",
    "Denis_OF_ADDR",  "Fritz_OF_ADDR", "Gabi_OF_ADDR", "Igor_OF_ADDR",
    "Josef_OF_ADDR", "Kate_OF_ADDR"
}
ADDR5 == {
    "Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR",
    "Charlie_OF_ADDR", "Denis_OF_ADDR"
}
ADDR3 == { "Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR" }

ADDR == ADDR3

\* Apalache can draw constants from the set of all integers
AMOUNTS == Int

VARIABLES
    \* @type: ADDR -> Int;
    balanceOf,
    \* @type: <<ADDR, ADDR>> -> Int;
    allowance,
    \* @type: Set(TX);
    pendingTransactions,
    \* Last executed transaction.
    \* @type: TX;
    lastTx,
    \* @type: Int;
    nextTxId

\* instantiate the spec with ADDR, balances, allowances, and pendingTxs
INSTANCE ERC20

===============================================================================
