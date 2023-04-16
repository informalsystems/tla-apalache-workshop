---------------------- MODULE erc20_mempool_typedefs --------------------------
EXTENDS Variants

(*
  Type definitions for the erc20 mempool.

  // The result of applying an ERC20 method
  @typeAlias: tx =
      NoneTx(NONE)
    | TransferTx({ sender: ADDR, toAddr: ADDR, amount: Int })
    | ApproveTx({ sender: ADDR, spender: ADDR, amount: Int })
    | TransferFromTx({ sender: ADDR, fromAddr: ADDR, toAddr: ADDR, amount: Int })
  ;
 *)

erc20_mempool_typedefs == TRUE

\* @type: $tx;
NoneTx == Variant("NoneTx", "none_OF_NONE")

\* @type: (ADDR, ADDR, Int) => $tx;
TransferTx(sender, toAddr, amount) ==
  Variant("TransferTx",
          [ sender |-> sender, toAddr |-> toAddr, amount |-> amount ])

\* @type: (ADDR, ADDR, Int) => $tx;
ApproveTx(sender, spender, amount) ==
  Variant("ApproveTx",
          [ sender |-> sender, spender |-> spender, amount |-> amount ])

\* @type: (ADDR, ADDR, ADDR, Int) => $tx;
TransferFromTx(sender, fromAddr, toAddr, amount) ==
  Variant("TransferFromTx",
          [ sender |-> sender,
            fromAddr |-> fromAddr, toAddr |-> toAddr, amount |-> amount ])

================================================================================