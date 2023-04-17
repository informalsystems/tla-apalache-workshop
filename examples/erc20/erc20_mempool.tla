---------------------------- MODULE erc20_mempool ----------------------------
\* Specifying transaction execution in the mempool.
\* We represent mempool as a set. Since we are not using 'nonce',
\* duplicate transactions are simply ignored.
\* It should be easy to extend this specification with nonces.
\*
\* Igor Konnov, Informal Systems, 2023
EXTENDS Integers, erc20_mempool_typedefs

AllAddresses == {
  "0_OF_ADDR", "alice_OF_ADDR", "bob_OF_ADDR", "eve_OF_ADDR"
}

MAX_UINT == 2^256 - 1
\* Use a tiny value of MAX_UINT, if you'd like to run it in TLC:
\* MAX_UINT == 2^2 - 1
AMOUNTS == 0..MAX_UINT

INSTANCE erc20

VARIABLES
  \* @type: $state;
  contractState,
  \* @type: Set($tx);
  mempool,
  \* @type: $tx;
  lastTx,
  \* @type: Str;
  lastTxStatus

Init ==
  /\ \E sender \in AllAddresses \ { ZERO_ADDRESS }:
       \E initialSupply \in AMOUNTS:
         contractState = newErc20(sender, initialSupply)
  /\ mempool = {}
  /\ lastTx = NoneTx
  /\ lastTxStatus = ""

\* Submit a transaction to the memory pool.
\* This transaction is simply added to the pool, but not executed.
submit(tx) ==
  /\ mempool' = mempool \union { tx }
  /\ lastTx' = tx
  /\ lastTxStatus' = "pending"
  /\ UNCHANGED contractState

\* an auxilliary action that assigns variables from a method execution result
\* @type: ($tx, $result) => Bool;
fromResult(tx, result) ==
  /\ lastTx' = tx
  /\ IF VariantTag(result) /= "Error"
     THEN /\ lastTxStatus' = "success"
          /\ contractState' = VariantGetUnsafe("Ok", result).state
     ELSE /\ lastTxStatus' = VariantGetUnsafe("Error", result)
          /\ UNCHANGED contractState
  
\* @type: $tx => Bool;
commit(tx) ==
  /\ mempool' = mempool \ { tx }
  /\ \/ /\ VariantTag(tx) = "TransferTx"
        /\ LET ttx == VariantGetUnsafe("TransferTx", tx) IN
           LET res ==
             transfer(contractState, ttx.sender, ttx.toAddr, ttx.amount) IN
           fromResult(tx, res)
     \/ /\ VariantTag(tx) = "ApproveTx"
        /\ LET atx == VariantGetUnsafe("ApproveTx", tx) IN
           LET res ==
             approve(contractState, atx.sender, atx.spender, atx.amount) IN
           fromResult(tx, res)
     \/ /\ VariantTag(tx) = "TransferFromTx"
        /\ LET ftx == VariantGetUnsafe("TransferFromTx", tx) IN
           LET res ==
             transferFrom(contractState, ftx.sender,
                          ftx.fromAddr, ftx.toAddr, ftx.amount) IN
           fromResult(tx, res)

Next ==
  \* execute the contract methods
  \E sender \in AllAddresses:
    \E amount \in AMOUNTS:
      \/ \E toAddr \in AllAddresses:
           submit(TransferTx(sender, toAddr, amount))  
      \/ \E spender \in AllAddresses:
           submit(ApproveTx(sender, spender, amount))
      \/ \E fromAddr, toAddr \in AllAddresses:
           submit(TransferFromTx(sender, fromAddr, toAddr, amount))  
      \/ \E tx \in mempool:
           commit(tx)

(**
 * No transferFrom should be possible, while there is a pending approval
 * for a smaller amount. This invariant is violated, as explained in:
 *
 * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
 *)
noTransferFromWhileApproveInFlight ==
  LET BadExample ==
    /\ lastTxStatus = "success"
    /\ VariantTag(lastTx) = "TransferFromTx"
    /\ LET ltx == VariantGetUnsafe("TransferFromTx", lastTx) IN
       /\ ltx.amount > 0
       /\ \E tx \in mempool:
            /\ VariantTag(tx) = "ApproveTx"
            /\ LET atx == VariantGetUnsafe("ApproveTx", tx) IN
               /\ atx.sender = ltx.fromAddr
               /\ atx.spender = ltx.sender
               /\ atx.amount < ltx.amount
               /\ atx.amount > 0
  IN
  ~BadExample

==============================================================================