---------------------------- MODULE counterexample ----------------------------

EXTENDS MC_ERC20

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 0
    /\ pendingTransactions = {}

(* Transition 2 to State1 *)
State1 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 1
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 0,
        sender |-> "Bob_OF_ADDR",
        spender |-> "Alice_OF_ADDR",
        tag |-> "approve",
        value |-> -1]}

(* Transition 3 to State2 *)
State2 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx
      = [fail |-> TRUE,
        id |-> 0,
        sender |-> "Bob_OF_ADDR",
        spender |-> "Alice_OF_ADDR",
        tag |-> "approve",
        value |-> -1]
    /\ nextTxId = 1
    /\ pendingTransactions = {}

(* Transition 2 to State3 *)
State3 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 2
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 1,
        sender |-> "Alice_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 3]}

(* Transition 4 to State4 *)
State4 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx
      = [fail |-> FALSE,
        id |-> 1,
        sender |-> "Alice_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 3]
    /\ nextTxId = 2
    /\ pendingTransactions = {}

(* Transition 2 to State5 *)
State5 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 3
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 2,
        sender |-> "Alice_OF_ADDR",
        spender |-> "Eve_OF_ADDR",
        tag |-> "approve",
        value |-> 2]}

(* Transition 4 to State6 *)
State6 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 2>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx
      = [fail |-> FALSE,
        id |-> 2,
        sender |-> "Alice_OF_ADDR",
        spender |-> "Eve_OF_ADDR",
        tag |-> "approve",
        value |-> 2]
    /\ nextTxId = 3
    /\ pendingTransactions = {}

(* Transition 0 to State7 *)
State7 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 2>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 4
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 3,
        sender |-> "Alice_OF_ADDR",
        tag |-> "transfer",
        toAddr |-> "Alice_OF_ADDR",
        value |-> 0]}

(* Transition 2 to State8 *)
State8 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 2>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 5
    /\ pendingTransactions
      = { [fail |-> FALSE,
          id |-> 3,
          sender |-> "Alice_OF_ADDR",
          tag |-> "transfer",
          toAddr |-> "Alice_OF_ADDR",
          value |-> 0],
        [fail |-> FALSE,
          id |-> 4,
          sender |-> "Alice_OF_ADDR",
          spender |-> "Eve_OF_ADDR",
          tag |-> "approve",
          value |-> 1] }

(* Transition 1 to State9 *)
State9 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 2>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 6
    /\ pendingTransactions
      = { [fail |-> FALSE,
          fromAddr |-> "Alice_OF_ADDR",
          id |-> 5,
          sender |-> "Eve_OF_ADDR",
          tag |-> "transferFrom",
          toAddr |-> "Bob_OF_ADDR",
          value |-> 2],
        [fail |-> FALSE,
          id |-> 3,
          sender |-> "Alice_OF_ADDR",
          tag |-> "transfer",
          toAddr |-> "Alice_OF_ADDR",
          value |-> 0],
        [fail |-> FALSE,
          id |-> 4,
          sender |-> "Alice_OF_ADDR",
          spender |-> "Eve_OF_ADDR",
          tag |-> "approve",
          value |-> 1] }

(* Transition 6 to State10 *)
State10 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 0>>,
        <<"Bob_OF_ADDR", 2>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx
      = [fail |-> FALSE,
        fromAddr |-> "Alice_OF_ADDR",
        id |-> 5,
        sender |-> "Eve_OF_ADDR",
        tag |-> "transferFrom",
        toAddr |-> "Bob_OF_ADDR",
        value |-> 2]
    /\ nextTxId = 6
    /\ pendingTransactions
      = { [fail |-> FALSE,
          id |-> 3,
          sender |-> "Alice_OF_ADDR",
          tag |-> "transfer",
          toAddr |-> "Alice_OF_ADDR",
          value |-> 0],
        [fail |-> FALSE,
          id |-> 4,
          sender |-> "Alice_OF_ADDR",
          spender |-> "Eve_OF_ADDR",
          tag |-> "approve",
          value |-> 1] }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  LET BadExample_si_2_si__skolem ==
    lastTx["tag"] = "transferFrom"
      /\ lastTx["value"] > 0
      /\ ~(lastTx["fail"])
      /\ Skolem((\E approval$2 \in pendingTransactions:
        approval$2["tag"] = "approve"
          /\ approval$2["sender"] = lastTx["fromAddr"]
          /\ approval$2["spender"] = lastTx["sender"]
          /\ ~(lastTx["sender"] = lastTx["toAddr"])
          /\ approval$2["value"] < lastTx["value"]
          /\ approval$2["value"] > 0))
  IN
  BadExample_si_2_si__skolem

================================================================================
(* Created by Apalache on Wed May 25 20:15:13 CEST 2022 *)
(* https://github.com/informalsystems/apalache *)
