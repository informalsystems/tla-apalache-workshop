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
        <<"Eve_OF_ADDR", 3>> })
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
        <<"Eve_OF_ADDR", 3>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 1
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 0,
        sender |-> "Eve_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 3]}

(* Transition 4 to State2 *)
State2 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 3>> })
    /\ lastTx
      = [fail |-> FALSE,
        id |-> 0,
        sender |-> "Eve_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 3]
    /\ nextTxId = 1
    /\ pendingTransactions = {}

(* Transition 2 to State3 *)
State3 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 3>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 2
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 1,
        sender |-> "Eve_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 2]}

(* Transition 1 to State4 *)
State4 ==
  allowance
      = SetAsFun({ <<<<"Bob_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Bob_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Bob_OF_ADDR">>, 3>>,
        <<<<"Alice_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Bob_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Eve_OF_ADDR">>, 0>>,
        <<<<"Alice_OF_ADDR", "Alice_OF_ADDR">>, 0>>,
        <<<<"Eve_OF_ADDR", "Alice_OF_ADDR">>, 0>> })
    /\ balanceOf
      = SetAsFun({ <<"Alice_OF_ADDR", 2>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 3>> })
    /\ lastTx = [fail |-> FALSE, id |-> 0, tag |-> "None"]
    /\ nextTxId = 3
    /\ pendingTransactions
      = { [fail |-> FALSE,
          fromAddr |-> "Eve_OF_ADDR",
          id |-> 2,
          sender |-> "Bob_OF_ADDR",
          tag |-> "transferFrom",
          toAddr |-> "Alice_OF_ADDR",
          value |-> 3],
        [fail |-> FALSE,
          id |-> 1,
          sender |-> "Eve_OF_ADDR",
          spender |-> "Bob_OF_ADDR",
          tag |-> "approve",
          value |-> 2] }

(* Transition 6 to State5 *)
State5 ==
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
      = SetAsFun({ <<"Alice_OF_ADDR", 5>>,
        <<"Bob_OF_ADDR", 0>>,
        <<"Eve_OF_ADDR", 0>> })
    /\ lastTx
      = [fail |-> FALSE,
        fromAddr |-> "Eve_OF_ADDR",
        id |-> 2,
        sender |-> "Bob_OF_ADDR",
        tag |-> "transferFrom",
        toAddr |-> "Alice_OF_ADDR",
        value |-> 3]
    /\ nextTxId = 3
    /\ pendingTransactions
      = {[fail |-> FALSE,
        id |-> 1,
        sender |-> "Eve_OF_ADDR",
        spender |-> "Bob_OF_ADDR",
        tag |-> "approve",
        value |-> 2]}

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
(* Created by Apalache on Wed May 25 21:16:03 CEST 2022 *)
(* https://github.com/informalsystems/apalache *)
