---------------------------- MODULE erc20_tests --------------------------------
(*
 * A state machine for model checking the contract
 *
 * Igor Konnov, Informal Systems, 2023
 *)

EXTENDS Integers

\* we fix the set of addresses to a small set
AllAddresses == {
  "0_OF_ADDR", "alice_OF_ADDR", "bob_OF_ADDR", "eve_OF_ADDR"
}

MAX_UINT == 2^256 - 1
AMOUNTS == 0..MAX_UINT

INSTANCE erc20

VARIABLE
  \* @type: $state;
  state

Init ==
  \E sender \in AllAddresses \ { ZERO_ADDRESS }:
    \E initialSupply \in AMOUNTS:
      state = newErc20(sender, initialSupply)

\* @type: $result => Bool;
fromResult(result) ==
  /\ VariantTag(result) = "Ok"
  /\ state' = VariantGetUnsafe("Ok", result).state

\* a single-method Next predicate
Next1 ==
  \E sender, toAddr \in AllAddresses:
    \E amount \in AMOUNTS:
      fromResult(transfer(state, sender, toAddr, amount))  

\* all three methods can be called in any order
Next ==
  \* execute the contract methods
  \E sender \in AllAddresses:
    \E amount \in AMOUNTS:
      \* transfer
      \/ \E toAddr \in AllAddresses:
           fromResult(transfer(state, sender, toAddr, amount))  
      \* approve
      \/ \E spender \in AllAddresses:
           fromResult(approve(state, sender, spender, amount))
      \* transferFrom
      \/ \E fromAddr, toAddr \in AllAddresses:
           fromResult(transferFrom(state, sender, fromAddr, toAddr, amount))  

(****************************************************************
 * INVARIANTS
 ****************************************************************)
totalSupplyInv == isTotalSupplyCorrect(state)

zeroAddressInv == isZeroAddressEmpty(state)

noOverflowInv == isNoOverflows(state)

isValid ==
  /\ totalSupplyInv
  /\ zeroAddressInv
  /\ noOverflowInv

\* Use this predicate to initialize the state space,
\* when proving inductiveness of isValid:
\*
\* apalache-mc check --init=initArbitrary --inv=isValid --length=1 erc20_tests.tla
initArbitrary ==
  \* Note: we are mapping to balances and allowance to Int, not to AMOUNTS.
  \* Otherwise, Apalache attempts to unroll the set AMOUNTS, which is huge.
  \E owner \in AllAddresses \ { ZERO_ADDRESS }:
    \E balances \in [ AllAddresses -> Int ]:
      \E allowances \in [ AllAddresses \X AllAddresses -> Int ]:
        /\ state = [
             balanceOf |-> balances,
             totalSupply |-> sumOverBalances(balances),
             allowance |-> allowances,
             owner |-> owner
           ]
        /\ isValid

\* Check this action invariant to ensure that 'transfer' is working
\* as expected under the assumption that it has not returned an error,
\* and it has not returned FALSE.
\*
\* We could also check that case when `transfer` returns an error or FALSE,
\* but this would require to define ghost variables.
\*
\* apalache-mc check --init=initArbitrary --next=Next1 \
\*  --inv=transferPrePost --length=2 erc20_tests.tla
transferPrePost ==
  \E sender, toAddr \in AllAddresses:
    LET ob == state.balanceOf IN
    LET nb == state'.balanceOf IN
      /\ \/ sender = toAddr /\ nb = ob
         \/ /\ sender /= toAddr
            /\ nb[sender] <= ob[sender]
            /\ nb[toAddr] >= ob[toAddr]
            /\ nb[toAddr] - ob[toAddr] = ob[sender] - nb[sender]
            /\ \A a \in AllAddresses:
                a \notin { sender, toAddr } => nb[a] = ob[a]
      /\ state'.allowance = state.allowance
      /\ state'.owner = state.owner
      /\ state'.totalSupply = state.totalSupply


================================================================================
