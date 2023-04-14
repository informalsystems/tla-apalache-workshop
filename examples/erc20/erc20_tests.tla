---------------------------- MODULE erc20_tests --------------------------------
\* A set of tests to check the contract

\* we fix the set of addresses to a small set
AllAddresses == {
  "0_OF_ADDR", "alice_OF_ADDR", "bob_OF_ADDR", "eve_OF_ADDR"
}

INSTANCE erc20 WITH AllAddresses <- AllAddresses

VARIABLE
  \* @type: $state;
  state

AMOUNTS == 0..MAX_UINT

Init ==
  \E sender \in AllAddresses \ { ZERO_ADDRESS }:
    \E initialSupply \in AMOUNTS:
      state = newErc20(sender, initialSupply)

\* @type: $result => Bool;
fromResult(result) ==
  /\ VariantTag(result) = "Ok"
  /\ VariantGetUnsafe("Ok", result).returnedTrue
  /\ state' = VariantGetUnsafe("Ok", result).state

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
\*apalache-mc check --init=initArbitrary --inv=isValid --length=1 erc20_tests.tla
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

================================================================================
