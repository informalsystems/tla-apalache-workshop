# Typing the specification and checking it

## Version 1: Introducing data structures

1. Open [TokenTransfer1.tla](../examples/TokenTransfer1.tla) and [MC1.tla](../examples/MC1.tla).
1. Notice how `CHAINS`, `ACCOUNTS`, and `banks` are declared.
1. Run:

    ```sh
    $ apalache-mc check MC1.tla
    ```

4. The tool reports no errors.

## Version 2: Let the banks do local banking

1. Open [TokenTransfer2.tla](../examples/TokenTransfer2.tla) and [MC2.tla](../examples/MC2.tla).
1. Inspect the operators `LocalTransfer` and `Next`. Do you see any issues?
1. Inspect the expected invariants `ReservesInv` and `NoNegativeAccounts`.
Do you see any issues?
1. Check the property `ReservesInv` by running:

    ```sh
    $ apalache-mc check --inv=ReservesInv MC2.tla
    ```

1. The tool reports on a counterexample. Check `counterexample.tla`.
Can you fix the issue?

1. Check the property `NoNegativeAccounts` by running:

    ```sh
    $ apalache-mc check --inv=NoNegativeAccounts MC2.tla
    ```

1. The tool reports on a counterexample. Check `counterexample.tla`.
Can you fix the issue?


## Version 3: Fixing the invariants and introducing more properties

1. Open [TokenTransfer3.tla](../examples/TokenTransfer3.tla) and [MC3.tla](../examples/MC3.tla).
1. See how we have fixed `NoNegativeAccounts` by using `Nat` instead of `Int`.
1. Notice how we introduced the constant `GENESIS_SUPPLY` and
the operators `SumAddresses` and `ChainSupply`.
1. Check what has changed in `Init` and `Next`.
1. Inspect the new invariant `ChainSupplyUnchanged`.
1. Observe how we have introduced `GENESIS_SUPPLY` in
[MC3.tla](../examples/MC3.tla).

1. Check the property `ChainSupplyUnchanged` by running:

    ```sh
    $ apalache-mc check --inv=ChainSupplyUnchanged MC3.tla
    ```

1. Apalache is stuck after some time. Any ideas why?    

1. Check the detailed log by typing:

    ```sh
    $ tail -f detailed.log
    ```

1. You can see the results of preprocessing steps in the directory
that is called like `x/hh.mm-DD.MM.YYYY-.*`. The file `out-analysis.tla`
is the final result of all preprocessing steps.

1. You can tell Apalache to produce the log of SMT constraints:

    ```sh
    $ apalache-mc check --inv=ChainSupplyUnchanged --debug MC3.tla
    ```

1. The log file can be found in `log0.smt`. If you are feeling adventurous
today, you can install [Microsoft Z3](https://github.com/Z3Prover/z3) and run
the log directly with `z3`:

    ```sh
    $ z3 -smt2 log0.smt
    ```

## Version 4: skipped

## Version 5: Make Apalache fast again

1. Open [TokenTransfer5.tla](../examples/TokenTransfer5.tla) and
[MC5.tla](../examples/MC5.tla).
1. Notice that we have added two new operators: `TypeOK` and `IndInv`.
1. Run Apalache as follows:

    ```sh
    $ apalache-mc check --init=IndInv --inv=IndInv --length=1 MC5.tla
    $ apalache-mc check --init=Init --inv=IndInv --length=0 MC5.tla
    $ apalache-mc check --init=IndInv --inv=ChainSupplyUnchanged --length=0 MC5.tla
    ```

1. Why do you think we have checked `ChainSupplyUnchanged` for the executions
of arbitrary length?

## Version 6: Send packets!

1. Open [TokenTransfer6.tla](../examples/TokenTransfer6.tla) and
[MC6.tla](../examples/MC6.tla).
1. Notice the changes:
  - new constant `CHANNELS`
  - new variable `sentPackets`
  - new definition `Escrow == "escrow"`
  - update in `Init` and `Next`
  - new operators `LocalStep` and `SendPacketFromSource`

1. Check the invariant `InFlyPacketIsSecured` by running:

    ```sh
    $ apalache-mc check --inv=InFlyPacketIsSecured MC6.tla
    ```

1. Do you think it is a good invariant? Can we improve it?

1. Can you write a version of `InFlyPacketIsSecured` that counts
the sum of token over all in-fly packets?

## Version 7: Receive packets

1. Open [TokenTransfer7.tla](../examples/TokenTransfer7.tla) and
[MC7.tla](../examples/MC7.tla).
1. Notice the changes:
    - new field `seqno` in sentPackets
    - new variable `seqno`
    - new variable `deliveredNums`
    - new operators `MintCoins` and `ReceivePacketFromSource`
    - updates in `Init` and `Next`

1. Do you think our spec is still OK?    
1. Check the property `ChainSupplyUnchanged` by running:

    ```sh
    $ apalache-mc check --inv=ChainSupplyUnchanged MC7.tla
    ```

1. If it takes too long, let's cheat a bit and check how to tune the model
checker. Read the page on [tuning
parameters](https://apalache.informal.systems/docs/apalache/tuning.html).

1. Create the file `apalache.properties` and write the follows:
    
    ```sh
    search.invariantFilter=[2-4]
    search.invariant.mode=after
    ```

The first option instructs Apalache to check the invariant only after 2, 3, or
4 steps. The second option instructs Apalache to check the invariant after
choosing a transition in a step, not before.

1. Run Apalache with the tuning options:

    ```sh
    $ apalache-mc check --inv=ChainSupplyUnchanged --tuning=apalache.properties MC7.tla
    ```

1. Apalache should find an error very quickly. Check `counterexample1.tla`.
Do you understand what happened?

## Version 8: Introducing denominations

1. Open [TokenTransfer8.tla](../examples/TokenTransfer8.tla) and
[MC8.tla](../examples/MC8.tla).
1. Notice the changes:
    - new constants `DENOMS` and `MK_DENOM`
    - new operator `Native`
    - updates in many operators to attach denomination to an account

1. Check the property `NoForeignCoins` by running:

    ```sh
    $ apalache-mc check --inv=NoForeignCoins MC8.tla
    ```

1. Check `counterexample.tla` for an example.    

1. We can run Apalache again to check `ChainSupplyUnchanged`:

    ```sh
    $ apalache-mc check --inv=ChainSupplyUnchanged MC8.tla
    ```

1. This time, Apalache does not come back that fast. If you want to prove
this property for all executions, construct an inductive invariant,
similar to what we did with `MC5.tla`.

## Version 9: Sending coins back

1. Open [TokenTransfer9.tla](../examples/TokenTransfer9.tla) and
[MC9.tla](../examples/MC9.tla).
1. Notice the changes:
  - new constant `UNMK_DENOM`
  - new operators: `SendPacket`, `BurnCoins`, `SendPacketToSource`,
    `ReceivePacketOnSource`
1. Check the property `InFlyPacketIsSecured` by running:

    ```sh
    $ apalache-mc check --inv=InFlyPacketIsSecured MC9.tla
    ```

1. Check `counterexample.tla` for an example.

1. Uncomment the precondition in the definition of `InFlyPacketIsSecured`
and check the property again.

## Version 10: Adding timeouts

1. Open [TokenTransfer10.tla](../examples/TokenTransfer10.tla) and
[MC10.tla](../examples/MC10.tla).
1. Notice the changes:
  - new variables: `srcTimeoutNums` and `dstTimeoutNums`
  - new operators: `RegisterTimeout` and `ApplyTimeout`
1. Check the property `InFlyPacketIsSecured` by running:

    ```sh
    $ apalache-mc check --inv=InFlyPacketIsSecured MC10.tla
    ```


## Version NNN: Fungible token transfer

If you are not tired, you can check
[ICS20](https://github.com/cosmos/ics/tree/master/spec/ics-020-fungible-token-transfer)
and improve `TokenTransfer10.tla` to support the full token transfer protocol.

