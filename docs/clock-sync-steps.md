# Clock Synchronization with Apalache

## Version 1: Introducing clocks

1. Open [ClockSync1][] and [MC_ClockSync1][].
1. Notice how the variables `time`, `hc`, and `adj` are declared.
1. Check the type annotations that start with `@type`.
1. Check the test in [MC_ClockSync1][].
1. Run:

    ```sh
    $ apalache check --init=Test1_Init \
        --next=Test1_Next --inv=Test1_Inv --length=1 MC_ClockSync1.tla
    ```

4. The tool reports no error.

## Version 2: Sending messages

1. Open [ClockSync2][] and [MC_ClockSync2][].
1. Check constants `t_min` and `t_max`.
1. Notice that variables `msgs` and `state` are added.
1. Check the test in [MC_ClockSync2][].
1. Run:

    ```sh
    $ apalache check --init=Test2_Init \
        --next=Test2_Next --inv=Test2_Inv --length=1 MC_ClockSync2.tla
    ```

4. The tool reports no error.

## Version 3: Receiving messages

1. Open [ClockSync3][] and [MC_ClockSync3][].
1. Notice that variable `rcvd` is added.
1. Check the test in [MC_ClockSync3][].
1. Run:

    ```sh
    $ apalache check --init=Test3_Init \
        --next=Test3_Next --inv=Test3_Inv --length=1 MC_ClockSync3.tla
    ```

4. The tool reports no error.

## Version 4: Adjusting clocks

1. Open [ClockSync4][] and [MC_ClockSync4][].
1. Notice that variable `diff` is added.
1. Check the test in [MC_ClockSync4][].
1. Run:

    ```sh
    $ apalache check --init=Test4_Init \
        --next=Test4_Next --inv=Test4_Inv --length=1 MC_ClockSync4.tla
    ```

5. The tool reports no error.
1. Check the invariant `SkewInv` in [ClockSync4][].
1. Run:

    ```sh
    $ apalache check --inv=SkewInv MC_ClockSync4.tla
    ```

8. The tool reports an error. Open `counterexample1.tla`.

## Version 5: Ignoring self-messages

1. Open [ClockSync5][] and [MC_ClockSync5][].
1. Notice the changes in `AdjustClock`.
1. Run:

    ```sh
    $ apalache check --inv=SkewInv MC_ClockSync5.tla
    ```

5. The tool reports no error.

## Version 6: Parameterizing the set of processes

1. Open [ClockSync6][] and [MC_ClockSync6][].
1. Notice that we made `Proc` a constant.
1. Check the operator `DiffSum` and how it is used.
1. Run:

    ```sh
    $ apalache check --inv=SkewInv MC_ClockSync6.tla
    ```

## Version 6p: ConstInit to check arbitrary t_min and t_max

1. Open [MC_ClockSync6p][].
1. Check the operator `ConstInit`.
1. Check how we have changed the bound in `SkewInv`.
1. Run:

    ```sh
    $ apalache check --cinit=ConstInit --inv=SkewInv MC_ClockSync6p.tla
    ```

5. The tool reports no error.

[ClockSync1]: ../examples/clock-sync/ClockSync1.tla
[ClockSync2]: ../examples/clock-sync/ClockSync2.tla
[ClockSync3]: ../examples/clock-sync/ClockSync3.tla
[ClockSync4]: ../examples/clock-sync/ClockSync4.tla
[ClockSync5]: ../examples/clock-sync/ClockSync5.tla
[ClockSync6]: ../examples/clock-sync/ClockSync6.tla
[ClockSync6p]: ../examples/clock-sync/ClockSync6p.tla
[ClockSync7]: ../examples/clock-sync/ClockSync7.tla
[MC_ClockSync1]: ../examples/clock-sync/MC_ClockSync1.tla
[MC_ClockSync2]: ../examples/clock-sync/MC_ClockSync2.tla
[MC_ClockSync3]: ../examples/clock-sync/MC_ClockSync3.tla
[MC_ClockSync4]: ../examples/clock-sync/MC_ClockSync4.tla
[MC_ClockSync5]: ../examples/clock-sync/MC_ClockSync5.tla
[MC_ClockSync6]: ../examples/clock-sync/MC_ClockSync6.tla
[MC_ClockSync7]: ../examples/clock-sync/MC_ClockSync7.tla

