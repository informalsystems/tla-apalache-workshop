---------------------------- MODULE MC_ClockSync1 -----------------------------

VARIABLES
    \* the reference clock, inaccessible to the processes
    \* @type: Int;
    time,
    \* hardware clock of a process
    \* @type: Str -> Int;
    hc,
    \* clock adjustment of a process
    \* @type: Str -> Int;
    adj

INSTANCE ClockSync1

\* test that the clocks are non-decreasing
Test1_Init ==
  /\ time \in Nat
  /\ hc \in [ Proc -> Nat ]
  /\ adj \in [ Proc -> Int ]

Test1_Next ==
  \E delta \in Int:
    AdvanceClocks(delta)

Test1_Inv  ==
  /\ time' >= time
  /\ \A p \in Proc: hc'[p] >= hc[p]

===============================================================================
