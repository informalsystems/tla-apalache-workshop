---------------------------- MODULE MC_ClockSync7 -----------------------------
EXTENDS Integers

Proc == { "p1", "p2", "p3" }

CONSTANTS
    \* @type: Int;
    t_min,
    \* maximum message delay
    \* @type: Int;
    t_max

ASSUME(t_min >= 0 /\ t_max > t_min)    

VARIABLES
    \* the reference clock, inaccessible to the processes
    \* @type: Int;
    time,
    \* hardware clock of a process
    \* @type: Str -> Int;
    hc,
    \* clock adjustment of a process
    \* @type: Str -> Int;
    adj,
    \* clock diff for process j, as seen by a process j
    \* @type: <<Str, Str>> -> Int;
    diff,
    \* messages sent by the processes
    \* @type: Set([src: Str, ts: Int]);
    msgs,
    \* messages received by the processes
    \* @type: Str -> Set([src: Str, ts: Int]);
    rcvd,
    \* the control state of a process
    \* @type: Str -> Str;
    state

INSTANCE ClockSync7

\* use --cinit=ConstInit to check for all t_min and t_max
ConstInit ==
    /\ t_min \in Nat
    /\ t_max \in Nat

===============================================================================
