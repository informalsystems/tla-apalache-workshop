------------------------------ MODULE ClockSync1 ------------------------------
(*
 * Incremental TLA+ specification of the clock synchronization algorithm from:
 *
 * Hagit Attiya, Jennifer Welch. Distributed Computing. Wiley Interscience, 2004,
 * p. 147, Algorithm 20.
 *
 * Assumptions: timestamps are natural numbers, not reals.
 *
 * Version 1: Setting up the clocks
 *)
EXTENDS Integers

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

(***************************** DEFINITIONS *********************************)

\* we fix the set to contain two processes
Proc == { "p1", "p2" }

\* the adjusted clock of process i
AC(i) == hc[i] + adj[i]

(*************************** INITIALIZATION ********************************)

\* Initialization
Init ==
  /\ time \in Nat
  /\ hc \in [ Proc -> Nat ]
  /\ adj = [ p \in Proc |-> 0 ]

(******************************* ACTIONS ***********************************)

\* let the time flow
AdvanceClocks(delta) ==
  /\ delta > 0
  /\ time' = time + delta
  /\ hc' = [ p \in Proc |-> hc[p] + delta ]
  /\ UNCHANGED adj

\* all actions together
Next ==
  \E delta \in Int:
    AdvanceClocks(delta)

(******************************* PROPERTIES ***********************************)
NaiveSkewInv ==
  \A p, q \in Proc:
    AC(p) = AC(q)
      
===============================================================================
