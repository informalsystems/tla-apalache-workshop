------------------------------ MODULE ClockSync6 ------------------------------
(*
 * Incremental TLA+ specification of the clock synchronization algorithm from:
 *
 * Hagit Attiya, Jennifer Welch. Distributed Computing. Wiley Interscience, 2004,
 * p. 147, Algorithm 20.
 *
 * Assumptions: timestamps are natural numbers, not reals.
 *
 * Version 6: Make Proc a parameter and use FoldSet
 * Version 5: Ignoring the message by the process itself
 * Version 4: Adjusting clock values (test 4 + invariant violation)
 * Version 3: Receiving messages (test 3)
 * Version 2: Sending messages (test 2)
 * Version 1: Setting up the clocks (test 1)
 *)
EXTENDS Integers, FiniteSets, Apalache

CONSTANTS
    \* the set of processes
    \* @type: Set(Str);
    Proc,
    \* minimum message delay
    \* @type: Int;
    t_min,
    \* maximum message delay
    \* @type: Int;
    t_max

ASSUME(t_min >= 0 /\ t_max >= t_min)

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

(***************************** DEFINITIONS *********************************)

\* the number of processes
NProc == Cardinality(Proc)

\* control states
State == { "init", "sent", "sync" }

\* the adjusted clock of process i
AC(i) == hc[i] + adj[i]

\* sum up the clock differences as observed by a process p
\* @type: (<<Str, Str>> -> Int, Str) => Int;
DiffSum(df, p) ==
    LET Add(total, q) ==
        total + df[p, q]
    IN
    FoldSet(Add, 0, Proc)

(*************************** INITIALIZATION ********************************)

\* Initialization
Init ==
  /\ time \in Nat
  /\ hc \in [ Proc -> Nat ]
  /\ adj = [ p \in Proc |-> 0 ]
  /\ diff = [ <<p, q>> \in Proc \X Proc |-> 0 ]
  /\ state = [ p \in Proc |-> "init" ]
  /\ msgs = {}
  /\ rcvd = [ p \in Proc |-> {} ]

(******************************* ACTIONS ***********************************)

\* send the value of the hardware clock
SendMsg(p) ==
  /\ state[p] = "init"
  /\ msgs' = msgs \union { [ src |-> p, ts |-> hc[p] ] }
  /\ state' = [ state EXCEPT ![p] = "sent" ]
  /\ UNCHANGED <<time, hc, adj, diff, rcvd>>

\* If the process has received a message from all processes (but p),
\* then adjust the clock. Otherwise, accumulate the difference.
\* @type: (Str, <<Str, Str>> -> Int,
\*         Set([src: Str, ts: Int])) => Bool;
AdjustClock(p, newDiff, newRcvd) ==
  LET fromAll == { m.src: m \in newRcvd } = Proc \ { p } IN
  IF fromAll
  THEN
    \* Assuming that Proc = { "p1", "p2" }.
    \* See ClockSync5 for the general case.
    /\ adj' = [ adj EXCEPT ![p] = DiffSum(newDiff, p) \div NProc ]
    /\ state' = [ state EXCEPT ![p] = "sync" ]
  ELSE
    UNCHANGED <<adj, state>>

\* Receive a message sent by another process.
\* Adjust the clock if the message has been received from all processes.
ReceiveMsg(p) ==
  /\ state[p] = "sent"
  /\ \E m \in msgs:
      /\ m \notin rcvd[p]
      /\ m.src /= p     \* ignore the message by p itself
      \* the message cannot be received earlier than after t_min
      /\ hc[m.src] >= m.ts + t_min
      \* accumulate the difference and adjust the clock if possible
      /\ LET delta == m.ts - hc[p] + (t_min + t_max) \div 2 IN
         LET newDiff == [ diff EXCEPT ![p, m.src] = delta ] IN
         LET newRcvd == rcvd[p] \union { m } IN
          /\ AdjustClock(p, newDiff, newRcvd)
          /\ rcvd' = [ rcvd EXCEPT ![p] = newRcvd ]
          /\ diff' = newDiff
  /\ UNCHANGED <<time, hc, msgs>>

\* let the time flow
AdvanceClocks(delta) ==
  /\ delta > 0
  \* clocks can be advanced only if there is no pending message
  /\ \A m \in msgs:
        hc[m.src] + delta > t_max =>
            \A p \in Proc:
                m \in rcvd[m.src]
  \* clocks are advanced uniformly
  /\ time' = time + delta
  /\ hc' = [ p \in Proc |-> hc[p] + delta ]
  /\ UNCHANGED <<adj, diff, msgs, state, rcvd>>

\* all actions together
Next ==
  \/ \E delta \in Int:
      AdvanceClocks(delta)
  \/ \E p \in Proc:
      \/ SendMsg(p)
      \/ ReceiveMsg(p)

(******************************* PROPERTIES **********************************)

\* Theorem 6.15 from AW04:
\* Algorithm achieves u * (1 - 1/n)-synchronization for n processors.
SkewInv ==
    LET allSync ==
        \A p \in Proc: state[p] = "sync"
    IN
    LET boundedSkew ==
        LET bound ==
          \* extend the bound by NProc to account for rounding errors
          (t_max - t_min) * (NProc - 1) + NProc * NProc
        IN
        \A p, q \in Proc:
            LET df == AC(p) - AC(q)
            IN
            -bound <= df * NProc /\ df * NProc <= bound
    IN
    allSync => boundedSkew

===============================================================================
