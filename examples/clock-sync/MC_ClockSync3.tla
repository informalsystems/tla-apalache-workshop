---------------------------- MODULE MC_ClockSync3 -----------------------------

t_min == 17
t_max == 91

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
    \* messages sent by the processes
    \* @type: Set([src: Str, ts: Int]);
    msgs,
    \* messages received by the processes
    \* @type: Str -> Set([src: Str, ts: Int]);
    rcvd,
    \* the control state of a process
    \* @type: Str -> Str;
    state

INSTANCE ClockSync3

\* like TypeOK, but used only in initialization
TypeInit ==
  /\ time \in Nat
  /\ hc \in [ Proc -> Nat ]
  /\ adj \in [ Proc -> Int ]
  /\ state \in [ Proc -> State ]
  /\ \E t \in [ Proc -> Int ]:
     msgs \in SUBSET { [ src |-> p, ts |-> t[p] ]: p \in Proc }
  /\ rcvd \in [ Proc -> SUBSET msgs ]

\* test that the clocks are non-decreasing
Test1_Init ==
  TypeInit

Test1_Next ==
  \E delta \in Int:
    AdvanceClocks(delta)

Test1_Inv  ==
  /\ time' >= time
  /\ \A p \in Proc: hc'[p] >= hc[p]

\* test that messages are sent
Test2_Inv ==
  \A p \in Proc:
    state[p] = "sent" <=>
      \E m \in msgs:
        m.src = p

Test2_Init ==
  /\ TypeInit
  /\ Test2_Inv

Test2_Next ==
  \E p \in Proc:
    SendMsg(p)

\* test that messages are received within [t_min, t_max]
Test3_Inv ==
  /\ \A m \in msgs:
      \* no messages from the future
      m.ts <= hc[m.src]
  /\ \A p \in Proc:
      \A m \in rcvd[p]:
        \* the message is received no earlier than after t_min
        hc[m.src] >= m.ts + t_min
  /\ \A m \in msgs:
      \* the message is received no later than before t_max
      m.ts >= hc[m.src] + t_max =>
        \A p \in Proc:
          m \in rcvd[p]

Test3_Init ==
  /\ TypeInit
  /\ Test3_Inv

Test3_Next ==
  \/ \E delta \in Int:
      AdvanceClocks(delta)
  \/ \E p \in Proc:
      ReceiveMsg(p)

===============================================================================
