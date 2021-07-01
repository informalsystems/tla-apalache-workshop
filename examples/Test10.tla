---------------------------------- MODULE Test10 ------------------------------
\* Unit tests for version 10
EXTENDS MC10

\* bound sequence numbers for TypeOK
BOUNDED_SEQ_NOS == 0..5
\* bound amounts for TypeOK
BOUNDED_AMOUNTS == 0..100

\* An invariant on the variable shapes, assuming bounded sequence numbers.
\* As we have to use bounded amount, Init may violate TypeOK!
TypeOK ==
    /\ banks \in [ CHAINS \X ACCOUNTS \X DENOMS -> BOUNDED_AMOUNTS ]
    /\ sentPackets \in SUBSET [
            seqNo: BOUNDED_SEQ_NOS,
            src: CHAINS,
            dest: CHAINS,
            data: [
                sender: ACCOUNTS,
                receiver: ACCOUNTS,
                denom: DENOMS,
                amount: BOUNDED_AMOUNTS
            ]
        ]
    /\ deliveredNums \in SUBSET BOUNDED_SEQ_NOS
    /\ dstTimeoutNums \in SUBSET BOUNDED_SEQ_NOS
    /\ srcTimeoutNums \in SUBSET BOUNDED_SEQ_NOS
    /\ seqno \in BOUNDED_SEQ_NOS

\* the "classical" approach to produce states
TypeOKandSupply ==
    /\ TypeOK
    /\ AllChainsSupplyUnchanged

\* the "generators" approach
TestApplyTimeoutRequires ==
    /\ \E b \in [ CHAINS \X ACCOUNTS \X DENOMS -> Nat ]:
        banks = b
    /\ \E n \in Nat:
        seqno = n
    \* bound the sizes of data structures by 100
    /\ sentPackets = Gen(100)
    /\ deliveredNums = Gen(100)
    /\ dstTimeoutNums = Gen(100)
    /\ srcTimeoutNums = Gen(100)
    /\ AllChainsSupplyUnchanged

\* action to execute
TestApplyTimeoutAction ==
    ApplyTimeout

\* what we expect at the output    
TestApplyTimeoutEnsures ==
    AllChainsSupplyUnchanged

===============================================================================
