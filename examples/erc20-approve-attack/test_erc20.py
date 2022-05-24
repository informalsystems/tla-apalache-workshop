#!/usr/bin/env python3

import unittest

from hypothesis import given, strategies as st
from hypothesis.stateful import Bundle, RuleBasedStateMachine
from hypothesis.stateful import rule, consumes, invariant, initialize
from hypothesis import assume, settings, event, Verbosity

# The list of addresses to use. We could use real addresses here,
# but simple readable names are much nicer.
ADDR = [ "Alice", "Bob", "Eve" ]

# We restrict the amounts to a small range, to avoid too much randomness
AMOUNTS = range(0, 4)


class TransferTx:
    """An instance of transfer"""

    def __init__(self, sender, toAddr, value):
        self.tag = "transfer"
        self.sender = sender
        self.toAddr = toAddr
        self.value = value

class TransferFromTx:
    """An instance of transferFrom"""

    def __init__(self, sender, fromAddr, toAddr, value):
        self.tag = "transferFrom"
        self.sender = sender
        self.fromAddr = fromAddr
        self.toAddr = toAddr
        self.value = value

class ApproveTx:
    """An instance of approve"""

    def __init__(self, sender, spender, value):
        self.tag = "approve"
        self.sender = sender
        self.spender = spender
        self.value = value


class Erc20Simulator(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()

    pendingTxs = Bundle("pendingTxs")

    @initialize(amounts=st.lists(st.sampled_from(AMOUNTS),
                min_size=len(ADDR),
                max_size=len(ADDR)))
    def init(self, amounts):
        self.balanceOf = {
            addr: amount for (addr, amount) in zip(ADDR, amounts)
        }
        self.allowance = { (src, dst): 0 for src in ADDR for dst in ADDR }
        self.pendingTxs = set()
        self.lastTx = None

    @rule(target=pendingTxs, _sender=st.sampled_from(ADDR),
            _toAddr=st.sampled_from(ADDR), _value=st.sampled_from(AMOUNTS))
    def add_transfer(self, _sender, _toAddr, _value):
        tx = TransferTx(_sender, _toAddr, _value)
        self.pendingTxs.add(tx)
        return tx

    @rule(target=pendingTxs, _sender=st.sampled_from(ADDR),
            _fromAddr=st.sampled_from(ADDR),
            _toAddr=st.sampled_from(ADDR), _value=st.sampled_from(AMOUNTS))
    def add_transfer_from(self, _sender, _fromAddr, _toAddr, _value):
        tx = TransferFromTx(_sender, _fromAddr, _toAddr, _value)
        self.pendingTxs.add(tx)
        return tx

    @rule(target=pendingTxs, _sender=st.sampled_from(ADDR),
            _spender=st.sampled_from(ADDR), _value=st.sampled_from(AMOUNTS))
    def add_approve(self, _sender, _spender, _value):
        tx = ApproveTx(_sender, _spender, _value)
        self.pendingTxs.add(tx)
        return tx

    @rule(tx=consumes(pendingTxs))
    def process_transfer(self, tx):
        assume(tx.tag == "transfer" \
               and tx.value <= self.balanceOf[tx.sender] \
               and tx.value > 0 \
               and tx.sender != tx.toAddr)
        self.pendingTxs.remove(tx)
        self.balanceOf[tx.sender] -= tx.value
        self.balanceOf[tx.toAddr] += tx.value
        self.lastTx = tx
        event("transfer")

    @rule(tx=consumes(pendingTxs))
    def process_transfer_from(self, tx):
        assume(tx.tag == "transferFrom" \
               and tx.value > 0 \
               and tx.value <= self.balanceOf[tx.fromAddr] \
               and tx.value <= self.allowance[(tx.fromAddr, tx.sender)] \
               and tx.fromAddr != tx.toAddr)
        self.pendingTxs.remove(tx)
        self.balanceOf[tx.fromAddr] -= tx.value
        self.balanceOf[tx.toAddr] += tx.value
        self.allowance[(tx.fromAddr, tx.sender)] -= tx.value
        self.lastTx = tx
        event("transferFrom")

    @rule(tx=consumes(pendingTxs))
    def process_approve(self, tx):
        assume(tx.tag == "approve" \
               and tx.value > 0 and tx.sender != tx.spender)
        self.pendingTxs.remove(tx)
        self.allowance[(tx.sender, tx.spender)] = tx.value
        self.lastTx = tx
        event("approve")

    @invariant()
    def non_negative_balances(self):
        for addr in ADDR:
            assert(self.balanceOf[addr] >= 0)

    @invariant()
    def all_transfers_approved(self):
        last = self.lastTx
        if last:
            if last.tag == "transferFrom" and last.value > 0:
                for p in self.pendingTxs:
                    if p.tag == "approve" \
                            and p.sender == last.fromAddr \
                            and p.spender == last.sender \
                            and last.sender != last.toAddr \
                            and p.value < last.value and p.value > 0:
                        assert(false)

    # Uncomment the following invariant to check,
    # whether it is possible to have allowances in progress.
#    @invariant()
#    def no_approval(self):
#        for sender in ADDR:
#            for spender in ADDR:
#                assert(self.allowance[(sender, spender)] <= 0)

    # Uncomment the following invariant to check,
    # whether it is possible to have allowances in progress.
#    @invariant()
#    def no_transfers_from(self):
#        for sender in ADDR:
#            for spender in ADDR:
#                total = self.histSumTransferFrom[(sender, spender)]
#                assert(total == 0)


TestTrees = Erc20Simulator.TestCase

Erc20Simulator.TestCase.settings = settings(
    max_examples=100000, stateful_step_count=10, deadline=None)

if __name__ == "__main__":
    unittest.main()
