/**
 * Simulation of the ERC20 API in C++.
 * To measure the performance of a hand-coded simulation.
 *
 * Igor Konnov, Informal Systems, 2022
 */

#include <iostream>
#include <vector>

#include <stdlib.h>
#include <time.h>

using namespace std;

// use this value to limit NAMOUNTS
const unsigned MAX_UINT16 = (1 << 15) - 1 + (1u << 15);

/**
 * Number of addresses to pick from.
 */
const unsigned NADDR = 10;

/**
 * Number of amounts to pick from.
 */
const unsigned NAMOUNTS = 20;

/**
 * Number of steps to try in each simulation run.
 */
const unsigned NSTEPS = 10;

/**
 * Number of simulation runs.
 */
const unsigned NRUNS = 1000000000;

/**
 * Number of random before a run is completely discarded.
 */
const unsigned NTRIES = 3;

/**
 * The datatype to use to encode the amounts.
 * Although Ethereum has 256-bit values, we limit the values to
 * machine integers, for simulation purposes.
 */
typedef int amount_t;

enum TxType {
    None, Transfer, TransferFrom, Approve,
    CommitTransfer, CommitTransferFrom, CommitApprove
};

/**
 * A transaction of one of three types: transfer, transferFrom, or approve.
 */
struct Tx {
    TxType txType;
    union {
        struct {
            unsigned sender;
            unsigned toAddr;
            amount_t value;
        } transferData;
        struct {
            unsigned sender;
            unsigned fromAddr;
            unsigned toAddr;
            amount_t value;
        } transferFromData;
        struct {
            unsigned sender;
            unsigned spender;
            amount_t value;
        } approveData;
    };
};

/**
 * A state of our ERC20 state machine.
 */
class StateMachine {
    /**
     * The balance for each account.
     */
    amount_t balanceOf[NADDR];
    /**
     * Allowance from a sender to a spender.
     */
    amount_t allowance[NADDR][NADDR];
    /**
     * Pending transfers.
     */
    vector<Tx> pendingTransfers;
    /**
     * Pending transferFroms.
     */
    vector<Tx> pendingTransferFroms;
    /**
     * Pending approves.
     */
    vector<Tx> pendingApproves;

public:

    /**
     * The history trace.
     */
    vector<Tx> history;

    /**
     * Randomly initialize the balances.
     */
    StateMachine() {
        for (int i = 0; i < NADDR; i++) {
            balanceOf[i] = arc4random_uniform(NAMOUNTS);
            fill(allowance[i], allowance[i] + NADDR, 0);
        }
    }

    bool next() {
        switch (arc4random_uniform(6)) {
            case 0: return submit_transfer();
            case 1: return submit_transferFrom();
            case 2: return submit_approve();
            case 3: return commit_transfer();
            case 4: return commit_transferFrom();
            case 5: return commit_approve();
            default: return false;
        }
    }

    bool invariant_holds() {
        return no_negative_balances() && all_transfers_approved();
    }

    void print_history() {
        for (vector<Tx>::iterator hi = history.begin();
                hi != history.end(); hi++) {
            switch (hi->txType) {
                case Transfer:
                    cout << "submit Transfer: sender="
                         << hi->transferData.sender
                         << " toAddr=" << hi->transferData.toAddr
                         << " value=" << hi->transferData.value << endl;
                    break;

                case TransferFrom:
                    cout << "submit TransferFrom: sender="
                         << hi->transferFromData.sender
                         << " fromAddr=" << hi->transferFromData.fromAddr
                         << " toAddr=" << hi->transferFromData.toAddr
                         << " value=" << hi->transferData.value << endl;
                    break;

                case Approve:
                    cout << "submit Approve: sender=" << hi->approveData.sender
                         << " spender=" << hi->approveData.spender
                         << " value=" << hi->transferData.value << endl;
                    break;

                case CommitTransfer:
                    cout << "commit Transfer: sender="
                         << hi->transferData.sender
                         << " toAddr=" << hi->transferData.toAddr
                         << " value=" << hi->transferData.value << endl;
                    break;

                case CommitTransferFrom:
                    cout << "commit TransferFrom: sender="
                         << hi->transferFromData.sender
                         << " fromAddr=" << hi->transferFromData.fromAddr
                         << " toAddr=" << hi->transferFromData.toAddr
                         << " value=" << hi->transferData.value << endl;
                    break;

                case CommitApprove:
                    cout << "commit Approve: sender=" << hi->approveData.sender
                         << " spender=" << hi->approveData.spender
                         << " value=" << hi->transferData.value << endl;
                    break;

                default:
                    cout << "None" << endl;
            }
        }
    }

private:
    bool submit_transfer() {
        Tx tx;
        tx.txType = Transfer;
        tx.transferData.sender = arc4random_uniform(NADDR);
        tx.transferData.toAddr = arc4random_uniform(NADDR);
        tx.transferData.value = arc4random_uniform(NAMOUNTS);
        pendingTransfers.push_back(tx);
        history.push_back(tx);
        return true;
    }

    bool submit_transferFrom() {
        Tx tx;
        tx.txType = TransferFrom;
        tx.transferFromData.sender = arc4random_uniform(NADDR);
        tx.transferFromData.fromAddr = arc4random_uniform(NADDR);
        tx.transferFromData.toAddr = arc4random_uniform(NADDR);
        tx.transferFromData.value = arc4random_uniform(NAMOUNTS);
        pendingTransferFroms.push_back(tx);
        history.push_back(tx);
        return true;
    }

    bool submit_approve() {
        Tx tx;
        tx.txType = Approve;
        tx.approveData.sender = arc4random_uniform(NADDR);
        tx.approveData.spender = arc4random_uniform(NADDR);
        tx.approveData.value = arc4random_uniform(NAMOUNTS);
        pendingApproves.push_back(tx);
        history.push_back(tx);
        return true;
    }

    bool commit_transfer() {
        if (pendingTransfers.empty()) {
            return false;
        }
        uint32_t index = arc4random_uniform(pendingTransfers.size());
        const Tx* ptx = &pendingTransfers[index];
        amount_t value = ptx->transferData.value;
        unsigned sender = ptx->transferData.sender;
        unsigned toAddr = ptx->transferData.toAddr;
        if (value > 0 && value <= balanceOf[sender]
                && sender != toAddr) {
            balanceOf[sender] -= value;
            balanceOf[toAddr] += value;
            Tx commitTx = *ptx;
            commitTx.txType = CommitTransfer;
            history.push_back(commitTx);
            // Remove the transaction from the vector.
            // O(pendingTransfers.size()).
            pendingTransfers.erase(pendingTransfers.begin() + index);
            return true;
        } else {
            return false;
        }
    }

    bool commit_transferFrom() {
        if (pendingTransferFroms.empty()) {
            return false;
        }
        uint32_t index = arc4random_uniform(pendingTransferFroms.size());
        const Tx* ptx = &pendingTransferFroms[index];
        amount_t value = ptx->transferFromData.value;
        unsigned sender = ptx->transferFromData.sender;
        unsigned fromAddr = ptx->transferFromData.fromAddr;
        unsigned toAddr = ptx->transferFromData.toAddr;
        if (value > 0
                && value <= balanceOf[fromAddr]
                && value <= allowance[fromAddr][sender]
                && fromAddr != toAddr) {
            balanceOf[fromAddr] -= value;
            balanceOf[toAddr] += value;
            allowance[fromAddr][sender] -= value;
            Tx commitTx = *ptx;
            commitTx.txType = CommitTransferFrom;
            history.push_back(commitTx);
            // Remove the transaction from the vector.
            // O(pendingTransferFroms.size()).
            pendingTransferFroms.erase(pendingTransferFroms.begin() + index);
            return true;
        } else {
            return false;
        }
    }

    bool commit_approve() {
        if (pendingApproves.empty()) {
            return false;
        }
        uint32_t index = arc4random_uniform(pendingApproves.size());
        const Tx* ptx = &pendingApproves[index];
        amount_t value = ptx->approveData.value;
        unsigned sender = ptx->approveData.sender;
        unsigned spender = ptx->approveData.spender;
        if (value > 0 && sender != spender) {
            allowance[sender][spender] = value;
            Tx commitTx = *ptx;
            commitTx.txType = CommitApprove;
            history.push_back(commitTx);
            // Remove the transaction from the vector.
            // O(pendingApproves.size()).
            pendingApproves.erase(pendingApproves.begin() + index);
            return true;
        } else {
            return false;
        }
    }

    // a simple invariant to make sure that the balances do not go negative
    bool no_negative_balances() {
        for (unsigned addr = 0; addr < NADDR; addr++) {
            if (balanceOf[addr] < 0) {
                return false;
            }
        }
        return true;
    }

    // If this invariant is violated, then it is possible to transfer tokens
    // (based on an earlier approval), while there is an approval for a
    // smaller amount in the pending transactions
    bool all_transfers_approved() {
        if (history.empty()) {
            return true;
        }

        const Tx* lastTx = &history.back();

        if (lastTx->txType == CommitTransferFrom
                && lastTx->transferFromData.value > 0) {
            for (vector<Tx>::const_iterator pi = pendingApproves.begin();
                    pi != pendingApproves.end();
                    pi++) {
                if (pi->approveData.sender == lastTx->transferFromData.fromAddr
                        && pi->approveData.spender
                            == lastTx->transferFromData.sender
                        && lastTx->transferFromData.sender
                            != lastTx->transferFromData.toAddr
                        && pi->approveData.value < lastTx->approveData.value
                        && pi->approveData.value > 0) {
                    return false;
                }
            }
        }

        return true;
    }
};

int main(int argc, const char* argv[]) {
    cout << "Running the simulation for NADDR="
        << NADDR << " and NAMOUNTS=" << NAMOUNTS << endl;
    cout << "This make take a while unless P = NP..." << endl;
    time_t start = time(NULL);
    unsigned ndiscarded = 0;
    unsigned ngenerated = 0;
    unsigned nretries = 0;
    bool error = false;
    while (ngenerated < NRUNS && !error) {
        StateMachine machine;
        unsigned nsteps = 0;
        // Try to randomly construct a run of NSTEPS steps
        for (; nsteps < NSTEPS && !error; nsteps++) {
            // Try to make a single random step.
            // As it may be hard to find such a step, limit the number of tries.
            unsigned nr = NTRIES;
            for (; nr > 0; nr--, nretries++) {
                if (machine.next()) {
                    // managed to make a random step
                    break;
                }
            }
            if (nr == 0) {
                // all retries were fruitless, no step made
                break;
            } else {
                // made a step, check the invariant
                if (!machine.invariant_holds()) {
                    cout << "Found an invariant violation" << std::endl;
                    machine.print_history();
                    error = true;
                }
            }
        }
        if (nsteps == NSTEPS) {
            // yay, we have generated a run of NSTEPS steps
            ngenerated++;
        } else {
            // meh, we could not generate a run
            ndiscarded++;
        }
    }

    time_t diff = time(NULL) - start;
    cout << "Simulation stats. #generated runs: " << ngenerated
         << " #discarded runs: " << ndiscarded
         << " #retries: " << nretries << " " << endl;
    cout << "It took me " << diff << " seconds" << endl;
    return 0;
}
