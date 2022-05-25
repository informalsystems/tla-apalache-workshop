def count(txs, n):
    if n > 5:
        # produced 5 steps
        return 1

    # submit one more transaction
    ntransfer = count(txs + [0], n + 1) * 180
    napprove  = count(txs + [1], n + 1) * 180
    ntransfer_from = count(txs + [2], n + 1) * 540
    # consume one of the transactions
    nctransfer = 0
    if 0 in txs:
        copy = txs[:]
        copy.remove(0)
        nctransfer = count(copy, n + 1) * 0.2375

    ncapprove = 0
    if 1 in txs:
        copy = txs[:]
        copy.remove(1)
        ncapprove = count(copy, n + 1) * 0.475

    nctransfer_from = 0
    if 2 in txs:
        copy = txs[:]
        copy.remove(2)
        nctransfer_from = count(copy, n + 1) * 0.1128125

    return ntransfer + napprove + ntransfer_from \
            + ncapprove + nctransfer + nctransfer_from

print("number of combinations: %d" % count([], 1))
