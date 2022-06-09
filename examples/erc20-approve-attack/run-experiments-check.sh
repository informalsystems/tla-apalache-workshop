#!/usr/bin/env bash

if [ "$APALACHE_HOME" == "" ]; then
    echo "set APALACHE_HOME to the directory where Apalache resides"
    exit 1
fi

CSV=./fig/apa-check.csv
echo "name,mean,stddev" >$CSV

for l in 5 10; do
    for a in 3 5 10; do
        for v in 2 10 20 Int; do
            perl -pi -e "s/ADDR == .*/ADDR == ADDR$a/" MC_ERC20.tla
            if [ "$v" == "Int" ]; then
                perl -pi -e "s/AMOUNTS == .*/AMOUNTS == Int/" MC_ERC20.tla
            else
                perl -pi -e "s/AMOUNTS == .*/AMOUNTS == 0..$v/" MC_ERC20.tla
            fi
            hyperfine -i -m 10 --export-csv /tmp/r.csv \
                "$APALACHE_HOME/bin/apalache-mc check \
                --length=$l \
                --inv=NoTransferFromWhileApproveInFlight MC_ERC20.tla"
            tail -n 1 /tmp/r.csv \
                | cut -d "," -f 2,3 \
                | sed "s/^/L$l-A$a-V$v,/" >>$CSV
        done
    done
done
