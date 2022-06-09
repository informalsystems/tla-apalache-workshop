#!/usr/bin/env bash

CSV=./fig/sim-cpp.csv
echo "name,mean,stddev" >$CSV

for l in 5 10; do
    for a in 3 5 10; do
        for v in 2 10 20; do
            perl -pi -e "s/NADDR = .*;/NADDR = $a;/" sim_erc20.cpp
            perl -pi -e "s/NAMOUNTS = .*;/NAMOUNTS = $v;/" sim_erc20.cpp
            perl -pi -e "s/NSTEPS = .*;/NSTEPS = $l;/" sim_erc20.cpp
            g++ -Wall -O3 -o sim_erc20 sim_erc20.cpp
            hyperfine -m 100 --export-csv /tmp/r.csv ./sim_erc20
            tail -n 1 /tmp/r.csv \
                | cut -d "," -f 2,3 \
                | sed "s/^/L$l-A$a-V$v,/" >>$CSV
        done
    done
done
