#!/usr/bin/env bash
#
# Run all unit tests

set -e

trap ctrl_c INT
function ctrl_c() {
    echo "Terminating the test suite..."
    kill -9 $$
}

VER="ghcr.io/informalsystems/apalache:unstable"
docker pull "$VER"
apalache="docker run --rm -v $(pwd):/var/apalache $VER"

TEST="$1"

function test() {
  if [ -z "$TEST" -o "$TEST" == $1 ]; then
    $apalache check --init=$2 --next=$3 --inv=$4 --length=1 $5 \
        2>&1 >test$1.out \
      || echo "TEST $1 FAILED: $5 on $2 $3 $4"
  fi
}

test 1 Test1_Init Test1_Next Test1_Inv MC_ClockSync1.tla
test 2 Test1_Init Test1_Next Test1_Inv MC_ClockSync2.tla
test 3 Test1_Init Test1_Next Test1_Inv MC_ClockSync3.tla
test 4 Test1_Init Test1_Next Test1_Inv MC_ClockSync4.tla
test 5 Test1_Init Test1_Next Test1_Inv MC_ClockSync5.tla
test 6 Test1_Init Test1_Next Test1_Inv MC_ClockSync6.tla

test 7 Test2_Init Test2_Next Test2_Inv MC_ClockSync2.tla
test 8 Test2_Init Test2_Next Test2_Inv MC_ClockSync3.tla
test 9 Test2_Init Test2_Next Test2_Inv MC_ClockSync4.tla
test 10 Test2_Init Test2_Next Test2_Inv MC_ClockSync5.tla
test 11 Test2_Init Test2_Next Test2_Inv MC_ClockSync6.tla

test 12 Test3_Init Test3_Next Test3_Inv MC_ClockSync3.tla
test 13 Test3_Init Test3_Next Test3_Inv MC_ClockSync4.tla
test 14 Test3_Init Test3_Next Test3_Inv MC_ClockSync5.tla
test 15 Test3_Init Test3_Next Test3_Inv MC_ClockSync6.tla

test 16 Test4_Init Test4_Next Test4_Inv MC_ClockSync4.tla
test 17 Test4_Init Test4_Next Test4_Inv MC_ClockSync5.tla
test 18 Test4_Init Test4_Next Test4_Inv MC_ClockSync6.tla

