#!/bin/bash
# TM 实战验收计时组：顺序跑（并发 1），结果落 out/tm_c/bench_*.log
cd "$(dirname "$0")"
C0=out/cases_prep/prep-BIXPCGW_7274157868_a_split_0_2.json
C1=out/cases_prep/prep-BIXPCGW_7274157868_a_split_1_2.json
echo "start $(date -Is)" > out/tm_c/bench.status
run() {  # run <tag> <case> <extra args...>
  tag=$1; shift; c=$1; shift
  echo "running $tag $(date -Is)" >> out/tm_c/bench.status
  { /usr/bin/time -v nice -n 19 ./bb_arb "$c" --max-nodes 4000000 "$@"; } \
    > "out/tm_c/bench_${tag}.log" 2>&1
  echo "done $tag rc=$? $(date -Is)" >> out/tm_c/bench.status
}
run bare_s0 "$C0"
run tm_s0 "$C0" --tm
run tm_w1_s0 "$C0" --tm --tm-w0 1.0
run bare_s1 "$C1"
run tm_s1 "$C1" --tm
echo "ALL-DONE $(date -Is)" >> out/tm_c/bench.status
