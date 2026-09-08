#!/bin/bash
# Phase 4 (b): dReal batch over out/smt/*.smt2
# usage: run_dreal_batch.sh [precision] [timeout_s] [parallel]
PREC=${1:-0.001}; TO=${2:-300}; PAR=${3:-32}
DREAL=$(dirname $0)/../tools/dreal-4.21.06.2/bin/dreal
OUT=$(dirname $0)/out/dreal_log
mkdir -p $OUT
ls $(dirname $0)/out/smt/*.smt2 | xargs -P $PAR -I{} sh -c '
  f={}; b=$(basename $f .smt2); s=$(date +%s)
  timeout '"$TO"' '"$DREAL"' --precision '"$PREC"' $f > '"$OUT"'/$b.txt 2>&1
  rc=$?; e=$(date +%s)
  r=$(grep -oE "unsat|delta-sat" '"$OUT"'/$b.txt | head -1)
  echo "$b rc=$rc result=${r:-none} $((e-s))s"
' | sort > $(dirname $0)/out/dreal_results.txt
echo "=== summary ==="
awk '{for(i=1;i<=NF;i++) if($i~/^result=/) print $i}' $(dirname $0)/out/dreal_results.txt | sort | uniq -c
