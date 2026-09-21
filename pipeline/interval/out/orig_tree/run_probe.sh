#!/bin/bash
# run_probe.sh <name> — 编译 orig-tree 探针驱动并跑 pinned rung 12/-64
# setsid + 状态文件纪律; nice 19; 单进程
set -u
G4E=/home/scroll/repos/kepler-g4e
name=$1
d=$G4E/pipeline/interval/out/orig_tree/$name.d
st=$G4E/pipeline/interval/out/orig_tree/$name.status
log=$G4E/pipeline/interval/out/orig_tree/$name.run.log
rel=Kepler/Interval/Cases/Repair/Probe${name#probe}.lean
cp "$d/driver.lean" "$G4E/lean/$rel"
echo "RUNNING $(date +%s)" > "$st"
(
  cd "$G4E/lean"
  nice -n 19 lake env lean --run "$rel" "$d/boxes.txt" 12 -64
) > "$log" 2>&1
rc=$?
echo "DONE rc=$rc $(date +%s)" >> "$st"
