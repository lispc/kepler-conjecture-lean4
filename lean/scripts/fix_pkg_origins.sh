#!/usr/bin/env bash
# fix_pkg_origins.sh — 隔离克隆的 mathlib 截断根治（2026-10-19）
# 用法: 在克隆的 lean/ 目录里 bash scripts/fix_pkg_origins.sh
# 原理: 全局 insteadOf(https→git@) 让 lake clone 时把改写后的 origin 存进
# 包仓库，而 lake-manifest.json 记的是 https 原形 → lake 校验 origin≠manifest
# 判 "URL changed" → 删包重克隆 → 网络截断(646M/6.5G)。本脚本把每个包的
# origin 逐字重写为 manifest 记的 URL，校验恒等，重克隆永不触发。
set -euo pipefail
MANIFEST=lake-manifest.json
[ -f "$MANIFEST" ] || { echo "no lake-manifest.json (先拷主仓的!)"; exit 1; }
n=0
python3 - "$MANIFEST" <<'PY' | while IFS=$'\t' read -r pkg url; do
import json,sys
m=json.load(open(sys.argv[1]))
for p in m.get("packages",[]):
    name=p.get("name"); url=p.get("url")
    if name and url: print(f"{name}\t{url}")
PY
  d=".lake/packages/$pkg"
  if [ -d "$d/.git" ]; then
    cur=$(git -C "$d" remote get-url origin 2>/dev/null || echo "")
    if [ "$cur" != "$url" ]; then git -C "$d" remote set-url origin "$url"; echo "fixed: $pkg"; n=$((n+1)); fi
  fi
done
echo "origins normalized."
