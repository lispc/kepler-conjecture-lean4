#!/bin/bash
# dep_sweep.sh — 逐模块直接依赖边扫描（census v3 管线第 2 段）
# 用法: dep_sweep.sh <outfile> <module-file...>   （路径相对 lean/，顺序即扫描序）
# 原理: import 后 value? 被擦除，故把模块源码复制到 /tmp、追加命名空间 end +
# 扫描片段后在本进程内重新 elaboration——当前模块常量此时有完整 value，
# 可提取 Kepler→Kepler 直接依赖边与字面 taint。
cd /Users/zhangzhuo/repos/kepler-conjecture-lean4/lean || exit 1
export PATH="$HOME/.elan/bin:$PATH"
OUT="$1"; shift
: > "$OUT"
i=0
for f in "$@"; do
  i=$((i+1))
  mod=$(basename "$f" .lean)
  tmp="/tmp/dep_scan_work.lean"
  cp "$f" "$tmp"
  ns=$(grep '^namespace' "$f" | tail -1 | awk '{print $2}')
  if [ -n "$ns" ]; then printf '\nend %s\n' "$ns" >> "$tmp"; else printf '\n' >> "$tmp"; fi
  cat scripts/dep_scan_snippet.lean >> "$tmp"
  if lake env lean "$tmp" >> "$OUT" 2>>/tmp/dep_sweep_err.log; then
    echo "[$i/$#] OK $mod" >&2
  else
    echo "[$i/$#] FAIL $mod (详 /tmp/dep_sweep_err.log)" >&2
  fi
done
echo "SWEEP_COMPLETE $(grep -c '^DEP' "$OUT") edges" >&2
