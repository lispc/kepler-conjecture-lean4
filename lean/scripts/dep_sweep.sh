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
  # EOF 时仍打开的作用域名: namespace/section 压栈, end 就近配对弹出(裸 end 弹一层)
  ns=$(awk '
    $1=="namespace" && $2 != "" { stack[++n] = $2; next }
    $1=="section"  && $2 != "" { stack[++n] = $2; next }
    $1=="end" && $2 != "" { for (j = n; j >= 1; j--) if (stack[j] == $2) { n = j - 1; break }; next }
    $1=="end" { if (n > 0) n--; next }
    END { if (n > 0) print stack[n] }' "$f")
  if [ -n "$ns" ]; then printf '\nend %s\n' "$ns" >> "$tmp"; else printf '\n' >> "$tmp"; fi
  # 块标记: ranker 据此把本块内 _private._stdin.0.* 名重写回真实模块名
  # (扫描副本按主文件 _stdin elaboration, 本模块私有名的 Mangling 模块段失真)
  scanmod=$(echo "${f%.lean}" | tr '/' '.')
  echo "SCAN_MODULE $scanmod" >> "$OUT"
  cat scripts/dep_scan_snippet.lean >> "$tmp"
  if lake env lean "$tmp" >> "$OUT" 2>>/tmp/dep_sweep_err.log; then
    echo "[$i/$#] OK $mod" >&2
  else
    echo "[$i/$#] FAIL $mod (详 /tmp/dep_sweep_err.log)" >&2
  fi
done
echo "SWEEP_COMPLETE $(grep -c '^DEP' "$OUT") edges" >&2
