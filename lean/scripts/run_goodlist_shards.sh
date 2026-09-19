#!/usr/bin/env bash
# P6-C good_list shard runner (idempotent, re-entrant).
#
# Compiles every Kepler/Assembly/GoodListShard*.lean with the flock-capped
# lean wrapper, writing .olean into the lake build tree and one status line
# per shard into p6c_goodlist.status.  Shards already marked OK are skipped,
# so the script can be re-run after interruption (incl. SIGKILL) at will.
# Finally compiles the kernel-only combiner GoodListAll.lean.
#
# Usage:  setsid lean/scripts/run_goodlist_shards.sh >/dev/null 2>&1 &
# Status: /home/scroll/repos/kepler-p6c/p6c_goodlist.status
# Logs:   /home/scroll/repos/kepler-p6c/lean/.tmpwork/goodlist/<shard>.log
set -u

ROOT=/home/scroll/repos/kepler-p6c
LEAN_DIR="$ROOT/lean"
STATUS="$ROOT/p6c_goodlist.status"
LOGDIR="$LEAN_DIR/.tmpwork/goodlist"
LEAN_BIN=/home/scroll/toolchains/g4cap/bin/lean   # 64-slot flock wrapper
BLD="$LEAN_DIR/.lake/build/lib/lean/Kepler/Assembly"

mkdir -p "$LOGDIR" "$BLD"
cd "$LEAN_DIR"
export LEAN_PATH=$(PATH="$HOME/.elan/bin:$PATH" lake env printenv LEAN_PATH)

echo "RUN START $(date -Is) pid=$$" >> "$STATUS"

# Prerequisite: GoodListDefs olean (pure defs; rebuild if missing/stale).
if [ ! -f "$BLD/GoodListDefs.olean" ] || \
   [ Kepler/Assembly/GoodListDefs.lean -nt "$BLD/GoodListDefs.olean" ]; then
  if "$LEAN_BIN" -o "$BLD/GoodListDefs.olean" Kepler/Assembly/GoodListDefs.lean \
      > "$LOGDIR/GoodListDefs.log" 2>&1; then
    echo "GoodListDefs OK $(date -Is)" >> "$STATUS"
  else
    echo "GoodListDefs FAIL $(date -Is)" >> "$STATUS"
    echo "RUN ABORT $(date -Is) (defs broken)" >> "$STATUS"
    exit 1
  fi
fi

for f in Kepler/Assembly/GoodListShard*.lean; do
  name=$(basename "$f" .lean)
  if grep -q "^$name OK" "$STATUS" 2>/dev/null; then
    echo "skip $name (already OK)"
    continue
  fi
  if "$LEAN_BIN" -o "$BLD/$name.olean" "$f" > "$LOGDIR/$name.log" 2>&1 \
      && ! grep -q sorryAx "$LOGDIR/$name.log"; then
    echo "$name OK $(date -Is)" >> "$STATUS"
  else
    echo "$name FAIL $(date -Is)" >> "$STATUS"
  fi
done

# Combiner (kernel-only; needs every shard olean above).
if "$LEAN_BIN" -o "$BLD/GoodListAll.olean" Kepler/Assembly/GoodListAll.lean \
    > "$LOGDIR/GoodListAll.log" 2>&1 && ! grep -q sorryAx "$LOGDIR/GoodListAll.log"; then
  echo "GoodListAll OK $(date -Is)" >> "$STATUS"
else
  echo "GoodListAll FAIL $(date -Is)" >> "$STATUS"
fi

echo "RUN END $(date -Is)" >> "$STATUS"
