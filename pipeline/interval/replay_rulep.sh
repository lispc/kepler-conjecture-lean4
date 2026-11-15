#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# Rule P batch replay template (TSKAJXY family B, 1,400 leaves).
#
# NOT run by guardrule-w1; handed to the orchestrator for the full replay.
# Each leaf:
#   1) emit main sqrt certs + point certs with the bit-exact Python replica
#      (emit_tm_params.py --rule P --rung $RUNG);
#   2) kernel-check the generated module (`decide +kernel` on
#      checkPosTMHullP) with the Rule P CertTM olean installed in an island;
#   3) record RC, wall, RSS and the `#print axioms` lines.
#
# Prerequisites (orchestrator):
#   * CertTM with the Rule P section landed and its olean installed, or an
#     island tree built per AGENTS §4:
#         island/Kepler/Interval/CertTM.olean   <- new CertTM
#         island/Kepler/...                     <- symlink farm of .lake
#   * LEAN_PATH must put the island first (first entry containing Kepler/).
#   * the leaf list: leaf indices with base NEG (family B).  From the
#     guardcons-w1 artifact:
#         awk -F'\t' 'NR>1 && $2+0<0 {print $1}' logs/familyB_all.tsv \
#           > familyB.idx            # exactly 1,400 lines
#
# Usage:
#   LEAN=<toolchain>/bin/lean \
#   LP=<lake lib path> \
#   ISLAND=/tmp/rulep-island \
#   LEAF_LIST=familyB.idx \
#   RUNG=8192 \
#   bash pipeline/interval/replay_rulep.sh
#
# Cost (guardrule-w1 measurements, 1 lean at a time):
#   * emit: ~65-130 s / leaf (R=8192), ~2-4 s / leaf of that is the base
#     model; the rest is the point path (open arctan at rung R).
#   * kernel: ~? per leaf at R=8192 (see VALIDATION.md); ~4x lower at
#     R=4096, ~16x lower at R=2048 (margins per leaf shrink accordingly).
#   * disk: ~10-20 KB / leaf module; certificate lists fit in RAM.
# ---------------------------------------------------------------------------
set -u

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../.." && pwd)

RUNG=${RUNG:-8192}
LEAF_LIST=${LEAF_LIST:-familyB.idx}
EXPR=${EXPR:-$REPO/lean/Kepler/Interval/Cases/TskXLLIPLSAtan1Base.lean}
CERT=${CERT:-$REPO/certificates/tskajxy/full.cert.json}
OUTDIR=${OUTDIR:-/tmp/rulep-leaves}
LOGDIR=${LOGDIR:-/tmp/rulep-logs}
LEAN=${LEAN:-lean}
LP=${LP:-}
ISLAND=${ISLAND:-}
PY=${PY:-python3}
LOCK=${LOCK:-/tmp/lean_global_lock}

mkdir -p "$OUTDIR" "$LOGDIR"
if [ -n "$ISLAND" ]; then
  LP="$ISLAND:$LP"
fi
if [ ! -f "$CERT" ]; then
  echo "CERT not found: $CERT"
  echo "  set CERT=<path to the 6,512-leaf full.cert.json> (guardcons-w1 artifact)"
  exit 3
fi
if [ ! -f "$LEAF_LIST" ]; then
  echo "LEAF_LIST not found: $LEAF_LIST (1400 family-B leaf indices)"
  exit 3
fi
command -v "$LEAN" >/dev/null 2>&1 || { echo "LEAN not found: $LEAN"; exit 3; }

n=0; ok=0; bad=0
while IFS=$'\t ' read -r idx rest; do
  [ -z "${idx:-}" ] && continue
  case "$idx" in \#*) continue ;; esac
  n=$((n+1))
  tag=$idx
  mod="$OUTDIR/TskXLLIPLSAtan1PLeaf$tag.lean"
  log="$LOGDIR/leaf$tag.log"

  if ! "$PY" -I "$HERE/emit_tm_params.py" \
        --expr "$EXPR" --cert "$CERT" --leaf "$tag" \
        --rule P --rung "$RUNG" \
        --out "$OUTDIR/leaf$tag.params.lean" --module "$mod" \
        > "$log.gen" 2>&1; then
    echo "GENFAIL $tag"; bad=$((bad+1)); continue
  fi

  # one Lean process at a time (global lock; stale after 30 min may be cleared)
  tries=0
  while ! mkdir "$LOCK" 2>/dev/null; do
    tries=$((tries+1))
    if [ "$tries" -gt 90 ]; then
      echo "LOCK TIMEOUT $tag"; bad=$((bad+1)); break
    fi
    sleep 20
  done
  [ "$tries" -gt 90 ] && continue

  /usr/bin/time -l env LEAN_PATH="$LP" nice -n 19 "$LEAN" "$mod" \
      > "$log" 2>&1
  rc=$?
  rmdir "$LOCK"

  ax=$(grep -c "sorryAx" "$log" || true)
  std=$(grep -c "propext, Classical.choice, Quot.sound" "$log" || true)
  wall=$(grep -E "^ *[0-9.]+ real" "$log" | tail -1 | awk '{print $1}')
  rss=$(grep "maximum resident set size" "$log" | tail -1 | awk '{print $1}')
  echo "$tag rc=$rc sorryAx=$ax std3=$std wall=${wall:-?} rssKB=${rss:-?}"
  if [ "$rc" -eq 0 ] && [ "$ax" -eq 0 ]; then ok=$((ok+1)); else bad=$((bad+1)); fi
done < "$LEAF_LIST"

echo "DONE leaves=$n ok=$ok bad=$bad rung=$RUNG"
