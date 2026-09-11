#!/usr/bin/env bash
# auto_loop.sh <target-file-rel-to-lean>
# Autonomous Phase 5 porting loop. Run from lean/ on the wip branch.
# Picks the first theorem in $FILE still carrying a bare `  sorry` line,
# dispatches a worker (big-pickle; 3rd attempt escalates to glm-5.3),
# runs auto_gate.sh, commits on pass, resets+retries on fail.
# A theorem failing 3 attempts is skipped (NEEDS-HUMAN) — 3 consecutive
# skips trip the circuit breaker and stop the loop for human review.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
FILE="$1"
STATE=${LOOPLOG:-/tmp/auto_loop.log}
SKIPS=${LOOPSKIPS:-/tmp/auto_loop_skips.txt}
declare -A FAILS
touch "$SKIPS"
consec_skip=0

log(){ echo "[$(date '+%H:%M:%S')] $*" | tee -a "$STATE"; }

pending_theorems(){
  awk '
    /^theorem /{ if (name != "" && pend) print name; name=$2; pend=0 }
    /^  sorry[[:space:]]*$/ { pend=1 }
    END{ if (name != "" && pend) print name }
  ' "$FILE" | grep -vxF -f "$SKIPS"
}

gen_prompt(){
  local thm="$1"
  cat <<EOF
You are working in the lean/ directory of a Lean 4 + Mathlib project
(toolchain via elan; check a file with: export PATH="\$HOME/.elan/bin:\$PATH" && lake env lean <file>).

TASK: Fill in the proof of theorem \`$thm\` in file $FILE.
The theorem statement is FINAL — it was transcribed from the HOL Light
original and is frozen. Directly above it sits a docstring containing the
verbatim HOL source (with planarity.hl line numbers), a proof-approach
sketch, and candidate existing lemmas. The single line \`sorry\` below the
statement is your work area.

Context:
- 3D type is Kepler.Geom.V3; \`open Kepler.Geom\` is already in effect where needed.
- Existing layers: Kepler/Geom/{Azim,AzimLemmas,Aff,Coplanar}.lean,
  Kepler/Text/{Hypermap,Fan,TopologyFan,Planarity,PlanarityNotCut}.lean —
  grep for lemmas before reproving anything.
- HOL original (for reference): lean/scripts/planarity.hl inside this repo.

HARD RULES:
1. Modify ONLY $FILE. Replace ONLY the sorry line of \`$thm\` (you may add
   private helper lemmas immediately above it). NEVER edit any statement or
   signature line, NEVER touch other theorems or their sorries. Never use
   git. Never read or write anything outside this repository.
2. Zero sorry/admit/native_decide in what you add. Do not even write these
   words in comments.
3. Locate with grep -n; read with sed -n 'A,Bp' windows of at most 100
   lines. NEVER read a file >500 lines whole (kills the session).
4. Start writing code within 10 minutes of starting.
5. Iterate \`lake env lean $FILE\` until it exits 0 with no errors.
6. If truly stuck after ~25 minutes of real attempts: restore the sorry
   line exactly as it was and say so in your final report. Honest bail-out
   is acceptable; fake or weakened statements are not.
7. Final report: what was proved, compile iterations, remaining issues.
EOF
}

log "=== auto_loop start on $FILE ==="
while true; do
  THM=$(pending_theorems | head -1)
  if [ -z "$THM" ]; then
    log "ALL DONE (or all remaining skipped). pending left: $(pending_theorems | wc -l)"
    break
  fi
  n=${FAILS[$THM]:-0}
  if [ "$n" -ge 3 ]; then
    echo "$THM" >> "$SKIPS"
    consec_skip=$((consec_skip+1))
    log "SKIP $THM after $n failed attempts (NEEDS-HUMAN)"
    if [ "$consec_skip" -ge 3 ]; then
      log "CIRCUIT BREAKER: 3 consecutive skips, stopping for human review"
      exit 1
    fi
    continue
  fi
  # 2026-09-10 用户定：worker 全用 deepseek-v4-flash（更快更便宜，真产试车双杀）；
  # 满血 glm-5.3 留作最后兜底
  if [ "$n" -ge 2 ]; then MODEL="zhipuai-coding-plan/glm-5.3"; else MODEL="deepseek/deepseek-v4-flash"; fi
  gen_prompt "$THM" > "/tmp/auto_prompt_$THM.txt"
  log "DISPATCH $THM (attempt $((n+1)), model $MODEL)"
  timeout 5400 opencode run -m "$MODEL" "$(cat /tmp/auto_prompt_$THM.txt)" \
    > "/tmp/auto_$THM.log" 2>&1
  rc=$?
  log "WORKER-EXIT $THM rc=$rc"
  if bash scripts/auto_gate.sh "$FILE" "$THM"; then
    git add "$FILE"
    git commit -q -m "phase5 auto: $THM (big-pickle/${MODEL##*/}); gate green (build+axioms+signature-freeze)" \
      && log "COMMIT $THM accepted"
    consec_skip=0
    sleep 45
  else
    git checkout -- "$FILE"
    FAILS[$THM]=$((n+1))
    log "REJECT $THM (attempt $((n+1))) — file reset"
    sleep 120
  fi
done
log "=== auto_loop finished ==="
