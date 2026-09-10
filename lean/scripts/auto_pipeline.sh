#!/usr/bin/env bash
# auto_pipeline.sh — fully autonomous Phase 5 planarity.hl porting pipeline.
# Runs batch after batch without human intervention:
#   skeleton design (deepseek) -> auto_loop workers (deepseek) -> mechanical
#   batch audit -> ff main -> push -> next batch.
# State persisted in scripts/auto_pipeline_state.txt (committed) so restarts
# are safe. Stops (FAIL-STOP) on: skeleton invalid, loop circuit-breaker,
# audit failure, leftover sorries (NEEDS-HUMAN), or no more theorems.
# Kimi's role: 4-hourly report + STATUS.md + statement-fidelity spot checks.
set -u
cd "$(dirname "$0")/.."   # lean/
export PATH="$HOME/.elan/bin:$PATH"
HL=scripts/planarity.hl
STATE=scripts/auto_pipeline_state.txt
LOG=/tmp/auto_pipeline.log
BATCH_SIZE=10

log(){ echo "[$(date '+%m-%d %H:%M:%S')] $*" | tee -a "$LOG"; }
die(){ log "FAIL-STOP: $*"; exit 1; }

[ -f "$STATE" ] || die "state file $STATE missing (format: <start_line> <batch_no>)"
read -r START BATCH < "$STATE"
git checkout -q wip/auto-phase5 || die "not on wip branch"

while true; do
  # --- pick theorems: next BATCH_SIZE `let ... = prove` landmarks from START ---
  mapfile -t LINES < <(grep -nE '^let .*= *prove' "$HL" | awk -F: -v s="$START" '$1>=s{print $1}')
  [ "${#LINES[@]}" -eq 0 ] && { log "PIPELINE COMPLETE: no more theorems at/after :$START"; exit 0; }
  COUNT=${#LINES[@]}
  [ "$COUNT" -gt "$BATCH_SIZE" ] && COUNT=$BATCH_SIZE
  END=$(wc -l < "$HL")
  if [ "${#LINES[@]}" -gt "$BATCH_SIZE" ]; then END=$(( LINES[BATCH_SIZE] - 1 )); fi
  FIRST=${LINES[0]}
  FILE="Kepler/Text/PlanarityAuto${BATCH}.lean"
  MODULE="Kepler.Text.PlanarityAuto${BATCH}"
  NAMES=$(for l in "${LINES[@]:0:$COUNT}"; do sed -n "${l}s/^let \([A-Za-z0-9_]*\).*/\1/p" "$HL"; done)
  log "=== BATCH $BATCH: :$FIRST-:$END, $COUNT theorems -> $FILE ==="
  log "theorems: $(echo $NAMES)"

  # --- skeleton design by deepseek ---
  LIST=$(for l in "${LINES[@]:0:$COUNT}"; do n=$(sed -n "${l}s/^let \([A-Za-z0-9_]*\).*/\1/p" "$HL"); echo "  :$l $n"; done)
  {
    cat <<EOF
You are working in the lean/ directory of a Lean 4 + Mathlib project
(toolchain via elan; check a file with: export PATH="\$HOME/.elan/bin:\$PATH" && lake env lean <file>).

TASK: Design the SKELETON for Phase 5 porting batch $BATCH. Create exactly ONE
new file: $FILE (do NOT touch any other file). Add Lean 4 statements
(no proofs — every proof is the literal line \`sorry\`) for these HOL Light
theorems from planarity.hl (pasted at bottom):
$LIST
  If a statement is Mathlib-general, check first whether Mathlib already has
  it; if yes, skip it and say so in your report.

FORMAT (a worker pool fills sorries mechanically; the gate is strict):
1. Model the file header/imports/namespace on Kepler/Text/PlanarityConnect.lean
   and Kepler/Text/PlanarityDarts.lean (read with grep -n + sed -n windows
   of at most 100 lines, NEVER whole-file reads of >500 lines).
   \`namespace Kepler.Text\`, every theorem PUBLIC, name = HOL name exactly
   (keep ALL-CAPS names as-is).
2. Directly above each theorem, a \`/-/ ... -/\` docstring with:
   - \`HOL planarity.hl :<start>-<end>\`
   - the VERBATIM HOL statement (between the backticks)
   - 2-5 line proof-approach sketch
   - candidate existing lemmas (grep the repo to confirm, file:line)
3. Statement fidelity is THE priority: quantifier structure, hypotheses,
   conclusion must match HOL exactly in meaning.
4. Every theorem ends with \`:= by\` on the last signature line, then a line
   containing ONLY \`  sorry\` (two-space indent).
5. File MUST compile green with all sorries present:
   \`lake env lean $FILE\` exits 0. Iterate.

HARD RULES:
- Create ONLY $FILE. Never use git. Never \`lake build\` (use
  \`lake env lean\` only). Never leave the repo.
- Missing notions: closest existing encoding + note gap in docstring;
  do NOT invent new definitions.
- Final report: theorem list, fidelity caveats, difficulty ranking.

=== HOL SOURCE (planarity.hl lines $FIRST-$END) ===
EOF
    sed -n "${FIRST},${END}p" "$HL"
  } > /tmp/auto_skel_prompt.txt
  log "dispatch skeleton design (deepseek)"
  timeout 5400 opencode run -m deepseek/deepseek-v4-flash "$(cat /tmp/auto_skel_prompt.txt)" \
    > /tmp/auto_skel_b$BATCH.log 2>&1 || die "skeleton dispatch failed rc=$? (batch $BATCH)"

  # --- validate skeleton ---
  [ -f "$FILE" ] || die "skeleton file $FILE not created"
  SKEL_SORRIES=$(grep -c '^  sorry$' "$FILE")
  [ "$SKEL_SORRIES" -ge 1 ] || die "skeleton has no sorry placeholders"
  if ! lake env lean "$FILE" > /tmp/auto_skel_build.log 2>&1; then
    die "skeleton does not compile (batch $BATCH), see /tmp/auto_skel_build.log"
  fi
  grep -qE 'error' /tmp/auto_skel_build.log && die "skeleton compile errors (batch $BATCH)"
  log "skeleton ok: $SKEL_SORRIES theorems, compiles green"

  # --- import + commit skeleton ---
  LAST_IMP=$(grep -n '^import Kepler.Text.Planarity' Kepler.lean | tail -1 | cut -d: -f1)
  sed -i "${LAST_IMP}a import $MODULE" Kepler.lean
  SKEL_MARK=$(git rev-parse --short HEAD)
  git add "$FILE" Kepler.lean
  git commit -q -m "wip: PlanarityAuto$BATCH skeleton — $SKEL_SORRIES frozen statements (planarity.hl:$FIRST-$END), deepseek-designed (auto_pipeline)" || die "skeleton commit failed"
  git push -q origin wip/auto-phase5
  log "skeleton committed ($SKEL_MARK -> $(git rev-parse --short HEAD))"

  # --- worker loop ---
  log "starting worker loop"
  bash scripts/auto_loop.sh "$FILE" >> /tmp/auto_loop_driver.log 2>&1
  LOOP_RC=$?
  [ "$LOOP_RC" -ne 0 ] && die "auto_loop circuit breaker (batch $BATCH)"
  LEFT=$(grep -c '^  sorry$' "$FILE" || true)
  [ "$LEFT" -eq 0 ] || die "batch $BATCH finished with $LEFT sorries left (NEEDS-HUMAN: $(grep -B1 '^  sorry$' "$FILE" | grep -oE 'theorem [A-Za-z0-9_]+' | tail -1))"

  # --- batch audit (mechanical) ---
  lake build Kepler > /tmp/auto_audit_build.log 2>&1 || die "audit: lake build failed (batch $BATCH)"
  grep -qE '(^| )error:' /tmp/auto_audit_build.log && die "audit: build errors (batch $BATCH)"
  NODEL=$(git diff "$SKEL_MARK"..HEAD -- "$FILE" | grep -E '^-' | grep -v '^---' | grep -vcE '^-[[:space:]]*sorry[[:space:]]*$' || true)
  [ "$NODEL" = "0" ] || die "audit: signature freeze violated (batch $BATCH)"
  {
    echo "import $MODULE"
    grep -oE '^theorem [A-Za-z0-9_]+' "$FILE" | awk '{print "#print axioms Kepler.Text." $2}'
  } > /tmp/AxCheck_auto.lean
  lake env lean /tmp/AxCheck_auto.lean > /tmp/AxCheck_auto.out 2>&1 || die "audit: axioms check crashed"
  tr '\n' ' ' < /tmp/AxCheck_auto.out | grep -q 'sorryAx' && die "audit: sorryAx (batch $BATCH)"
  log "audit green (batch $BATCH)"

  # --- merge to main ---
  git branch -f main wip/auto-phase5
  git push -q origin main wip/auto-phase5 || die "push failed"
  log "MERGED to main: batch $BATCH, coverage :$END"

  # --- advance state ---
  NEWSTART=$(grep -nE '^let .*= *prove' "$HL" | awk -F: -v e="$END" '$1>e{print $1; exit}')
  [ -n "$NEWSTART" ] || { log "PIPELINE COMPLETE: all theorems ported (through :$END)"; exit 0; }
  echo "$NEWSTART $((BATCH+1))" > "$STATE"
  git add "$STATE"
  git commit -q -m "auto_pipeline state: next batch $((BATCH+1)) from :$NEWSTART"
  git push -q origin wip/auto-phase5
  BATCH=$((BATCH+1)); START=$NEWSTART
  sleep 30
done
