#!/usr/bin/env bash
# auto_pipeline_conforming.sh — autonomous Phase 5 Conforming.hl porting pipeline.
#
# Like auto_pipeline.sh but for Conforming.hl, and with two differences:
#   1. It does NOT merge to main. Conforming depends (transitively) on the
#      still-unproven `solid_of_dartset_leads_into_fan_triangle_fan`, so main
#      must stay sorry-free. Batches are committed/pushed to wip/auto-phase5
#      only; a later session merges once the volume chain closes.
#   2. A theorem that exhausts 3 worker attempts is treated as BLOCKED and its
#      leftover `sorry` is tolerated (audit excludes it). The known blocked
#      theorems are exactly those depending on solid_of (DWFBRQY and its sole
#      consumer). Everything else must close.
#
# State persisted in scripts/auto_pipeline_conforming_state.txt.
set -u
cd "$(dirname "$0")/.."   # lean/
export PATH="$HOME/.elan/bin:$PATH"
HL=scripts/conforming.hl
STATE=scripts/auto_pipeline_conforming_state.txt
LOG=/tmp/auto_pipeline_conforming.log
BATCH_SIZE=10
# known-blocked theorems (may legitimately keep `sorry`); other skipped
# theorems are still tolerated but reported.
BLOCKED="DWFBRQY nonconformin_fan_imp_n_fan_ge0"
export LOOPSKIPS=/tmp/auto_loop_conforming_skips.txt
export LOOPLOG=/tmp/auto_loop_conforming.log
LOOPDRIVER=/tmp/auto_loop_conforming_driver.log

log(){ echo "[$(date '+%m-%d %H:%M:%S')] $*" | tee -a "$LOG"; }
die(){ log "FAIL-STOP: $*"; exit 1; }

[ -f "$STATE" ] || die "state file $STATE missing (format: <start_line> <batch_no>)"
read -r START BATCH < "$STATE"
git checkout -q wip/auto-phase5 || die "not on wip branch"
touch "$LOOPSKIPS"

while true; do
  mapfile -t LINES < <(grep -nE '^let .*= *prove' "$HL" | awk -F: -v s="$START" '$1>=s{print $1}')
  [ "${#LINES[@]}" -eq 0 ] && { log "PIPELINE COMPLETE: no more theorems at/after :$START"; exit 0; }
  COUNT=${#LINES[@]}
  [ "$COUNT" -gt "$BATCH_SIZE" ] && COUNT=$BATCH_SIZE
  END=$(wc -l < "$HL")
  if [ "${#LINES[@]}" -gt "$BATCH_SIZE" ]; then END=$(( LINES[BATCH_SIZE] - 1 )); fi
  FIRST=${LINES[0]}
  FILE="Kepler/Text/ConformingAuto${BATCH}.lean"
  MODULE="Kepler.Text.ConformingAuto${BATCH}"
  NAMES=$(for l in "${LINES[@]:0:$COUNT}"; do sed -n "${l}s/^let \([A-Za-z0-9_]*\).*/\1/p" "$HL"; done)
  log "=== BATCH $BATCH: :$FIRST-:$END, $COUNT theorems -> $FILE ==="
  log "theorems: $(echo $NAMES)"

  # --- skeleton design (deepseek) ---
  LIST=$(for l in "${LINES[@]:0:$COUNT}"; do n=$(sed -n "${l}s/^let \([A-Za-z0-9_]*\).*/\1/p" "$HL"); echo "  :$l $n"; done)
  {
    cat <<EOF
You are working in the lean/ directory of a Lean 4 + Mathlib project
(toolchain via elan; check a file with: export PATH="\$HOME/.elan/bin:\$PATH" && lake env lean <file>).

TASK: Design the SKELETON for Phase 5 porting batch $BATCH of the HOL Light
Flyspeck file Conforming.hl. Create exactly ONE new file: $FILE (do NOT touch
any other file). Add Lean 4 statements (no proofs — every proof is the literal
line \`sorry\`) for these HOL Light theorems from Conforming.hl (pasted below):
$LIST
  If a statement is Mathlib-general, check first whether Mathlib already has
  it; if yes, skip it and say so in your report.

AVAILABLE API (grep to confirm; use these, do NOT invent definitions):
- Import at the top: \`import Kepler.Text.PlanarityAuto16\` and
  \`import Kepler.Text.ConformingDefs\` (both already exist and compile).
- \`Kepler/Text/ConformingDefs.lean\` defines (namespace Kepler.Text):
  \`f1Fan\`, \`conformingBijectionFan\`, \`conformingHalfSpaceFan\`,
  \`conformingSolidAngleFan\`, \`conformingDiagonalFan\`, \`conformingFan\`,
  \`nFan\`, \`minimallyNonconformingFan\`. NOTE: these take an extra explicit
  \`(hfan : FAN x V E)\` argument (because \`hypermapOfFan\` needs it); pass the
  theorem's \`hfan\` hypothesis through.
- \`Kepler.Geom.Volume\` (via ConformingDefs): \`radialNorm\`, \`EventuallyRadial\`,
  \`sol\`, \`sol_spec\`. HOL \`sol x C\` ↔ \`Kepler.Geom.sol x C\`.
- Existing planarity/fan API: \`FAN\`, \`fan80\`, \`setOfEdge\`, \`dartOfFan\`,
  \`topologicalComponentYfan\`, \`dartsetLeadsIntoFan\`, \`dartLeadsInto\`,
  \`sigmaFan\`, \`azimFan\`, \`affGt\`, \`Collinear3\`, \`hypermapOfFan\` (.faceSet).
- HOL quadruple darts ↔ \`V3 × V3\`; \`pr2 y\`/\`pr3 y\` ↔ \`y.1\`/\`y.2\`.
  \`INTERS {g y | y IN f}\` ↔ \`⋂ y ∈ f, g y\`; \`sum (f) g\` ↔ \`∑ᶠ y ∈ f, g y\`;
  \`CARD f\` ↔ \`f.ncard\`; \`nsum S g\` ↔ \`∑ᶠ f ∈ S, g f\`.
- Theorem \`solid_of_dartset_leads_into_fan_triangle_fan\` lives in
  \`Kepler.Text.PlanarityAuto16\` (currently a sanctioned sorry). A few
  theorems here (notably \`DWFBRQY\`) legitimately need it; write the statement
  faithfully anyway — it will be left as a known-blocked sorry.

FORMAT (a worker pool fills sorries mechanically; the gate is strict):
1. Model the file header/imports/namespace on Kepler/Text/PlanarityAuto15.lean
   and Kepler/Text/PlanarityComponent.lean (read with grep -n + sed -n windows
   of at most 100 lines, NEVER whole-file reads of >500 lines).
   \`namespace Kepler.Text\`, every theorem PUBLIC, name = HOL name exactly
   (keep ALL-CAPS names as-is).
2. Directly above each theorem, a \`/-/ ... -/\` docstring with:
   - \`HOL Conforming.hl :<start>-<end>\`
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

=== HOL SOURCE (Conforming.hl lines $FIRST-$END) ===
EOF
    sed -n "${FIRST},${END}p" "$HL"
  } > /tmp/auto_skel_conforming_prompt.txt
  log "dispatch skeleton design (deepseek)"
  timeout 5400 opencode run -m deepseek/deepseek-v4-flash "$(cat /tmp/auto_skel_conforming_prompt.txt)" \
    > /tmp/auto_skel_conforming_b$BATCH.log 2>&1 || die "skeleton dispatch failed rc=$? (batch $BATCH)"

  [ -f "$FILE" ] || die "skeleton file $FILE not created"
  SKEL_SORRIES=$(grep -c '^  sorry$' "$FILE")
  [ "$SKEL_SORRIES" -ge 1 ] || die "skeleton has no sorry placeholders"
  if ! lake env lean "$FILE" > /tmp/auto_skel_conforming_build.log 2>&1; then
    die "skeleton does not compile (batch $BATCH), see /tmp/auto_skel_conforming_build.log"
  fi
  grep -qE 'error' /tmp/auto_skel_conforming_build.log && die "skeleton compile errors (batch $BATCH)"
  log "skeleton ok: $SKEL_SORRIES theorems, compiles green"

  LAST_IMP=$(grep -n '^import Kepler.Text.Conforming' Kepler.lean | tail -1 | cut -d: -f1)
  [ -n "$LAST_IMP" ] || LAST_IMP=$(grep -n '^import Kepler.Text.PlanarityAuto16' Kepler.lean | tail -1 | cut -d: -f1)
  sed -i "${LAST_IMP}a import $MODULE" Kepler.lean
  SKEL_MARK=$(git rev-parse --short HEAD)
  git add "$FILE" Kepler.lean
  git commit -q -m "wip: ConformingAuto$BATCH skeleton — $SKEL_SORRIES frozen statements (Conforming.hl:$FIRST-$END), deepseek-designed" || die "skeleton commit failed"
  git push -q origin wip/auto-phase5
  log "skeleton committed ($SKEL_MARK -> $(git rev-parse --short HEAD))"

  bash scripts/auto_loop.sh "$FILE" >> "$LOOPDRIVER" 2>&1
  LOOP_RC=$?
  [ "$LOOP_RC" -ne 0 ] && die "auto_loop circuit breaker (batch $BATCH)"

  # --- audit: tolerate skipped/blocked sorries, forbid others ---
  lake build Kepler > /tmp/auto_audit_conforming_build.log 2>&1 || die "audit: lake build failed (batch $BATCH)"
  grep -qE '(^| )error:' /tmp/auto_audit_conforming_build.log && die "audit: build errors (batch $BATCH)"
  NODEL=$(git diff "$SKEL_MARK"..HEAD -- "$FILE" | grep -E '^-' | grep -v '^---' | grep -vcE '^-[[:space:]]*sorry[[:space:]]*$' || true)
  [ "$NODEL" = "0" ] || die "audit: signature freeze violated (batch $BATCH)"

  # theorems still carrying a bare sorry
  mapfile -t LEFTOVER < <(awk '/^theorem /{name=$2} /^  sorry[[:space:]]*$/{print name}' "$FILE")
  for t in "${LEFTOVER[@]:-}"; do
    [ -z "$t" ] && continue
    if grep -qxF "$t" "$LOOPSKIPS"; then
      log "  BLOCKED (skipped after retries): $t"
    else
      die "batch $BATCH leftover sorry on non-skipped theorem: $t"
    fi
  done

  # axioms: check every theorem WITHOUT a sorry
  {
    echo "import $MODULE"
    awk '
      function flush() { if (name != "" && !has) print "#print axioms Kepler.Text." name }
      /^theorem / { flush(); name=$2; has=0; next }
      /^  sorry[[:space:]]*$/ { has=1 }
      END { flush() }
    ' "$FILE"
  } > /tmp/AxCheck_conforming.lean
  lake env lean /tmp/AxCheck_conforming.lean > /tmp/AxCheck_conforming.out 2>&1 || die "audit: axioms check crashed"
  tr '\n' ' ' < /tmp/AxCheck_conforming.out | grep -q 'sorryAx' && die "audit: sorryAx in a non-blocked theorem (batch $BATCH)"
  log "audit green (batch $BATCH): ${#LEFTOVER[@]} blocked, rest clean"

  # --- NO merge to main (Conforming is on wip until the volume chain closes) ---
  git push -q origin wip/auto-phase5 || die "push failed"
  log "batch $BATCH committed to wip (coverage :$END); main NOT updated"

  NEWSTART=$(grep -nE '^let .*= *prove' "$HL" | awk -F: -v e="$END" '$1>e{print $1; exit}')
  [ -n "$NEWSTART" ] || { log "PIPELINE COMPLETE: all Conforming theorems ported (through :$END)"; exit 0; }
  echo "$NEWSTART $((BATCH+1))" > "$STATE"
  git add "$STATE"
  git commit -q -m "auto_pipeline_conforming state: next batch $((BATCH+1)) from :$NEWSTART"
  git push -q origin wip/auto-phase5
  BATCH=$((BATCH+1)); START=$NEWSTART
  sleep 30
done
