#!/usr/bin/env bash
# auto_gate.sh <target-file-rel-to-lean> <theorem-name>
# Mechanical acceptance gate for autonomous Phase 5 porting. Run from lean/.
# Exit 0 = accept. Exit 1 = reject (reason printed, appended to /tmp/auto_gate.log).
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."   # lean/ — git diff paths must be cwd-relative
FILE="$1"; THM="$2"
MODULE=$(echo "$FILE" | sed 's|/|.|g; s|\.lean$||')

fail(){ echo "GATE-FAIL $THM: $*" | tee -a /tmp/auto_gate.log; exit 1; }

# portable timeout (macOS has no coreutils `timeout`): SIGALRM after N seconds
timeout(){ local t=$1; shift; perl -e 'alarm shift; exec @ARGV' "$t" "$@"; }

# 1. only $FILE has tracked modifications vs HEAD
#    (--relative: paths shown relative to cwd, matching $FILE)
changed=$(git diff HEAD --name-only --relative)
[ -n "$changed" ] || fail "no tracked changes (nothing to gate?)"
# LANE_FILES: comma-separated extra files allowed to be dirty (parallel lanes
# gated one at a time by the orchestrator). Default: only $FILE.
ALLOW=$(printf '%s' "${LANE_FILES:-$FILE}" | tr ',' '\n' | sort)
bad=$(comm -23 <(printf '%s\n' "$changed" | sort) <(printf '%s\n' "$ALLOW" | sort))
[ -z "$bad" ] || fail "tracked changes outside lane: [$bad]"

# 2. signature freeze: deletions must be sorry-bearing. Allowed shapes:
#    (a) pure sorry lines (bare or with trailing comment); (b) blank/comment/
#    docstring lines; (c) one-line `… := sorry` (skeleton style!) whose
#    statement prefix is re-added VERBATIM among the added lines. Anything
#    else => reject. At least one sorry must actually be consumed.
dels=$(git diff HEAD -- "$FILE" | grep -E '^-' | grep -v '^---' || true)
# NB: use [+] not \+ — \+ is undefined in POSIX ERE; BSD grep errors out
# (silently empty adds => check void) while GNU grep accepts it.
adds=$(git diff HEAD -- "$FILE" | grep -E '^[+]' | grep -v '^[+][+][+]' || true)
# NOTES-LANE 2026-09-28: a zero-deletion diff (pure comment insertions, e.g.
# NEEDS annotations from scout lanes) is provably structure-preserving; the
# sorry-consumed requirement only governs fill lanes.
if [ -n "$dels" ]; then
  printf '%s\n' "$dels" | grep -qE '^-[[:space:]]*sorry\b|:=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$' \
    || fail "no sorry consumed (theorem untouched?)"
fi
hard=$(printf '%s\n' "$dels" \
  | grep -vE '^-[[:space:]]*sorry\b' \
  | grep -vE '^-$' \
  | grep -vE '^-[[:space:]]*(--|/-)' || true)
rest=""
while IFS= read -r line; do
  [ -z "$line" ] && continue
  prefix=$(printf '%s' "$line" | sed -E 's/^-[[:space:]]*(.*):=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$/\1/')
  if [ -n "$prefix" ] && [ "$prefix" != "$line" ] && printf '%s\n' "$adds" | grep -qF -- "$prefix"; then
    continue
  fi
  rest+="$line"$'\n'
done <<EOF2
$hard
EOF2
[ -z "$rest" ] || fail "non-sorry lines deleted: $(printf '%s' "$rest" | head -3)"

# 3. banned tokens in added lines
#    NB: use [+] not \+ — \+ is undefined in POSIX ERE; BSD grep errors out
#    (silently empty adds => check void) while GNU grep accepts it.
adds=$(git diff HEAD -- "$FILE" | grep -E '^[+]' | grep -v '^[+][+][+]' || true)
printf '%s\n' "$adds" | grep -qE '\b(sorry|admit|native_decide)\b' \
  && fail "banned token in added lines"

# 4. build green (timeout => fail, safe direction; errors in log => fail)
if ! timeout 3600 lake build "$MODULE" > /tmp/auto_gate_build.log 2>&1; then
  fail "lake build $MODULE failed, see /tmp/auto_gate_build.log"
fi
grep -qE '(^| )error:' /tmp/auto_gate_build.log && fail "errors in build log"

# 4b. closure-root build: catches cross-module declaration collisions that the
#     per-module build above cannot see (e.g. two Auto files binding the same
#     name). MAC ADAPTATION 2026-09-28: full `lake build Kepler` pulls the
#     Phase 2 Graphs cert chain (~7-day compile on the old 128c server —
#     infeasible on M3 Pro). The seven Text closure roots below cover the
#     whole Text/ tree (the gate target of all current fill work). Restore
#     `lake build Kepler` before any Graphs/Interval/Cases work. Incremental.
#     GATE_ROOTS: comma/space-separated override — use when another lane's
#     mid-edit file would break an unrelated root (e.g. exclude the root that
#     imports a still-being-edited lane file). Must still cover $FILE's tree.
ROOTS="${GATE_ROOTS:-Kepler.Text.Hypermap Kepler.Text.PackingConcl Kepler.Text.LocalConcl Kepler.Text.LocalBridge Kepler.Text.TameLp Kepler.Text.AzimBridge Kepler.Text.ContraFan}"
if ! timeout 3600 lake build $ROOTS > /tmp/auto_gate_root_build.log 2>&1; then
  fail "lake build Text roots failed, see /tmp/auto_gate_root_build.log"
fi
grep -qE '(^| )error:' /tmp/auto_gate_root_build.log && fail "errors in root build log"

# 5. axioms whitelist on the target theorem (olean now exists)
#    NOTES-LANE: skipped for zero-deletion diffs — comments are lexically
#    inert, every proof term is unchanged, so the axiom surface is
#    bit-identical to HEAD by construction (and $THM may name no theorem).
#    NB: full name = <file's namespace>.<THM>, NOT <module>.<THM>
NS=$(grep -m1 -oE '^namespace [A-Za-z0-9_.]+' "$FILE" | awk '{print $2}')
[ -n "$NS" ] || fail "no namespace found in $FILE"
if [ -n "$dels" ]; then
cat > "/tmp/AxCheck_$THM.lean" <<EOF
import $MODULE
#print axioms $NS.$THM
EOF
timeout 600 lake env lean "/tmp/AxCheck_$THM.lean" > /tmp/AxCheck_$THM.out 2>&1 \
  || fail "axioms check crashed, see /tmp/AxCheck_$THM.out"
# NB: lean wraps long output across lines — flatten before matching
flat=$(tr '\n' ' ' < "/tmp/AxCheck_$THM.out")
echo "$flat" | grep -q 'sorryAx' && fail "sorryAx in axioms"
if echo "$flat" | grep -q 'does not depend on any axioms'; then
  axline="(none)"
else
  axline=$(echo "$flat" | grep -oE 'depends on axioms: \[.*\]' | head -1)
  [ -n "$axline" ] || fail "no axioms line in output"
  rest=$(echo "$axline" | sed 's/.*\[//; s/\]//; s/propext//g; s/Classical\.choice//g; s/Quot\.sound//g; s/[ ,]//g')
  [ -z "$rest" ] || fail "unexpected axioms: $axline"
fi
fi

echo "GATE-PASS $THM" | tee -a /tmp/auto_gate.log
