#!/usr/bin/env bash
# auto_gate.sh <target-file-rel-to-lean> <theorem-name>
# Mechanical acceptance gate for autonomous Phase 5 porting. Run from lean/.
# Exit 0 = accept. Exit 1 = reject (reason printed, appended to /tmp/auto_gate.log).
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."   # lean/ — git diff paths must be cwd-relative
REPO_ROOT="$(cd .. && pwd)"   # repo root — for repo-level paths (SF_PATCH etc.)
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

# 2-SF. STATEMENT-FIX mode (approved 2026-09-28, DECISIONS.md): statement
# modifications are only legal as the verbatim application of a human-approved
# patch draft archived under docs/statement-fix-proposals-patches/ and cited
# by an item in docs/statement-fix-proposals.md carrying an HOL fidelity
# citation. The working diff must equal the approved patch line-for-line
# (multiset compare — robust to hunk-context drift, strict on content).
# Replaces rule 2 below; rules 1/3/4/4b/5 unchanged (rule 5 then requires the
# FIXED theorem to be sorryAx-free).
if [ "${GATE_MODE:-}" = "STATEMENT-FIX" ]; then
  [ -n "${SF_PATCH:-}" ] || fail "STATEMENT-FIX: SF_PATCH (archived patch path) not set"
  case "$SF_PATCH" in /*) ;; *) SF_PATCH="$REPO_ROOT/$SF_PATCH" ;; esac
  [ -f "$SF_PATCH" ] || fail "STATEMENT-FIX: patch $SF_PATCH missing"
  [ -n "${SF_ITEM:-}" ] || fail "STATEMENT-FIX: SF_ITEM (proposals doc item no.) not set"
  grep -qF "+++ b/lean/$FILE" "$SF_PATCH" \
    || fail "STATEMENT-FIX: patch does not target lean/$FILE"
  sed -n "/^## ${SF_ITEM}\./,/^### /p" "$REPO_ROOT/docs/statement-fix-proposals.md" \
    | grep -q '(a) HOL' \
    || fail "STATEMENT-FIX: item $SF_ITEM lacks (a) HOL citation in proposals doc"
  sec=$(awk -v want="+++ b/lean/$FILE" '
      /^--- a\// { insec = 0 }
      /^\+\+\+ b\// { insec = ($0 == want) ? 1 : 0 }
      insec { print }
    ' "$SF_PATCH")
  [ -n "$sec" ] || fail "STATEMENT-FIX: patch section for lean/$FILE is empty"
  pdels=$(printf '%s\n' "$sec" | grep -E '^-' | grep -v -- '^--- a/' || true)
  padds=$(printf '%s\n' "$sec" | grep -E '^[+]' | grep -v '^[+][+][+]' || true)
  diff <(printf '%s\n' "$dels" | sort) <(printf '%s\n' "$pdels" | sort) > /dev/null \
    || fail "STATEMENT-FIX: deletions differ from approved patch (see $SF_PATCH)"
  diff <(printf '%s\n' "$adds" | sort) <(printf '%s\n' "$padds" | sort) > /dev/null \
    || fail "STATEMENT-FIX: additions differ from approved patch (see $SF_PATCH)"
else
# skeleton-tail pair (2026-09-28): the split-statement skeleton shape is
# `… := by` + next-line `sorry`; a fill may switch to term mode
# (`… :=` + term proof), so the tail line is excused when its deleted
# successor is a bare sorry.
dels=$(printf '%s\n' "$dels" | awk '{
  a[NR] = $0
}
END {
  for (i = 1; i <= NR; i++)
    if (a[i] ~ /:=[[:space:]]*by[[:space:]]*$/ && i < NR && a[i+1] ~ /^-[[:space:]]*sorry[[:space:]]*$/)
      continue
    else
      print a[i]
}')
#    NOTES-LANE 2026-09-28: a zero-deletion diff (pure comment insertions, e.g.
#    NEEDS annotations from scout lanes) is provably structure-preserving; the
#    sorry-consumed requirement only governs fill lanes.
# docstring interior (2026-09-28): lines inside a deleted `/- … -/` block are
# comment text (docstring rewording) — collected into $cmt and excused below.
# Safety rail: an "interior" line starting with a code keyword ends the
# comment state (unclosed-opening poisoning would void the rest of the gate).
cmt=$(printf '%s\n' "$dels" | awk '
  !incmt && /^-\/(-!)?/ { incmt = 1; next }
  incmt {
    if ($0 ~ /^-(theorem|def|lemma|example|instance|abbrev|namespace|end|open|import|set_option|macro|syntax|notation)\b/) { incmt = 0; next }
    print
    if ($0 ~ /-\//) incmt = 0
    next
  }')
if [ -n "$dels" ]; then
  printf '%s\n' "$dels" | grep -qE '^-[[:space:]]*sorry\b|:=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$' \
    || fail "no sorry consumed (theorem untouched?)"
fi
hard=$(printf '%s\n' "$dels" \
  | grep -vE '^-[[:space:]]*sorry\b' \
  | grep -vE '^-$' \
  | grep -vE '^-[[:space:]]*(--|/-)' \
  | grep -vE '^.*-/[[:space:]]*$' || true)
rest=""
while IFS= read -r line; do
  [ -z "$line" ] && continue
  # verbatim re-add (2026-09-28): a line deleted at one position and re-added
  # identically elsewhere = pure block move (forward-reference fixes); the
  # multiset of code lines is preserved, and a duplicate declaration would
  # crash rule 4 anyway.
  if printf '%s\n' "$adds" | grep -qF -- "${line#-}"; then
    continue
  fi
  # docstring interior (see $cmt above): pure comment rewording
  if printf '%s\n' "$cmt" | grep -qF -- "${line#-}"; then
    continue
  fi
  prefix=$(printf '%s' "$line" | sed -E 's/^-[[:space:]]*(.*):=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$/\1/')
  if [ -n "$prefix" ] && [ "$prefix" != "$line" ] && printf '%s\n' "$adds" | grep -qF -- "$prefix"; then
    continue
  fi
  rest+="$line"$'\n'
done <<EOF2
$hard
EOF2
[ -z "$rest" ] || fail "non-sorry lines deleted: $(printf '%s' "$rest" | head -3)"
fi # STATEMENT-FIX else

# 3. banned tokens in added lines. sorry: net-count rule (2026-09-28) — a
#    block move re-adds the same sorry at a new position, so only a NET
#    increase of sorry lines is a violation. admit/native_decide: zero
#    tolerance (Text modules have no scoped exception).
#    NB: use [+] not \+ — \+ is undefined in POSIX ERE; BSD grep errors out
#    (silently empty adds => check void) while GNU grep accepts it.
adds=$(git diff HEAD -- "$FILE" | grep -E '^[+]' | grep -v '^[+][+][+]' || true)
nsorry_dels=$(printf '%s\n' "$dels" | grep -cE '^-[[:space:]]*sorry\b')
nsorry_adds=$(printf '%s\n' "$adds" | grep -cE '^[+][[:space:]]*sorry\b')
[ "$nsorry_adds" -le "$nsorry_dels" ] \
  || fail "new sorry lines added ($nsorry_adds > $nsorry_dels)"
printf '%s\n' "$adds" | grep -qE '\b(admit|native_decide)\b' \
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
# sorryAx PERMITTED (2026-09-28): Text fills may consume other in-tree
# sorries — that debt is tracked by debt_ledger, not by this gate. What this
# gate still catches: any non-standard axiom beyond
# {propext, Classical.choice, Quot.sound, sorryAx} (e.g. ofReduceBool from a
# smuggled native_decide).
flat=$(tr '\n' ' ' < "/tmp/AxCheck_$THM.out")
if echo "$flat" | grep -q 'does not depend on any axioms'; then
  axline="(none)"
else
  axline=$(echo "$flat" | grep -oE 'depends on axioms: \[.*\]' | head -1)
  [ -n "$axline" ] || fail "no axioms line in output"
  rest=$(echo "$axline" | sed 's/.*\[//; s/\]//; s/propext//g; s/Classical\.choice//g; s/Quot\.sound//g; s/sorryAx//g; s/[ ,]//g')
  [ -z "$rest" ] || fail "unexpected axioms: $axline"
fi
fi

echo "GATE-PASS $THM" | tee -a /tmp/auto_gate.log
