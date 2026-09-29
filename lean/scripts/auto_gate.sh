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
elif [ "${GATE_MODE:-}" = "DEF-FIX" ]; then
# 2-DF. DEF-FIX mode (approved 2026-09-29, DECISIONS.md "planar 编码定义纠正"):
# definition corrections land only as the faithful application of a
# human-approved charter. The charter's ```diff fences must be FULLY applied
# (charter ⊆ tree, line-multiset); tree lines beyond the charter must each be
# (a) blank/comment/docstring-interior/sorry-bearing/block-move, or (b) inside
# a whitelisted declaration ($DF_NAMES — charter §3a refill set + sanctioned
# statement-touchers). Net new sorries must equal $DF_SORRY_NET (the refill
# debt is the deliverable, charter §4.2-6).
  [ -n "${DF_PATCH:-}" ] || fail "DEF-FIX: DF_PATCH (charter path) not set"
  case "$DF_PATCH" in /*) ;; *) DF_PATCH="$REPO_ROOT/$DF_PATCH" ;; esac
  [ -f "$DF_PATCH" ] || fail "DEF-FIX: charter $DF_PATCH missing"
  for anchor in polytope1.ml:1506 polytope1.ml:2546 sphere.hl:290; do
    grep -qF "$anchor" "$DF_PATCH" \
      || fail "DEF-FIX: charter lacks HOL anchor $anchor"
  done
  psec=$(sed -n '/^### 2.1/,/^### 2.2/p' "$DF_PATCH" \
    | awk '/^```/{ f = !f; next } f')
  [ -n "$psec" ] || fail "DEF-FIX: no diff fences under charter §2.1"
  pdels=$(printf '%s\n' "$psec" | grep -E '^-' || true)
  padds=$(printf '%s\n' "$psec" | grep -E '^[+]' || true)
  # hand-written charter fences vs git-minimal tree diff: a charter -/+ line
  # whose content is IDENTICAL old↔new shows up as unchanged context, not as
  # -/+ — accept charter ⊆ (dels ∪ ctx) / (adds ∪ ctx); truly removed lines
  # can never appear in ctx, so strictness is preserved.
  ctx=$(git diff HEAD -- "$FILE" | grep '^ ' | sort -u || true)
  xb=$(comm -23 <(printf '%s\n' "$pdels" | sort -u) \
                <(cat <(printf '%s\n' "$dels" | sort -u) \
                    <(printf '%s\n' "$ctx" | sed 's/^ /-/') | sort -u))
  [ -z "$xb" ] || fail "DEF-FIX: charter deletion not applied: $(printf '%s' "$xb" | head -2)"
  xb=$(comm -23 <(printf '%s\n' "$padds" | sort -u) \
                <(cat <(printf '%s\n' "$adds" | sort -u) \
                    <(printf '%s\n' "$ctx" | sed 's/^ /+/') | sort -u))
  [ -z "$xb" ] || fail "DEF-FIX: charter addition not applied: $(printf '%s' "$xb" | head -2)"
  # declaration attribution map (name TAB line) for a file content on stdin:
  # enclosing declaration = last start ≤ line; docstring blocks are re-bound
  # to the declaration they precede.
  declmap='
    /^[[:space:]]*((private|protected|noncomputable|unsafe)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|example)[[:space:]]/ {
      l2 = $0
      sub(/^[[:space:]]*((private|protected|noncomputable|unsafe)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|example)[[:space:]]+/, "", l2)
      split(l2, w, /[[:space:](]/)
      if (!(w[1] in seen)) { seen[w[1]] = 1; k++; starts[k] = NR; names[k] = w[1] }
    }
    { lines[NR] = $0
      if (!indoc && $0 ~ /^\/(-!)?/) { indoc = 1 }
      if (indoc && $0 ~ /-\//) { indoc = 0; dclose[++dc] = NR } }
    END {
      j = 0
      for (i = 1; i <= NR; i++) {
        while (j < k && starts[j+1] <= i) j++
        enc[i] = (j >= 1) ? names[j] : "HEADER"
      }
      for (x = 1; x <= dc; x++) {
        c = dclose[x]
        for (m = 1; m <= k; m++) if (starts[m] > c) break
        s = c
        while (s >= 1 && lines[s] !~ /^\/(-!)?/) s--
        for (i = s; i <= c; i++) enc[i] = (m <= k) ? names[m] : "HEADER"
      }
      for (i = 1; i <= NR; i++) print enc[i] "\t" lines[i]
    }'
  [ -n "${DF_NAMES:-}" ] || fail "DEF-FIX: DF_NAMES (whitelisted declarations) not set"
  inlist() {  # name in DF_NAMES (space/comma separated)
    printf '%s\n' " ${DF_NAMES} " | grep -qE "[ ,]${1}[ ,]"
  }
  anyinlist() {  # any enclosing-decl name (one per line) whitelisted?
    local n
    while IFS= read -r n; do
      [ -n "$n" ] || continue
      inlist "$n" && return 0
    done
    return 1
  }
  # NB: identical tactic lines recur across proofs — a body line is excused
  # when ANY of its occurrences sits in a whitelisted declaration.
  xdels=$(comm -23 <(printf '%s\n' "$dels" | sort -u) \
                  <(printf '%s\n' "$pdels" | sort -u) | grep -vE '^-$' || true)
  # docstring interiors are lexically inert (rule ② philosophy): excuse
  # del/add lines sitting inside any /- … -/ block of the OLD file (del side)
  # / CURRENT file (add side) — covers interior rewording whose opener/closer
  # are unchanged context lines.
  dint=$(git show HEAD:"./$FILE" | awk '
    !incmt && /^\/(-!)?/ { incmt = 1; next }
    incmt { print; if ($0 ~ /-\//) incmt = 0; next }' | sort -u)
  cint=$(awk '
    !incmt && /^\/(-!)?/ { incmt = 1; next }
    incmt { print; if ($0 ~ /-\//) incmt = 0; next }' "$FILE" | sort -u)
  headmap=$(git show HEAD:"./$FILE" | awk "$declmap")
  rest=""
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    body="${line#-}"
    if printf '%s\n' "$adds" | grep -qF -- "$body"; then continue; fi
    if printf '%s\n' "$dint" | grep -qF -- "$body"; then continue; fi
    case "$body" in '--'*|'/-'*|*'-/') continue ;; esac
    case "$body" in *sorry*) continue ;; esac
    if printf '%s\n' "$headmap" | awk -F'\t' -v b="$body" '$2 == b { print $1 }' | anyinlist; then continue; fi
    rest+="$line"$'\n'
  done <<EOF3
$xdels
EOF3
  [ -z "$rest" ] || fail "DEF-FIX: deletion outside charter+whitelist: $(printf '%s' "$rest" | head -3)"
  xadds=$(comm -23 <(printf '%s\n' "$adds" | sort -u) \
                  <(printf '%s\n' "$padds" | sort -u) | grep -vE '^[+]$' || true)
  curmap=$(cat "$FILE" | awk "$declmap")
  rest=""
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    body="${line#+}"
    case "$body" in '--'*|'/-'*|*'-/') continue ;; esac
    case "$body" in *'sorry -- DEF-FIX:'*) continue ;; esac
    if printf '%s\n' "$cint" | grep -qF -- "$body"; then continue; fi
    if printf '%s\n' "$curmap" | awk -F'\t' -v b="$body" '$2 == b { print $1 }' | anyinlist; then continue; fi
    rest+="$line"$'\n'
  done <<EOF3
$xadds
EOF3
  # added docstring interiors (e.g. hunk 6 ENCODING NOTES rewording)
  rest=$(printf '%s\n' "$rest" | awk '
    !incmt && /^[+]\/(-!)?/ { incmt = 1; next }
    incmt { if ($0 ~ /^[+]-</ || $0 ~ /-\/[[:space:]]*$/) incmt = 0; next }
    { print }')
  [ -z "$rest" ] || fail "DEF-FIX: addition outside charter+refill markers: $(printf '%s' "$rest" | head -3)"
  [ "$(( $(printf '%s\n' "$adds" | grep -cE '^[+][[:space:]]*sorry\b') - \
          $(printf '%s\n' "$dels" | grep -cE '^-[[:space:]]*sorry\b') ))" \
      -eq "${DF_SORRY_NET:-15}" ] \
    || fail "DEF-FIX: net new sorry != ${DF_SORRY_NET:-15}"
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
# EVOLUTION 10 (2026-09-29): docstring interiors must be collected from the
# HEAD file content (à la DEF-FIX dint), not from diff openers — a rewording
# that keeps the `/-` opener as a context line leaves the deleted block
# opener-less in the diff and the dels-based scan finds nothing (also: strip
# the diff `-` prefix so the consumer's `${line#-}` comparison can match).
# Safety rail kept: a code keyword ends the comment state.
cmt=$(git show HEAD:"./$FILE" | awk '
  !incmt && /^\/(-!)?/ { incmt = 1; next }
  incmt {
    if ($0 ~ /^(theorem|def|lemma|example|instance|abbrev|namespace|end|open|import|set_option|macro|syntax|notation)\b/) { incmt = 0; next }
    print
    if ($0 ~ /-\//) incmt = 0
    next
  }' | sort -u)
if [ -n "$dels" ]; then
  printf '%s\n' "$dels" | grep -qE '^-[[:space:]]*sorry\b|:=[[:space:]]*(by[[:space:]]+)?sorry[[:space:]]*$' \
    || fail "no sorry consumed (theorem untouched?)"
fi
hard=$(printf '%s\n' "$dels" \
  | grep -vE '^-[[:space:]]*sorry\b' \
  | grep -vE '^-$' \
  | grep -vE '^-[[:space:]]*(--|/-)' \
  | grep -vE '^-[[:space:]]*·[[:space:]]*--' \
  | grep -vE '^.*-/[[:space:]]*$' || true)
# anonymous-intro scaffolding (2026-09-29): a deleted `intro _ _ …` placeholder
# carries no information (r1 tactic skeletons) — excused when the fill
# re-introduces the hypotheses (an `intro` line exists among the adds); the
# statement itself stays frozen and rules 3/4/5 still apply to the real content.
if printf '%s\n' "$adds" | grep -qE '^[+][[:space:]]*intro\b'; then
  hard=$(printf '%s\n' "$hard" \
    | grep -vE '^-[[:space:]]*intro([[:space:]]+_[[:space:]]*)+$' || true)
fi
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
if [ "${GATE_MODE:-}" = "DEF-FIX" ]; then
  # DEF-FIX: the net refill debt is charter-specified (§3a/§3b), not forbidden
  [ "$((nsorry_adds - nsorry_dels))" -eq "${DF_SORRY_NET:-15}" ] \
    || fail "DEF-FIX: net new sorry = $((nsorry_adds - nsorry_dels)), expected ${DF_SORRY_NET:-15}"
elif [ "${GATE_MODE:-}" = "STATEMENT-FIX" ]; then
  # STATEMENT-FIX (2026-09-29): skip the line-prefix net-count — the SF
  # multiset equality already pins the sorry surface to the human-approved
  # patch, and the prefix heuristic is blind to def-bodied sorries
  # (`def x … := sorry` deleted vs bare `sorry` lines added reads as +N).
  :
else
  # annotated-scaffold exception (2026-09-29, construction lanes): bare sorry
  # lines may be added as explicit scaffolds up to $NEW_SORRY_ALLOW (default
  # 0), each accounted by a `-- NEEDS` comment among the added lines; beyond
  # the cap, or unaccounted, still fails.
  bare_new=$(printf '%s\n' "$adds" | grep -cE '^[+][[:space:]]*sorry\b[[:space:]]*$' || true)
  needs_docs=$(printf '%s\n' "$adds" | grep -cE -- '-- NEEDS' || true)
  [ "$bare_new" -le "${NEW_SORRY_ALLOW:-0}" ] \
    || fail "bare scaffold sorries added ($bare_new > NEW_SORRY_ALLOW=${NEW_SORRY_ALLOW:-0})"
  if [ "$bare_new" -gt 0 ]; then
    [ "$needs_docs" -ge "$bare_new" ] \
      || fail "scaffold sorries lack -- NEEDS accounting ($needs_docs docs < $bare_new)"
  fi
  other_new=$((nsorry_adds - bare_new))
  [ "$other_new" -le "$nsorry_dels" ] \
    || fail "new sorry lines added ($other_new > $nsorry_dels)"
fi
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
