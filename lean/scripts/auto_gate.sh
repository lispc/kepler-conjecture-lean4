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

# 1. only $FILE has tracked modifications vs HEAD
#    (--relative: paths shown relative to cwd, matching $FILE)
changed=$(git diff HEAD --name-only --relative)
[ "$changed" = "$FILE" ] || fail "tracked changes: [$changed] (expected only $FILE)"

# 2. signature freeze: every deleted line must be a bare sorry line,
#    and at least one sorry must actually be consumed
dels=$(git diff HEAD -- "$FILE" | grep -E '^-' | grep -v '^---' || true)
printf '%s\n' "$dels" | grep -qE '^-[[:space:]]*sorry[[:space:]]*$' \
  || fail "no sorry consumed (theorem untouched?)"
bad=$(printf '%s\n' "$dels" | grep -vE '^-[[:space:]]*sorry[[:space:]]*$' || true)
[ -z "$bad" ] || fail "non-sorry lines deleted: $(printf '%s' "$bad" | head -3)"

# 3. banned tokens in added lines
adds=$(git diff HEAD -- "$FILE" | grep -E '^\+' | grep -v '^\+\+\+' || true)
printf '%s\n' "$adds" | grep -qE '\b(sorry|admit|native_decide)\b' \
  && fail "banned token in added lines"

# 4. build green (timeout => fail, safe direction; errors in log => fail)
if ! timeout 3600 lake build "$MODULE" > /tmp/auto_gate_build.log 2>&1; then
  fail "lake build $MODULE failed, see /tmp/auto_gate_build.log"
fi
grep -qE '(^| )error:' /tmp/auto_gate_build.log && fail "errors in build log"

# 5. axioms whitelist on the target theorem (olean now exists)
#    NB: full name = <file's namespace>.<THM>, NOT <module>.<THM>
NS=$(grep -m1 -oE '^namespace [A-Za-z0-9_.]+' "$FILE" | awk '{print $2}')
[ -n "$NS" ] || fail "no namespace found in $FILE"
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

echo "GATE-PASS $THM" | tee -a /tmp/auto_gate.log
