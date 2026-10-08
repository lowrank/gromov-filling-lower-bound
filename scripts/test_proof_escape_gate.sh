#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch_dir="$(mktemp -d /tmp/gromov-filling-proof-escape-test.XXXXXX)"
trap 'rm -rf "$scratch_dir"' EXIT

mkdir -p "$scratch_dir/ClassificationOfSurfaces" \
  "$scratch_dir/GromovFilling" "$scratch_dir/SchoenfliesCompat" \
  "$scratch_dir/Wikipedia" "$scratch_dir/scripts"
cp "$repo_dir/scripts/check_no_proof_escapes.sh" "$scratch_dir/scripts/"
cp "$repo_dir/scripts/check_lean_unicode_confusables.sh" "$scratch_dir/scripts/"
cp "$repo_dir/GromovFilling.lean" "$scratch_dir/GromovFilling.lean"
printf '%s\n' \
  'theorem proofEscapeTamper : True := by' \
  '  sorry' \
  > "$scratch_dir/GromovFilling/ProofEscapeTamper.lean"

set +e
(cd "$scratch_dir" && ./scripts/check_no_proof_escapes.sh) \
  >"$scratch_dir/negative-control.log" 2>&1
gate_rc=$?
set -e

if [ "$gate_rc" -ne 1 ]; then
  cat "$scratch_dir/negative-control.log" >&2
  echo "Negative control expected exit code 1, got $gate_rc." >&2
  exit 1
fi

grep -F 'GromovFilling/ProofEscapeTamper.lean:2:' \
  "$scratch_dir/negative-control.log" >/dev/null
grep -F 'sorry' "$scratch_dir/negative-control.log" >/dev/null

# Comparator audit: a Challenge may use `sorry` (positive control); a Solution
# may not, a Challenge may use no other escape, and may import Mathlib only.
rm "$scratch_dir/GromovFilling/ProofEscapeTamper.lean"
mkdir -p "$scratch_dir/Audit/Claim"
printf '%s\n' 'import Mathlib.Logic.Basic' 'def d : Nat := 0' \
  > "$scratch_dir/Audit/Claim/Defs.lean"
printf '%s\n' 'import Mathlib.Logic.Basic' 'import Audit.Claim.Defs' \
  'theorem t : True := by' '  sorry' \
  > "$scratch_dir/Audit/Claim/Challenge.lean"
printf '%s\n' 'import Mathlib.Logic.Basic' 'theorem t : True := trivial' \
  > "$scratch_dir/Audit/Claim/Solution.lean"
(cd "$scratch_dir" && ./scripts/check_no_proof_escapes.sh) \
  >"$scratch_dir/audit-positive.log" 2>&1 || {
  cat "$scratch_dir/audit-positive.log" >&2
  echo 'Positive control: a Challenge sorry alone must pass.' >&2
  exit 1
}

audit_case() {  # description, file, content...
  local what="$1" file="$2"; shift 2
  local saved; saved="$(cat "$scratch_dir/$file")"
  printf '%s\n' "$@" > "$scratch_dir/$file"
  set +e
  (cd "$scratch_dir" && ./scripts/check_no_proof_escapes.sh) \
    >"$scratch_dir/audit-negative.log" 2>&1
  local rc=$?
  set -e
  printf '%s\n' "$saved" > "$scratch_dir/$file"
  if [ "$rc" -ne 1 ]; then
    cat "$scratch_dir/audit-negative.log" >&2
    echo "Negative control ($what) expected exit code 1, got $rc." >&2
    exit 1
  fi
}
audit_case 'sorry in a Solution' Audit/Claim/Solution.lean \
  'import Mathlib.Logic.Basic' 'theorem t : True := by' '  sorry'
audit_case 'admit in a Challenge' Audit/Claim/Challenge.lean \
  'import Mathlib.Logic.Basic' 'theorem t : True := by' '  admit'
audit_case 'non-Mathlib import in a Challenge' Audit/Claim/Challenge.lean \
  'import GromovFilling' 'theorem t : True := by' '  sorry'
audit_case 'non-Mathlib import in Defs' Audit/Claim/Defs.lean \
  'import GromovFilling' 'def d : Nat := 0'
audit_case 'sorry in Defs' Audit/Claim/Defs.lean \
  'import Mathlib.Logic.Basic' 'def d : Nat := sorry'

"$repo_dir/scripts/test_lean_unicode_confusable_gate.sh"

echo 'PASS: proof-escape gate rejects an injected sorry, and holds the comparator audit to its scoped rule.'
