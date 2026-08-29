#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch_dir="$(mktemp -d /tmp/gromov-filling-lean-confusable-test.XXXXXX)"
trap 'rm -rf "$scratch_dir"' EXIT

mkdir -p "$scratch_dir/ClassificationOfSurfaces" \
  "$scratch_dir/GromovFilling" "$scratch_dir/SchoenfliesCompat" \
  "$scratch_dir/Wikipedia" "$scratch_dir/scripts"
cp "$repo_dir/scripts/check_lean_unicode_confusables.sh" "$scratch_dir/scripts/"
cp "$repo_dir/GromovFilling.lean" "$scratch_dir/GromovFilling.lean"
printf '%s\n' \
  'def confusableInnerProduct := ⟦0, 0⟧_ℝ' \
  > "$scratch_dir/GromovFilling/UnicodeConfusableTamper.lean"

set +e
(cd "$scratch_dir" && ./scripts/check_lean_unicode_confusables.sh) \
  >"$scratch_dir/negative-control.log" 2>&1
gate_rc=$?
set -e

if [ "$gate_rc" -ne 1 ]; then
  cat "$scratch_dir/negative-control.log" >&2
  echo "Negative control expected exit code 1, got $gate_rc." >&2
  exit 1
fi

grep -F 'GromovFilling/UnicodeConfusableTamper.lean:1:' \
  "$scratch_dir/negative-control.log" >/dev/null
grep -F '⟦' "$scratch_dir/negative-control.log" >/dev/null

echo 'PASS: Unicode-confusable gate rejects an injected look-alike.'
