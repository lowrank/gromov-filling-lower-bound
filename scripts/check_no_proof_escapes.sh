#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

matches="$(mktemp /tmp/gromov-filling-proof-escapes.XXXXXX)"
trap 'rm -f "$matches"' EXIT

pattern='(^|[^[:alnum:]_])(sorry|sorryAx|admit|axiom|unsafe|native_decide)([^[:alnum:]_]|$)'

set +e
LC_ALL=C grep -RInE --include='*.lean' "$pattern" -- \
  ClassificationOfSurfaces GromovFilling SchoenfliesCompat Wikipedia \
  GromovFilling.lean >"$matches"
scan_rc=$?
set -e

case "$scan_rc" in
  0)
    cat "$matches"
    echo 'Lean proof escape or unsafe declaration found.' >&2
    exit 1
    ;;
  1)
    echo 'PASS: no Lean proof escapes or unsafe declarations.'
    ;;
  *)
    cat "$matches" >&2
    echo "Proof-escape scanner failed with exit code $scan_rc." >&2
    exit "$scan_rc"
    ;;
esac

./scripts/check_lean_unicode_confusables.sh

# Comparator audit (Audit/<Claim>/, see Audit/README.md). A challenge states a
# theorem whose proof is `sorry` by design, so Audit/<Claim>/Challenge.lean may
# contain `sorry` and nothing else from the list, and may import only Mathlib
# modules and its claim's Audit/<Claim>/Defs.lean, which imports Mathlib only.
# Every other Audit file, Defs.lean and each Solution.lean included, keeps the
# full rule.
if [ -d Audit ]; then
  challenge_pattern='(^|[^[:alnum:]_])(sorryAx|admit|axiom|unsafe|native_decide)([^[:alnum:]_]|$)'
  audit_failed=0
  if LC_ALL=C grep -RInE --include='*.lean' --exclude='Challenge.lean' "$pattern" -- Audit; then
    audit_failed=1
  fi
  if LC_ALL=C grep -RInE --include='Challenge.lean' "$challenge_pattern" -- Audit; then
    audit_failed=1
  fi
  if LC_ALL=C grep -RInE --include='Challenge.lean' '^import ' -- Audit \
      | LC_ALL=C grep -vE ':import (Mathlib(\.[[:alnum:]_.]+)?|Audit\.[[:alnum:]_]+\.Defs)[[:space:]]*$'; then
    echo 'A comparator challenge may import Mathlib modules and its Defs module only.' >&2
    audit_failed=1
  fi
  if LC_ALL=C grep -RInE --include='Defs.lean' '^import ' -- Audit \
      | LC_ALL=C grep -vE ':import Mathlib(\.[[:alnum:]_.]+)?[[:space:]]*$'; then
    echo 'A comparator Defs module may import Mathlib modules only.' >&2
    audit_failed=1
  fi
  if [ "$audit_failed" -ne 0 ]; then
    echo 'Proof escape in the comparator audit (only Challenge.lean may use sorry).' >&2
    exit 1
  fi
  echo 'PASS: comparator audit uses sorry only in Challenge.lean.'
fi
