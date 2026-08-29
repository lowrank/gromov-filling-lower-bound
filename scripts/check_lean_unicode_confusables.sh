#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

matches="$(mktemp /tmp/gromov-filling-lean-confusables.XXXXXX)"
trap 'rm -f "$matches"' EXIT

# These characters have each appeared as a visually plausible typo for the
# project notation shown on the right:
#   ⟦ ⟧  ->  ⟪ ⟫   (real inner product)
#   𝓈    ->  𝓘     (model with corners)
#   𝑍    ->  𝓝     (neighbourhood filter)
pattern='⟦|⟧|𝓈|𝑍'

set +e
grep -RInE --include='*.lean' "$pattern" -- \
  ClassificationOfSurfaces GromovFilling SchoenfliesCompat Wikipedia \
  GromovFilling.lean >"$matches"
scan_rc=$?
set -e

case "$scan_rc" in
  0)
    cat "$matches"
    echo 'Known Lean Unicode confusable found.' >&2
    exit 1
    ;;
  1)
    echo 'PASS: no known Lean Unicode confusables.'
    ;;
  *)
    cat "$matches" >&2
    echo "Unicode-confusable scanner failed with exit code $scan_rc." >&2
    exit "$scan_rc"
    ;;
esac
