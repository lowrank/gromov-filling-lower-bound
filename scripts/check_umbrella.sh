#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

expected_imports="$(mktemp /tmp/gromov-filling-imports.XXXXXX)"
trap 'rm -f "$expected_imports"' EXIT

find GromovFilling -type f -name '*.lean' -print \
  | LC_ALL=C sort \
  | sed 's#/#.#g; s#\.lean$##; s#^#import #' \
  > "$expected_imports"

diff -u "$expected_imports" GromovFilling.lean
echo 'PASS: GromovFilling.lean imports every project module in canonical order.'
