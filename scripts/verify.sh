#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

./scripts/check_umbrella.sh
lake exe cache get
lake build

if rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b' \
    --glob '*.lean' GromovFilling GromovFilling.lean; then
  echo 'Lean proof escape or unsafe declaration found.' >&2
  exit 1
fi

echo 'PASS: umbrella, build, and source proof-escape gates.'
echo 'The live environment axiom audit is enforced by GitHub Actions.'
