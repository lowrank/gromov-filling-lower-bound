#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

./scripts/check_umbrella.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
lake exe cache get
lake build

echo 'PASS: umbrella, build, and source proof-escape gates.'
echo 'The live environment axiom audit is enforced by GitHub Actions.'
