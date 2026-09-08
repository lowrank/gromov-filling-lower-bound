#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

./scripts/check_umbrella.sh
./scripts/check_surface_vendor.sh
./scripts/check_schoenflies_vendor.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
lake exe cache get
lake build
./scripts/audit_axioms.sh

echo 'PASS: complete package build, source gates, live axiom audit, and verified receipt.'
