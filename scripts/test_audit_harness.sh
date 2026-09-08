#!/usr/bin/env bash
set -euo pipefail

# Exercise the real audit executable and receipt mutations in a tiny standalone
# Lean project. The full-project CI remains the mathematical verification gate.
repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch_dir="$(mktemp -d "${TMPDIR:-/tmp}/gromov-audit-harness.XXXXXX")"
trap 'rm -rf "$scratch_dir"' EXIT
cp -r "$repo_dir/scripts" "$scratch_dir/scripts"
cp "$repo_dir/lean-toolchain" "$scratch_dir/lean-toolchain"
mkdir -p "$scratch_dir/GromovFilling" "$scratch_dir/.github/workflows"
cp "$repo_dir/.github/workflows/"*.yml "$scratch_dir/.github/workflows/"
for directory in ClassificationOfSurfaces Wikipedia SchoenfliesCompat; do
  mkdir -p "$scratch_dir/$directory"
  cp "$repo_dir/$directory/"{VENDOR.json,VENDOR.md,LICENSE} "$scratch_dir/$directory/"
done
printf '%s\n' 'import Lake' 'open Lake DSL' 'package auditFixture' \
  '@[default_target] lean_lib GromovFilling' >"$scratch_dir/lakefile.lean"
printf '%s\n' 'import GromovFilling.Fixture' >"$scratch_dir/GromovFilling.lean"
printf '%s\n' 'namespace GromovFilling' \
  'theorem fixture : (1 : Nat) = 1 := rfl' \
  'theorem secondFixture : (2 : Nat) = 2 := rfl' \
  'end GromovFilling' >"$scratch_dir/GromovFilling/Fixture.lean"
cd "$scratch_dir"
lake update
git init -q
git add -- scripts lean-toolchain lakefile.lean lake-manifest.json GromovFilling.lean \
  GromovFilling ClassificationOfSurfaces Wikipedia SchoenfliesCompat .github/workflows
git -c user.name='Audit fixture' -c user.email='audit@example.invalid' \
  -c core.hooksPath=/dev/null commit -qm 'Freeze disposable audit fixture'
./scripts/audit_axioms.sh
echo 'PASS: audit executable and receipt mutation tests on standalone Lean fixture.'
