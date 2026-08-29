# Verify the Lean package

The public gate checks source coverage, elaboration, proof escapes, and live
axiom provenance. A green build alone is not treated as a complete trust
receipt.

## One-command reproduction

On a machine with sufficient memory and the pinned Lean toolchain available:

```bash
git clone https://github.com/lowrank/conj-gromov-filling.git
cd conj-gromov-filling
./scripts/verify.sh
```

The script runs:

```text
./scripts/check_umbrella.sh
./scripts/check_surface_vendor.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
lake exe cache get
lake build
```

## Continuous integration gates

Every pull request to `main` must pass:

1. **Canonical umbrella check.** Every Gromov Lean source module must appear
   in the generated umbrella import list.
2. **Pinned surface-vendor closure.** Metadata, license, Lean/mathlib target,
   and all 132 modules must match the exact transitive closure of the
   classification entry module.
3. **Fail-closed source escape scan.** Gromov and vendored surface-topology
   Lean files reject placeholder, custom axiom, unsafe, and native reduction
   escape tokens; scanner errors are failures rather than clean results.
4. **Negative control.** A scratch source with an injected `sorry` must be
   rejected with the expected diagnostic and exit code.
5. **Pinned full build.** The complete package elaborates with Lean `4.29.0`
   and the revisions in `lake-manifest.json`.
6. **Live axiom audit.** Every declaration under `GromovFilling` is inspected
   in the compiled environment.

The accepted logical infrastructure is exactly:

```text
propext
Classical.choice
Quot.sound
```

The latest hardened receipt, run
[`33226422322`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33226422322)
on merge commit `ecad55ca15d4bda1f73c59969d7dc9f8809736fa`, audited
4,134 project declarations with no other axioms.

## What a pass means

A pass establishes that the exact checked package builds, exposes every source
module, contains no source-level proof escape, and uses only the declared
logical infrastructure.

It does not establish that a narrower Lean statement matches a stronger prose
claim. That semantic boundary is maintained in the
[statement ledger](formalization.md).

## Resource note

Full Lean replay can require more memory than a workstation safely provides.
Repository contributors should use GitHub CI or a calibrated high-memory host
for full checking rather than bypassing local resource guards.
