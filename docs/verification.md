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
./scripts/check_schoenflies_vendor.sh
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
3. **Pinned Jordan--Schönflies closure.** Metadata, licenses, Lean/mathlib
   target, namespace isolation, minimal imports, and all 134 source plus four
   compatibility modules must match the exact audited closure.
4. **Fail-closed source escape scan.** Gromov and vendored surface-topology
   Lean files reject placeholder, custom axiom, unsafe, and native reduction
   escape tokens; scanner errors are failures rather than clean results.
5. **Negative control.** A scratch source with an injected `sorry` must be
   rejected with the expected diagnostic and exit code.
6. **Pinned full build.** The complete package elaborates with Lean `4.29.0`
   and the revisions in `lake-manifest.json`.
7. **Live axiom audit.** Every declaration under `GromovFilling` is inspected
   in the compiled environment.

The accepted logical infrastructure is exactly:

```text
propext
Classical.choice
Quot.sound
```

The latest hardened merged-main receipt, run
[`33504856733`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33504856733)
on exact merge `f35f06688c7b8d208b526d8a7196c6a2e2baaf2e`, completed
all 3,769 full-build jobs and audited 6,677 project declarations with no other
axioms. The endpoint-specific `#print axioms` output for Theorem 1.1, the
strict Theorem 1.2 bound, and the all-parameter nonlinear theorem reports the
same exact allowlist.

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
