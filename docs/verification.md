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
lake exe mk_all --check
lake exe cache get
lake build
rg -n "proof escape tokens" GromovFilling GromovFilling.lean
```

## Continuous integration gates

Every pull request to `main` must pass:

1. **Canonical umbrella check.** Every Lean source module must appear in the
   generated umbrella import list.
2. **Pinned full build.** The complete package elaborates with Lean `4.29.0`
   and the revisions in `lake-manifest.json`.
3. **Source escape scan.** Project Lean files reject placeholder, custom axiom,
   unsafe, and native reduction escape tokens.
4. **Live axiom audit.** Every declaration under `GromovFilling` is inspected
   in the compiled environment.

The accepted logical infrastructure is exactly:

```text
propext
Classical.choice
Quot.sound
```

The first hardened receipt audited 3,965 project declarations with no other
axioms.

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

