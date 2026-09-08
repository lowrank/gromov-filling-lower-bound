# Verify the Lean package

The verification command checks the mathematical source, builds every project
module, audits every compiled project declaration, and produces a receipt
for the exact proof and checker files. CI uses the same audit script.

## First-time setup

Use a Linux or macOS machine with Bash, Git, Python 3, network access, and
sufficient memory. Git obtains the source. Python checks the receipt. Install
[elan](https://github.com/leanprover/elan#installation), which selects the Lean
version recorded in `lean-toolchain`. Lean checks the proofs; its build tool,
Lake, obtains the dependencies and builds the package. Mathlib is Lean's
mathematical library. Its downloadable cache avoids rebuilding that dependency
from source.

Full checking is a substantial build. A fresh GitHub runner has taken about
an hour; a project-cache replay has taken about ten minutes. These are examples,
not resource guarantees. Contributors using Dell or Greenwood should run full
verification in GitHub CI or on an approved build host.

## One-command reproduction

```bash
git clone https://github.com/lowrank/gromov-filling-lower-bound.git
cd gromov-filling-lower-bound
./scripts/verify.sh
```

To reproduce the September 7 publication audit, check out its persistent
proof and checker candidate before running the script:

```bash
git fetch origin 57500b07f9a75b73f2e4a27a0a42e3e6a5ecc5f2
git checkout --detach 57500b07f9a75b73f2e4a27a0a42e3e6a5ecc5f2
./scripts/verify.sh
```

The CI receipt names a temporary PR merge commit whose tree is identical to
this candidate; the [publication audit](publication-audit.md) records both
identities. Before the repository is made public, cloning requires
collaborator access.

The result is written to the ignored `.verification/` directory:

| File | Meaning |
|---|---|
| `positive.json` | Every checked declaration and source module, the allowed axioms, and the live audit result. |
| `negative.json` | The separate rejection of the compiled scratch theorem for `sorryAx`. |
| `source-receipt.json` | Source hashes, exact declaration and module inventories, toolchain, dependency revisions, and candidate commit. |
| `audit-tool-build.log` | Build of the pinned audit tool with the project inventory driver. |
| `negative-build.log` | Compilation of the intentionally invalid scratch proof. |

A successful run ends with:

```text
PASS: complete live axiom inventory, compiled negative control, and source receipt.
PASS: complete package build, source gates, live axiom audit, and verified receipt.
```

The revised mathematical library contains 6,762 audited declarations. The
receipt records their names; the count alone is not the verification criterion.

## Equivalent manual steps

```bash
./scripts/check_umbrella.sh
./scripts/check_surface_vendor.sh
./scripts/check_schoenflies_vendor.sh
./scripts/check_no_proof_escapes.sh
./scripts/test_proof_escape_gate.sh
lake exe cache get
lake build
./scripts/audit_axioms.sh
```

The last command builds the pinned audit tool, checks the complete compiled
environment, runs the scratch negative control, creates and verifies the
receipt, and runs 11 receipt mutation tests. To check an existing receipt
against a new live audit, run:

```bash
python3 scripts/verification_receipt.py verify PATH_TO_RECEIPT.json \
  --positive .verification/positive.json \
  --negative .verification/negative.json
```

The verifier rejects changed, missing, or extra bound files, omitted checker
files, changed declaration names, duplicates, missing compiled modules, and
disallowed axioms. Receipt creation requires committed source bytes. The
negative transcript stays separate from the positive evidence.

## What the gates check

1. Every mathematical module appears in the canonical umbrella. The two
   vendored surface-topology closures retain their exact metadata and licenses.
2. Source scans reject proof placeholders, custom axioms, unsafe declarations,
   native reduction, and known Unicode confusables in mathematical sources.
3. The complete package builds with Lean 4.29.0 and the exact dependencies in
   `lake-manifest.json`.
4. The live environment audit records every declaration defined in a project
   module, including private declarations. It accepts only `propext`,
   `Classical.choice`, and `Quot.sound`.
5. A scratch theorem is compiled with an injected proof gap. The same audit
   must reject `GromovFilling.auditTamper` specifically for `sorryAx`.
6. The receipt binds all proof and checker sources, including `lakefile.lean`,
   the inventory driver, verification scripts, and workflow definitions.
   Mutation tests demonstrate that altered evidence is rejected.

The audit uses `leanprover-community/axiom-audit` at
`46024e005996495c65ef609368e11ab39c4222e3`, with the repository's
`scripts/AuditInventory.lean` driver to retain exact names. The collector reads
compiled proof dependencies; it relies on the preceding Lean build for kernel
checking. It is not a separate implementation of Lean's kernel. The audit
tool's environment-loading code is outside the mathematical proof closure.

## CI and a pristine rebuild

Every pull request runs the full Lean verification, the standalone audit-tool
tests, and a strict documentation build. Full checks retain the positive and
negative streams and source receipt as a downloadable verification artifact.
The Pages deployment job is restricted to `main`.

A manual Lean CI run with target `GromovFilling` checks the whole project.
Setting `pristine` to `true` disables restoration of project build artifacts;
the pinned mathlib cache is still restored. A named development module checks
only that module's dependency closure and does not certify the full package.

## Troubleshooting

- If `lake` is missing, finish the elan installation and open a new shell.
- If a download fails, restore network access and rerun the same command.
  Keep the recorded dependency pins.
- If the mathlib cache cannot be obtained, resolve the cache/network problem
  before attempting a large dependency build on a small machine.
- If a process is killed or runs out of memory, use the approved CI or build
  host. A partial run is not a passing receipt.
- If the receipt reports changed sources, use a clean checkout of its named
  commit, or build and audit the changed candidate to obtain new evidence.

## Interpretation

A pass verifies the declared formal scope from the checked source bytes.
It establishes neither a stronger prose statement nor the filling-area
conjecture. The [current manuscript ledger](current-manuscript.md) records
all 18 numbered statements and distinguishes the three complete headline
theorems from broader formulations that remain partial.

The [publication audit](publication-audit.md) links the complete live
inventory, compiled negative control, and source receipt from
[CI 34177156896](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34177156896).
Those evidence files are committed under `verification/publication-20260907/`.

The earlier [Section 4 CI receipt](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34167476132)
records the full build and 6,762-declaration audit for
`bdf0d050ee1d375d7025645c7a2ff22b9a2dd16b`. Its historical JSON receipt is
preserved unchanged. New source receipts use the reproducible verifier above.
