# Publication audit — September 7, 2026

The Lean verification passed for the declared formal scope of `main2.tex`,
including Theorems 1.1, 1.2, and 4.1 and the strict lower bound `5.40154`.
The [current manuscript ledger](current-manuscript.md) records all 18 numbered
statements and 22 numbered equations. Nine statements are fully formalized;
nine broader intermediate statements remain partial. Those partial statements
are not unproved premises of the three headline proofs.

At the time of this audit, the repository remained private and the changes
were in [PR #157](https://github.com/lowrank/gromov-filling-lower-bound/pull/157).
Publication still required review and merge of that PR and a decision about
the historical manuscript described below.

## Source identity

The authors' mathematical snapshot is `main2.tex` at Overleaf commit
`85c9eb955a7ae04c8d799def3ac8e68fa70028e9`. The current version,
`3c37718a4bd21de0e283fda7ebf39ce81e42e8a0`, changes the formalization paragraph;
all 18 numbered statements and 22 numbered equations are byte-identical.
The ledger retains their source text, numbers, pages, and exact headline Lean
types. It also records the circle normalization and the relationship between
Theorem 4.1 and its numerical specialization.

The proof and checker candidate is
`57500b07f9a75b73f2e4a27a0a42e3e6a5ecc5f2`. GitHub checked the PR merge
object `f85f25c689ccba13d6fba99d364d5850f5b89ff3`; both have tree
`fb10ee160957d88fab1dfbf4f50e560cefd84001`. The committed
[CI evidence](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/verification/publication-20260907/ci-evidence.json)
records that equality and the hashes of the separate positive, negative, and
source-receipt files.

All 445 preexisting mathematical Lean and Lake-configuration hashes are
unchanged from the earlier Section 4 receipt. The manuscript's immutable
formalization link therefore still names the same mathematical sources.
This audit changes verification tooling, coverage records, and documentation.

## Executed checks

| Check | Result and evidence |
|---|---|
| Full package, live audit, and receipt at the new candidate | [CI 34177156896](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34177156896) passed; project cache restored, full Lake build and live audit rerun. |
| Pristine mathematical-source build | [CI 34172818364](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34172818364) passed at `bf67cd01abc1003c00da2145fc26c7a322c1b43f`, with no project cache restored. Its 445 Lean/Lake source hashes match the new candidate. This older job does not certify the revised checker. |
| Standalone audit-tool fixture | [CI 34177156844](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34177156844) passed with two distinct fixture declarations and the real compiled negative control. |
| Strict documentation build | [CI 34177156856](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34177156856) passed. |
| Pages permissions and deployment guard | [CI 34177153135](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34177153135) built and uploaded the site; deployment was skipped on the feature branch. |

The live audit records **6,762 distinct declarations from 174 project modules**.
Its only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or custom axioms in the mathematical sources,
and no `sorryAx` in the audited proof dependencies. The source receipt binds
474 files, including the proof sources, dependency pins, audit driver,
verification scripts, workflows, and vendor notices.

The same executable rejected a separately compiled scratch theorem,
`GromovFilling.auditTamper`, for `sorryAx`. The accepted inventory and this
negative result are retained in separate files. All 11 receipt mutation tests
were rejected, including changed or omitted files, altered declaration names,
duplicates, a missing module, and a disallowed axiom. See
[reproduction instructions](verification.md).

The first fixture run, [34174245638](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34174245638),
failed because its scratch-copy setup omitted a required checker directory.
The repaired successor passed. Two superseded full runs were canceled before
completion; they are not mathematical failures or passing evidence.

Lean's build performs kernel checking; the pinned audit collector inspects
compiled proof dependencies afterward. No second kernel implementation was
used. Statement alignment was reviewed by the implementer; an independent
human or model review is not asserted. GitHub runners provide the separate
execution evidence named above.

## Public documentation

The one-command reproduction now performs the live audit and verifies its
receipt. README, the site, the machine index, and the repository contract use
the same current claim boundary. Repository and Pages links use the canonical
name. The previous teaching deck is labeled as a historical snapshot.
Le Chen's NSF CAREER grant DMS-2443823 is acknowledged. Vendor licenses and
the audit driver's upstream attribution are preserved.

## Repository history and publication decision

A redacted Gitleaks 8.30.1 scan covered all fetched history: 185 remote refs,
1,031 reachable commits including merges, and 849 commits processed by the
scanner. Four generic-key matches were independently verified to be SHA-256
values of the named source files. No credential was identified. Separate
credential and context scans of 157 issue/PR bodies, one issue comment, and
zero inline review comments found no matches. These counts describe the
frozen scan, not future repository content.

The earlier 2,752-line draft `fourier_resonant_filling_area_v3.tex` remains
reachable as blob `42a9c8d2e856943f6109031f8bf914ae65872d63`. Commit
`ecb50eb70bcb06181f1f6ca76a088fe9075b4105` removed it from the current tree
with the message “remove the draft latex, offical latex will be put on arxiv”.
Changing this repository to public would expose that draft along with branch
and pull-request history. The maintainer must decide whether that exposure is
intended before changing visibility. This audit did not rewrite history,
delete branches, change visibility, or publish a release.
