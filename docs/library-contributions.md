# Reusable Lean library roadmap

The formalization produced reusable topology, geometry, analysis, and
verification infrastructure in addition to its paper-facing theorems. This
page records how that work should be contributed back to the Lean ecosystem
without destabilizing the exact package that verified Theorems 1.1 and 1.2.

## Current package boundary

The repository currently defines one Lake package, `gromovFilling`, with four
Lean library targets:

- `GromovFilling`, the project-authored proof and certificate library;
- `SchoenfliesCompat`, the project-maintained namespace and compatibility
  layer derived from Apache-2.0 Mathlib sources;
- `ClassificationOfSurfaces`, an audited and adapted Apache-2.0 upstream
  source closure; and
- `Wikipedia`, an audited and adapted Apache-2.0 Jordan--Schönflies source
  closure.

This is a reproducible theorem package, not yet an independently versioned
general-purpose geometry package. In particular, it remains pinned to Lean
4.29.0 and fixed dependency commits, contains manuscript-specific endpoint
wrappers, and carries source with distinct provenance and licenses.

## Candidate contribution lanes

| Lane | Candidate modules | Intended destination |
|---|---|---|
| Small general-purpose contributions | `OrientationAreaForm`, `CompactLipschitzExtension`, `EuclideanAreaFormula`, `IntegratedComassLimit`, and the generic linear-algebra layer of `RiemannianTwoJacobian` | Focused Mathlib pull requests after current-master API review |
| Coherent research library | `LipschitzWeakStokes`, `CircleDegree`, the surface-orientation and chart-overlap modules, and the general Jordan-coverage interfaces | A separately versioned Lake package, with later leaf contributions to Mathlib where appropriate |
| Original dependency upstream | `ClassificationOfSurfaces/Moise/EmbeddedComplexBoundary`, the retained full Radó invariant, `BoundaryLocusClassification`, `RadoBoundaryLocus`, `RadoAmbientBoundary`, `CanonicalBoundaryLocus`, and `CanonicalBoundaryConnectedness` | [`mccorvie/classification-of-surfaces`](https://github.com/mccorvie/classification-of-surfaces) in dependency order |
| Manuscript-local assembly | `Constants`, final numerical certificates, theorem-numbered wrappers, and the public Theorem 1.1 and 1.2 assemblies | Remain in this verified repository |

The table classifies intended ownership; it does not claim that a declaration
is already upstream-ready. Each candidate still needs a current-library
duplicate search, minimal-import review, API redesign where necessary,
provenance confirmation, and a clean build on its target toolchain.

## Five-step contribution plan

### 1. Freeze the verified theorem artifact

Keep the exact merged theorem tree, Lean 4.29.0 toolchain, dependency pins,
source gates, full build, and live axiom receipts intact. Do not combine
library extraction, a toolchain migration, and changes to the verified
headline statements in one branch.

All extraction work should begin in a separate worktree or repository. The
closed theorem package remains the downstream regression test and scientific
record.

### 2. Build a separate reusable package

Port the reusable declarations into a separately versioned Lake package. The
initial extraction target should be the stable Lean release current when the
work begins; as of 2026-09-01 this is Lean 4.33.1. The original theorem
repository should remain on its verified pins during this work.

The extraction package should provide:

- explicit version, description, keywords, license, and README metadata;
- a canonical umbrella module and narrowly scoped library targets;
- authorship and provenance for every original, adapted, or vendored file;
- source-only continuous integration, tests, lints, documentation, and
  release tags; and
- compatibility wrappers showing that the original theorem endpoint types do
  not drift.

A public package can be indexed by
[Reservoir](https://reservoir.lean-lang.org/inclusion-criteria) after it meets
the registry's inclusion criteria. Repository visibility and licensing must be
approved before publication; this roadmap does not itself authorize changing
either.

### 3. Return surface-topology additions to their upstream

The relative-boundary classification work extends the exact
`classification-of-surfaces` source on which this project depends. It should
therefore be offered to that project rather than published as an unattributed
competing copy.

Prepare focused pull requests in this order:

1. the intrinsic edge-midpoint boundary/valence characterization;
2. the full-support Radó invariant export that retains boundary regularity;
3. identification of the polygonal, simplicial, and ambient boundary loci;
4. preservation of the complete free-side locus through normalization; and
5. connectedness, the single-boundary-block reduction, and the canonical
   boundary loop.

Follow the upstream project's
[contribution and verification requirements](https://github.com/mccorvie/classification-of-surfaces/blob/master/CONTRIBUTING.md),
including its full build, countermodel, declaration, blueprint, and axiom
checks. Compatibility-only Lean 4.29 edits should not be mixed into these
semantic pull requests.

### 4. Contribute small generic leaves to Mathlib

Do not submit the complete paper repository as one Mathlib pull request.
Start with small declaration families that import only Mathlib and naturally
extend an existing file. A suitable first design discussion is the
source-to-target oriented area-form bridge in `OrientationAreaForm`; the
compactly supported Lipschitz-extension lemmas are another small candidate.

Before opening a pull request:

1. search current Mathlib master for equivalent declarations;
2. discuss any new theory or API with the relevant Lean community;
3. remove project namespaces, constants, and downstream-only instances;
4. follow current naming, style, documentation, import, test, and lint rules;
5. submit one dependency layer per pull request; and
6. follow Mathlib's current AI-assistance disclosure policy, with a human
   contributor able to understand and defend every design decision.

See the official
[Mathlib contribution guide](https://leanprover-community.github.io/contribute/)
for the current requirements.

### 5. Integrate accepted upstream revisions downstream

Do not delete a local implementation merely because an upstream pull request
has been opened. Wait for an accepted upstream commit or release, then update
the theorem project in a separate maintenance change:

1. pin the accepted dependency revision;
2. replace the local implementation with a compatibility wrapper where
   necessary;
3. compare the complete public theorem types and hypotheses;
4. rerun the canonical umbrella and vendor-closure checks;
5. rerun the fail-closed source scan and negative control;
6. rebuild the full package and repeat the live axiom audit; and
7. record a new exact receipt before removing the superseded local source.

An upstream merge is a library milestone. A regenerated downstream receipt is
the separate verification milestone that establishes continued equivalence of
the paper-facing artifact.

## Readiness criterion

Extraction is complete only when the reusable package builds independently,
the accepted upstream revisions have explicit provenance, and this frozen
theorem project still proves equivalent endpoint statements under a new
receipt. Until then, the existing repository remains the source of record for
the verified theorems.
