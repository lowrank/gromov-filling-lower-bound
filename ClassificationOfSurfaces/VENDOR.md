# Vendored compact-surface classification foundation

This directory contains the exact transitive Lean source closure of
`ClassificationOfSurfaces.EvalStatement` needed by the Gromov-filling
formalization.

- Upstream: <https://github.com/mccorvie/classification-of-surfaces>
- Upstream commit: `e3c7230fe78d7b056a415d9ecae6f77887046b32`
- Imported source files: 132
- Upstream license: Apache-2.0; see [`LICENSE`](LICENSE)
- Compatibility target: Lean 4.29.0 and mathlib v4.29.0

The upstream snapshot targets Lean 4.32.0. Files carrying an explicit
modification notice were adapted as needed for the repository's fixed
Lean/mathlib 4.29.0 pins. The `Compat` modules backport APIs from the
mathlib commit named in their headers. `Moise/ChartInduction.lean` also
exports the full-support `RadoInvariant` already established by the upstream
induction before its geometric-triangulation wrapper forgets that invariant.
Existing project dependency pins are not changed by this vendored source
import.

The imported theorems supply finite geometric triangulations of compact,
connected topological two-manifolds with boundary and classify them by
faithful sphere, orientable, or nonorientable polygonal quotient models. The
strengthened local wrapper retains boundary-facewise regularity. The
classification homeomorphism does not yet identify the manuscript's chosen
boundary circle with the appropriate free polygon loop; that relative
boundary statement remains a separate proof obligation.
