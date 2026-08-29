# Vendored Radó triangulation foundation

This directory contains the exact transitive Lean source closure of
`ClassificationOfSurfaces.Triangulation` needed by the Gromov-filling
formalization.

- Upstream: <https://github.com/mccorvie/classification-of-surfaces>
- Upstream commit: `e3c7230fe78d7b056a415d9ecae6f77887046b32`
- Imported source files: 81
- Upstream license: Apache-2.0; see [`LICENSE`](LICENSE)
- Compatibility target: Lean 4.29.0 and mathlib v4.29.0

The upstream snapshot targets Lean 4.32.0. Files carrying an explicit
modification notice were adapted only as needed for the repository's fixed
Lean/mathlib 4.29.0 pins. The `Compat` modules backport APIs from the
mathlib commit named in their headers. Existing project dependency pins are
not changed by this vendored source import.

The imported theorem supplies finite geometric triangulations of compact,
connected topological two-manifolds with boundary. It does not, by itself,
retain the boundary-facewise regularity needed to identify the manuscript's
chosen boundary circle. That refinement remains a separate proof obligation.
