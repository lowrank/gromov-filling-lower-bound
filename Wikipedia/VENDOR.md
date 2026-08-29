# Vendored Jordan–Schönflies foundation

This directory contains the exact transitive Lean source closure of
`Wikipedia.SchoenfliesTheorem.JordanSchoenflies` used by the Gromov-filling
formalization.

- Upstream: <https://github.com/plby/lean-proofs>
- Upstream commit: `2b380d2f2476782f55181ff21174a744cdb783d1`
- Upstream path: `src/latest`
- Imported source files: 134
- Upstream license: Apache-2.0; see [`LICENSE`](LICENSE)
- Upstream target: Lean 4.33.0 and mathlib commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`
- Repository target: Lean 4.29.0 and mathlib v4.29.0

The source was adapted to the repository's fixed toolchain. The changes are
compatibility-only: older set-API names, graph record syntax, scalar-action
normalization, continuous restriction names, and a larger heartbeat allowance
for the Jordan core. Graph imports are redirected to the four modules in
`SchoenfliesCompat`. Those modules namespace-isolate the newer mathlib
multigraph API as `SchoenfliesGraph` and backport the two missing graph
operations.

The repository also carries an independent pinned HOL Light Jordan-curve
development whose global `Graph` and `JordanCurveTheorem` names overlap the
upstream Schönflies closure. To make both verified developments coexist, the
vendored closure uses the alpha-renamed namespaces `SchoenfliesGraph` and
`SchoenfliesJordanCurveTheorem`. Four broad `import Mathlib` declarations in
the vendored Jordan proof are replaced by exact imports selected with
Mathlib's whole-file minimal-import linter. The vendor gate rejects a return of
the broad import or a transitive graph import. Existing Lean, mathlib, and HOL
Light Jordan-curve dependency pins are not changed.

The build and live trust audit verify the four exported Schönflies theorems.
Each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
