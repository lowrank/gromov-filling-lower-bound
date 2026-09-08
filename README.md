# Gromov filling-area formalization

[![Lean](https://img.shields.io/badge/Lean-4.29.0-137f9e.svg)](https://lean-lang.org/)
[![Lean CI](https://github.com/lowrank/gromov-filling-lower-bound/actions/workflows/ci.yml/badge.svg)](https://github.com/lowrank/gromov-filling-lower-bound/actions/workflows/ci.yml)
[![Documentation](https://github.com/lowrank/gromov-filling-lower-bound/actions/workflows/pages.yml/badge.svg)](https://lowrank.github.io/gromov-filling-lower-bound/)
[![License](https://img.shields.io/badge/license-MIT-0d2538.svg)](LICENSE)

![A circle boundary, triangulated spanning surface, and Fourier traces](docs/assets/hero.webp)

**Documentation:** <https://lowrank.github.io/gromov-filling-lower-bound/>

Lean 4 formalization of *A Fourier approach to Gromov's Filling Area Conjecture*
by Le Chen, Xiaolong Li, and Yimin Zhong.

> [!IMPORTANT]
> This repository does not prove Gromov's filling-area conjecture. The
> manuscript proves lower bounds below the conjectural value `2π`. Lean
> verifies Theorems 1.1 and 1.2 at their stated compact Riemannian
> isometric-filling interfaces. Theorem 1.2 reads “oriented” through the
> project-defined `RiemannianSurfaceOrientation` described below.
> See the [current manuscript ledger](docs/current-manuscript.md) for all
> 18 numbered statements and their verified or partial scope.

## Headline certificate values

`riemannian_universal_fourier_bound` establishes the orientation-free
Riemannian filling bound

$$
\frac{14\zeta(3)}{\pi}=5.3567723444\ldots
$$

`riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling`
establishes Theorem 1.2's strict bound at `λ = 1/25`

$$
5.40154.
$$

The companion theorem
`riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling`
establishes the revised Theorem 4.1 formula for every
`0 ≤ λ < π² / 32`. The project-defined orientation is a tangent-plane
orientation locally constant in canonical tangent-bundle trivializations. It
contains no boundary parametrization, controlled atlas, Stokes, winding,
comass, integral, or area conclusion. Lean derives the controlled boundary
data for the supplied parametrization or its reversal.

## Quickstart

```bash
git clone https://github.com/lowrank/gromov-filling-lower-bound.git
cd gromov-filling-lower-bound
./scripts/verify.sh
```

The command restores the pinned dependencies, builds the whole package, and
runs the live axiom audit against the exact allowlist `propext`,
`Classical.choice`, and `Quot.sound`. It records every checked declaration and
module, verifies a source receipt, and tests rejection of a compiled proof
gap and altered receipt inputs. See the [beginner and manual
instructions](docs/verification.md) for setup and interpretation.

## Verified core

- exact triangle-wave Fourier coefficients and boundary formulas;
- the explicit Givens product, orthogonality, energy preservation, and strict
  first-harmonic dominance;
- injectivity and degree `+1` for every mixed boundary curve;
- Jordan separation, bounded origin component, and polynomial disk area;
- finite mod-2 cochain obstruction with internally constructed lifts, edge
  turns, and face cuts;
- finite geometric triangulability of compact connected Hausdorff
  topological two-manifolds with boundary under the exact half-space chart
  hypotheses;
- arbitrary fixed-point-free polygon-side pairings, including
  orientation-reversing identifications;
- the full orientation-free Lemma 5.4: arbitrary Jordan-boundary coverage,
  interior preimages, and the canonical Riemannian two-Jacobian area
  inequality;
- Theorem 1.1: the universal Fourier lower bound for arbitrary compact
  connected Riemannian isometric fillings at the stated boundary interface;
- Theorem 1.2: the strict `λ = 1/25` nonlinear improvement, together with the
  all-parameter formula, for conventionally oriented Riemannian isometric
  fillings at the exact project-defined orientation interface;
- planar Lipschitz area inequalities and Jacobian budgets;
- sharp interior Riemannian Lipschitz-to-derivative bounds for boundary
  distance, odd-profile, and antipodal-slack functions;
- intrinsic half-energy two-Jacobian bounds and finite-family integrated
  Riemannian Jacobian budgets;
- strict positivity and symmetry of the Proposition 8.1 logarithmic sine
  kernel at interior off-diagonal points;
- summability, Tonelli/antidiagonal reindexing, and the exact closed form of
  the scalar double series underlying the Lemma 14.3 trace calculation;
- the finite one-high-leg odd-mode witness, exact boundary-action/resonance-
  matrix identity, weighted-Gram positivity, and Rayleigh ceiling;
- the de Sitter quadric, formal-velocity, Lorentz-product, and Züst-kernel
  identities from Proposition 15.1;
- finite and infinite certificate deductions, boundary-action series, and
  rigorous rational enclosures for the displayed constants.

The [current manuscript ledger](docs/current-manuscript.md) covers all 18 numbered statements; the [Section 4 map](docs/section4.md) gives the revised nonlinear proof details. [`FORMALIZATION.md`](FORMALIZATION.md) also preserves the historical 27-item ledger. The earlier `nonlinearCertificate` and `λ = 0.03` endpoint remain available.

## General polygon-side obstruction

`GromovFilling.GeneralSurfaceObstruction` removes the former
adjacent-preserving restriction. For every involutive fixed-point-free pairing,
paired edge turns agree or differ by sign according to the gluing orientation.
They cancel modulo two, so the glued lower loop has even circle degree and the
free boundary inherits the odd-degree obstruction.

The existing continuous-map and homeomorphism interfaces now derive this
lower obstruction automatically. Callers no longer supply it as a field.

## Repository map

| Path | Purpose |
|---|---|
| [`GromovFilling/`](GromovFilling/) | Lean definitions, lemmas, and certificate theorems |
| [`ClassificationOfSurfaces/`](ClassificationOfSurfaces/) | pinned Apache-2.0 compact-surface classification source closure, adapted to Lean 4.29 |
| [`Wikipedia/`](Wikipedia/) and [`SchoenfliesCompat/`](SchoenfliesCompat/) | pinned Apache-2.0 Jordan--Schönflies source closure and project compatibility layer |
| [`GromovFilling.lean`](GromovFilling.lean) | canonical generated umbrella import |
| [`docs/manuscript.md`](docs/manuscript.md) | manuscript version and source provenance |
| [`docs/current-manuscript.md`](docs/current-manuscript.md) | current manuscript statement ledger |
| [`FORMALIZATION.md`](FORMALIZATION.md) | headline boundary and historical 27-item ledger |
| [`AGENTS.md`](AGENTS.md) | repository contract for coding agents |
| [`docs/`](docs/) | GitHub Pages documentation source |
| [`scripts/verify.sh`](scripts/verify.sh) | one-command local verification |
| [`.github/workflows/ci.yml`](.github/workflows/ci.yml) | import, build, source, and live axiom gates |

## Trust and reproducibility

The project is pinned to:

- Lean `4.29.0`;
- mathlib `v4.29.0` at `8a178386ffc0f5fef0b77738bb5449d50efeea95`;
- EPFL LARA `JordanCurveTheorem` at
  `e442525a662e9e3beb8205b9fa1fc99509076ded`.

Lean CI [34167476132](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34167476132) on `bdf0d050ee1d375d7025645c7a2ff22b9a2dd16b` passed the full package build and live axiom audit. The audit accepted 6,762 declarations under `GromovFilling`, using only `propext`, `Classical.choice`, and `Quot.sound`.

[Machine-readable source and CI receipt](verification/section4-20260907.json).

The reproduction command also rejects missing umbrella imports and source-level proof escapes. Its compiled scratch control exercises the live axiom audit, and receipt mutation tests check source and inventory drift. See [verification](docs/verification.md) and the [current statement map](docs/current-manuscript.md).

## Verified headline boundary

Lemma 5.4 and Theorem 1.1 are end-to-end verified without an orientability
assumption. Theorem 1.2 is end-to-end verified with
`O : RiemannianSurfaceOrientation (modelWithCornersEuclideanHalfSpace 2) M`.
The final statements have no controlled-atlas, phase, induced-boundary,
coverage, Jacobian-budget, Stokes, comass, integral, or area-conclusion
hypothesis. The project-local orientation structure records the standard
tangent-plane datum and its local coherence; no equivalence with a future
generic Mathlib manifold-with-boundary orientation API is claimed.

Broader manuscript items such as the raw-distance eikonal formulation and a
standalone global manifold Stokes/comass API remain independently partial, but
they are not open dependencies of either headline theorem. Neither headline
reaches the conjectural `2π` bound.

## Documentation development

```bash
python3 -m venv .venv-docs
.venv-docs/bin/pip install -r requirements-docs.txt
.venv-docs/bin/mkdocs serve
```

Run `.venv-docs/bin/mkdocs build --strict` before submitting documentation
changes.

## Acknowledgment

Le Chen was partially supported by NSF CAREER grant DMS-2443823.

## License

The Gromov-filling project is released under the [MIT License](LICENSE). The
vendored compact-surface classification source closure retains its upstream
[Apache-2.0 license](ClassificationOfSurfaces/LICENSE) and modification
notices. The Jordan--Schönflies source and compatibility closures retain their
upstream [Apache-2.0](Wikipedia/LICENSE) licenses and provenance metadata.
The inventory driver, adapted from the upstream axiom-audit tool, is also
covered by [Apache-2.0](scripts/LICENSE.axiom-audit).
