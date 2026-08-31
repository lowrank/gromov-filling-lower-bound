# Gromov filling-area formalization

[![Lean](https://img.shields.io/badge/Lean-4.29.0-137f9e.svg)](https://lean-lang.org/)
[![Lean CI](https://github.com/lowrank/conj-gromov-filling/actions/workflows/ci.yml/badge.svg)](https://github.com/lowrank/conj-gromov-filling/actions/workflows/ci.yml)
[![Documentation](https://github.com/lowrank/conj-gromov-filling/actions/workflows/pages.yml/badge.svg)](https://lowrank.github.io/conj-gromov-filling/)
[![License](https://img.shields.io/badge/license-MIT-0d2538.svg)](LICENSE)

![A circle boundary, triangulated spanning surface, and Fourier traces](docs/assets/hero.webp)

**Documentation:** <https://lowrank.github.io/conj-gromov-filling/>

Lean 4 formalization of the Fourier, topology, planar area, and certificate
arguments accompanying Yimin Zhong's note *Fourier and Resonant Nonlinear
Bounds for Gromov's Filling Area Problem*.

> [!IMPORTANT]
> This repository does not prove Gromov's filling-area conjecture. The
> manuscript proves lower bounds below the conjectural value `2π`. Lean
> verifies Theorem 1.1 for the stated compact Riemannian isometric-filling
> interface and Theorem 1.2 at its explicit controlled-orientation interface.
> See [`FORMALIZATION.md`](FORMALIZATION.md) for the exact verified, partial,
> and open claim boundary.

## Headline certificate values

`riemannian_universal_fourier_bound` establishes the orientation-free
Riemannian filling bound

$$
\frac{14\zeta(3)}{\pi}=5.3567723444\ldots
$$

`riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling`
establishes the strict nonlinear bound at `λ = 0.03` for the explicit
`R`/`H` controlled surface-orientation and induced-boundary interface

$$
5.38982446.
$$

The latter interface is explicit because the pinned manifold library does not
provide a conventional orientation API for manifolds with boundary. Its
induced-boundary compatibility datum records local lift monotonicity only; it
does not assume a Stokes, winding, comass, integral, or area conclusion.

## Quickstart

```bash
git clone https://github.com/lowrank/conj-gromov-filling.git
cd conj-gromov-filling
./scripts/verify.sh
```

The script checks the canonical umbrella, rejects source-level proof escapes,
proves that the escape gate catches an injected placeholder, restores the
pinned mathlib cache, and builds the complete package. GitHub CI also audits
every declaration rooted at `GromovFilling` against the exact allowlist
`propext`, `Classical.choice`, and `Quot.sound`.

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
- Theorem 1.2: the strict nonlinear lower bound at the explicit controlled
  surface-orientation and outward-first induced-boundary interface;
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

The full manuscript-facing ledger contains 27 named items and is maintained in
[`FORMALIZATION.md`](FORMALIZATION.md).

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
| [`fourier_resonant_filling_area_v3.tex`](fourier_resonant_filling_area_v3.tex) | companion manuscript source |
| [`FORMALIZATION.md`](FORMALIZATION.md) | exact manuscript-to-Lean statement ledger |
| [`docs/`](docs/) | GitHub Pages documentation source |
| [`scripts/verify.sh`](scripts/verify.sh) | one-command local verification |
| [`.github/workflows/ci.yml`](.github/workflows/ci.yml) | import, build, source, and live axiom gates |

## Trust and reproducibility

The project is pinned to:

- Lean `4.29.0`;
- mathlib `v4.29.0` at `8a178386ffc0f5fef0b77738bb5449d50efeea95`;
- EPFL LARA `JordanCurveTheorem` at
  `e442525a662e9e3beb8205b9fa1fc99509076ded`.

The consolidated source-only CI receipt,
[`33363167477`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33363167477)
on exact source `7c19e1eb8e37b83a88190f15f9a65d4876797d74`, audited
**6,304 declarations** under `GromovFilling`; every declaration stayed within
the standard logical allowlist. CI also fails if the umbrella omits a source
module or if project Lean source contains placeholder, custom axiom, unsafe,
or native reduction escape tokens, and a negative control confirms that this
scan fails closed.

## Verified headline boundary

Lemma 5.4 and Theorem 1.1 are end-to-end verified without an orientability
assumption. The controlled-interface version of Theorem 1.2 is end-to-end
verified at the explicit
`R : ControlledRiemannianSurfaceOrientation M` and
`H : ControlledRiemannianInducedBoundaryOrientation R boundary` interface.
Those structures make the missing standard library notion of an orientation
with boundary visible rather than hiding it in an axiom or a conclusion-
bearing hypothesis. Lean does not yet derive that interface from the
manuscript's bare conventional orientation assumption, so the unqualified
manuscript Theorem 1.2 remains an open bridge.

Broader manuscript items such as a raw-distance eikonal theorem, a general
one-parameter nonlinear formula, and a conventional global manifold Stokes
API remain independently partial. They are not open dependencies of the two
headline declarations. Neither headline reaches the conjectural `2π` bound.

## Documentation development

```bash
python3 -m venv .venv-docs
.venv-docs/bin/pip install -r requirements-docs.txt
.venv-docs/bin/mkdocs serve
```

Run `.venv-docs/bin/mkdocs build --strict` before submitting documentation
changes.

## License

The Gromov-filling project is released under the [MIT License](LICENSE). The
vendored compact-surface classification source closure retains its upstream
[Apache-2.0 license](ClassificationOfSurfaces/LICENSE) and modification
notices. The Jordan--Schönflies source and compatibility closures retain their
upstream [Apache-2.0](Wikipedia/LICENSE) licenses and provenance metadata.
