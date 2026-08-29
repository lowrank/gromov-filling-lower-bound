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
> manuscript proves lower bounds below the conjectural value `2π`, and the
> headline Lean statements remain conditional on named Riemannian-surface
> foundations. See [`FORMALIZATION.md`](FORMALIZATION.md) for the exact
> verified, partial, and open claim boundary.

## Headline certificate values

The verified finite-to-infinite and numerical layers establish the exact
orientation-free constant

$$
\frac{14\zeta(3)}{\pi}=5.3567723444\ldots
$$

and the scalar oriented nonlinear certificate at `λ = 0.03`

$$
5.38982446.
$$

Their application to every compact Riemannian isometric filling still needs
the geometric bridges listed under [Current frontier](#current-frontier).

## Quickstart

```bash
git clone https://github.com/lowrank/conj-gromov-filling.git
cd conj-gromov-filling
./scripts/verify.sh
```

The script checks the canonical umbrella, rejects source-level proof escapes,
proves that the escape gate catches an injected placeholder, restores the
pinned mathlib cache, and builds the complete package. GitHub CI also audits
every compiled project declaration against the exact allowlist `propext`,
`Classical.choice`, and `Quot.sound`.

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
- planar Lipschitz area inequalities and Jacobian budgets;
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
| [`GromovFilling.lean`](GromovFilling.lean) | canonical generated umbrella import |
| [`fourier_resonant_filling_area_v3.tex`](fourier_resonant_filling_area_v3.tex) | companion manuscript source |
| [`FORMALIZATION.md`](FORMALIZATION.md) | exact manuscript-to-Lean statement ledger |
| [`docs/`](docs/) | GitHub Pages documentation source |
| [`scripts/verify.sh`](scripts/verify.sh) | one-command local verification |
| [`.github/workflows/ci.yml`](.github/workflows/ci.yml) | import, build, source, and live axiom gates |

## Trust and reproducibility

The project is pinned to:

- Lean `4.29.0`;
- mathlib `v4.29.0`;
- EPFL LARA `JordanCurveTheorem` at
  `e442525a662e9e3beb8205b9fa1fc99509076ded`.

The latest hardened CI receipt, run
[`33226422322`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33226422322)
on merge commit `ecad55ca15d4bda1f73c59969d7dc9f8809736fa`, audited
**4,134 declarations** under `GromovFilling`; every declaration stayed within
the standard logical allowlist. CI also fails if the umbrella omits a source
module or if project Lean source contains placeholder, custom axiom, unsafe,
or native reduction escape tokens, and a negative control confirms that this
scan fails closed.

## Current frontier

The end-to-end Riemannian statements still require:

1. identification of the Radó valence-one edge locus with the ambient boundary,
   followed by the deduction that the supplied one-boundary parametrization
   selects the unique free loop in the verified polygonal classification
   normal form, up to a circle homeomorphism;
2. Riemannian eikonal and weak parameter-integral differentiation;
3. globalization of the planar area formula through surface charts, including
   the intrinsic `J₂` density;
4. a global differential-form Stokes/comass interface for the oriented case.

These are tracked gaps, not project axioms. The repository does not encode an
open target as an assumption and call the resulting implication a proof.

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
notices.
