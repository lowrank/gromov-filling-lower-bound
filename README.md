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

The script checks the canonical umbrella, restores the pinned mathlib cache,
builds the complete package, and rejects source-level proof escapes. GitHub CI
also audits every compiled project declaration against the exact allowlist
`propext`, `Classical.choice`, and `Quot.sound`.

## Verified core

- exact triangle-wave Fourier coefficients and boundary formulas;
- the explicit Givens product, orthogonality, energy preservation, and strict
  first-harmonic dominance;
- injectivity and degree `+1` for every mixed boundary curve;
- Jordan separation, bounded origin component, and polynomial disk area;
- finite mod-2 cochain obstruction with internally constructed lifts, edge
  turns, and face cuts;
- arbitrary fixed-point-free polygon-side pairings, including
  orientation-reversing identifications;
- planar Lipschitz area inequalities and Jacobian budgets;
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

The first hardened CI receipt audited **3,965 declarations** under
`GromovFilling`; every declaration stayed within the standard logical
allowlist. CI also fails if the umbrella omits a source module or if project
Lean source contains placeholder, custom axiom, unsafe, or native reduction
escape tokens.

## Current frontier

The end-to-end Riemannian statements still require:

1. a classification or compatible arbitrarily-fine cell decomposition for
   every compact connected surface with one boundary component;
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

Released under the [MIT License](LICENSE).
