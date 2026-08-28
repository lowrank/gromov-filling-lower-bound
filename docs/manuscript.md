# Manuscript relationship

The Lean project accompanies
`fourier_resonant_filling_area_v3.tex`, titled *Fourier and Resonant Nonlinear
Bounds for Gromov's Filling Area Problem*.

## Mathematical scope

The note studies compact Riemannian fillings of the circle with no boundary
shortcuts. It proves an orientation-free lower bound

```text
14 ζ(3) / π = 5.3567723444...
```

and an oriented nonlinear improvement

```text
area > 5.38982446.
```

The conjectural filling area remains `2π`. The paper develops stronger
certificates; it does not prove the conjecture.

## Formal scope

Lean verifies the finite Fourier algebra, exact boundary curves, orthogonal
mixing, Jordan and degree arguments, finite mod-2 obstruction, planar area
inequalities, certificate deductions, and rigorous numerical conclusions.

The general-surface realization of the topological and analytic interfaces is
still open. See the [formalization boundary](formalization.md) before citing a
statement as machine-checked.

## Source of record

- Manuscript source: [`fourier_resonant_filling_area_v3.tex`](https://github.com/lowrank/conj-gromov-filling/blob/main/fourier_resonant_filling_area_v3.tex)
- Lean source: [`GromovFilling/`](https://github.com/lowrank/conj-gromov-filling/tree/main/GromovFilling)
- Statement ledger: [`FORMALIZATION.md`](https://github.com/lowrank/conj-gromov-filling/blob/main/FORMALIZATION.md)
- Verification workflow: [Lean CI](https://github.com/lowrank/conj-gromov-filling/actions/workflows/ci.yml)

