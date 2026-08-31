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
mixing, Jordan and degree arguments, finite mod-2 obstruction, Riemannian
area inequalities, certificate deductions, and rigorous numerical conclusions.
It verifies the orientation-free universal Fourier bound and the strict
nonlinear improvement at the explicit controlled surface-orientation and
induced-boundary interface described in the
[formalization boundary](formalization.md).

That interface is necessary because the pinned manifold library has no
conventional orientation API for manifolds with boundary. Lean does not yet
derive the controlled interface from the manuscript's bare conventional
orientation hypothesis, so the unqualified manuscript Theorem 1.2 remains an
open bridge. It does not claim Gromov's conjectural `2π` bound. Broader
manuscript claims listed as partial in the ledger are independent future work
for Theorem 1.1 and the controlled-interface theorem; the orientation bridge
is explicitly tracked rather than hidden.

## Source of record

- Manuscript source: [`fourier_resonant_filling_area_v3.tex`](https://github.com/lowrank/conj-gromov-filling/blob/main/fourier_resonant_filling_area_v3.tex)
- Lean source: [`GromovFilling/`](https://github.com/lowrank/conj-gromov-filling/tree/main/GromovFilling)
- Statement ledger: [`FORMALIZATION.md`](https://github.com/lowrank/conj-gromov-filling/blob/main/FORMALIZATION.md)
- Verification workflow: [Lean CI](https://github.com/lowrank/conj-gromov-filling/actions/workflows/ci.yml)
