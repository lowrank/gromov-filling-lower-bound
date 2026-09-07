# Manuscript relationship

The Lean project accompanies *A Fourier approach to Gromov's Filling Area Conjecture*. This update follows the authors' `main2.tex` at Overleaf commit `85c9eb9`; its Section 4 contains the improved orientable bound. The manuscript source is maintained separately from this Lean repository.

## Mathematical scope

The note studies compact Riemannian fillings of the circle with no boundary
shortcuts. It proves an orientation-free lower bound

```text
14 ζ(3) / π = 5.3567723444...
```

and an oriented nonlinear improvement

```text
area > 5.40154.
```

The conjectural filling area remains `2π`. The paper develops stronger
certificates; it does not prove the conjecture.

## Formal scope

Lean verifies the finite Fourier algebra, exact boundary curves, orthogonal
mixing, Jordan and degree arguments, finite mod-2 obstruction, Riemannian
area inequalities, certificate deductions, and rigorous numerical conclusions.
It verifies the orientation-free universal Fourier bound and the oriented
nonlinear improvement, including both the strict decimal endpoint and the
all-parameter formula, at the exact interfaces described in the
[formalization boundary](formalization.md).

For Theorem 1.2, the project represents “oriented” by
`RiemannianSurfaceOrientation`: a tangent-plane orientation locally constant
in canonical tangent-bundle trivializations. Lean derives the required
controlled boundary data for the supplied parametrization or its reversal;
the final theorem has no controlled-atlas or induced-boundary hypothesis. The
pinned library still has no bundled generic manifold-with-boundary orientation
API, and no equivalence with a future such API is claimed. The formalization
does not claim Gromov's conjectural `2π` bound. Broader manuscript claims
listed as partial in the ledger are independent future work, not hidden
dependencies of either headline theorem.

## Source of record

- Current manuscript snapshot: `main2.tex`, Overleaf commit `85c9eb9`, SHA-256 `d6ec5c17e00be87d174cd730e2dd84b6c65881b3f36d4ab99abd0fb0dd556249`.
- [Current Section 4 statement map](section4.md).
- [Verified Lean source](https://github.com/lowrank/gromov-filling-lower-bound/tree/bdf0d050ee1d375d7025645c7a2ff22b9a2dd16b/GromovFilling).
- [Statement ledger](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/FORMALIZATION.md).
- [Earlier long manuscript](https://github.com/lowrank/gromov-filling-lower-bound/blob/6510257be426839a514ae0c7ae811a085264337f/fourier_resonant_filling_area_v3.tex), retained as historical context for the older ledger and module numbering.
- [Lean CI receipt](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34167476132).
