# Current manuscript statement ledger

This table covers all 18 numbered theorem, lemma, and proposition statements
in `main2.tex` at Overleaf commit `85c9eb955a7ae04c8d799def3ac8e68fa70028e9`.
Numbers and pages come from the compiled manuscript. The later Overleaf
commit `3c37718a4bd21de0e283fda7ebf39ce81e42e8a0` changes only the
formalization paragraph; these statements are unchanged.

The three main theorems are proved at the stated Riemannian filling
interfaces. Several intermediate claims are represented by the finite or
Fourier results needed in those proofs. Their broader standalone formulations
remain partial. A partial row is a coverage limitation, not a proof gap in a
Lean declaration or a missing premise of the three main theorems.

| Statement | Page | Status | Lean scope |
|---|---:|---|---|
| Theorem 1.1 | 1 | Verified | `riemannian_universal_fourier_bound`: the orientation-free `14 ζ(3)/π` area bound. |
| Theorem 1.2 | 2 | Verified | `riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling`: strict area bound `5.40154`. |
| Lemma 2.1 | 4 | Partially verified | `RiemannianLipschitzDerivative` proves the sharp upper derivative bound used by the surface proof. The raw-distance eikonal equality in the stated generality is not formalized. |
| Lemma 2.2 | 5 | Verified | `FourierBoundary` and `ProfileFourier`: exact triangle-wave boundary Fourier coefficients. |
| Lemma 2.3 | 5 | Partially verified | `RiemannianProfileFourierAE` supplies the controlled-atlas Fubini and almost-everywhere coefficient differentiation used by Theorem 1.1. The broader parameter-integral statement is not separately asserted. |
| Proposition 2.4 | 6 | Partially verified | `JacobianBudget`, `RiemannianJacobianBudget`, and `RiemannianProfileFourierAE` prove the algebraic and integrated Riemannian budgets. The Givens family used by the area theorem is supplied internally; the displayed general orthogonal-family proposition is not a standalone surface endpoint. |
| Lemma 3.1 | 8 | Verified | `Givens`: the explicit matrix entries and orthogonality. |
| Lemma 3.2 | 8 | Verified | `Givens` and `BoundaryCertificate`: rowwise strict first-harmonic dominance. |
| Lemma 3.3 | 9 | Verified | `DominantHarmonic`, `BoundaryDegree`, `PolynomialDiskArea`, and their companion modules: embedded boundary, degree one, and exact bounded-region area. |
| Lemma 3.4 | 10 | Verified | `Lemma54`, `JordanSchoenfliesCoverage`, and `Lemma54Area`: orientation-free Jordan coverage and the Riemannian area inequality. The module name retains its earlier manuscript number. |
| Proposition 3.5 | 11 | Verified | `finite_universal_ennreal_of_givens_coverage_budget`, with coverage and budget supplied in `RiemannianUniversalFourierBound`, gives the finite partial-sum bound. |
| Theorem 4.1 | 12 | Verified | `riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling`: the complete formula for every `0 ≤ λ < π²/32`. |
| Lemma 4.2 | 13 | Partially verified | Coefficient energy and profile-tail estimates. The standalone Hilbert-valued differentiability statement is outside the claim. |
| Proposition 4.3 | 14 | Partially verified | The exact boundary-action series and finite controlled-atlas Stokes deduction. A general Hilbert-valued surface-integral API is outside the claim. |
| Lemma 4.4 | 16 | Partially verified | Finite first variation, its infinite Fourier limit, cancellation, and stationarity. The broader differential-form statement is outside the claim. |
| Proposition 4.5 | 17 | Partially verified | The sharpened first-variation estimate for genuine profile Fourier coefficients; the surface proof supplies its hypotheses. |
| Lemma 4.6 | 19 | Partially verified | The finite quadratic-variation estimate and its use in the coherent truncation limit. |
| Proposition 4.7 | 19 | Partially verified | The infinite pointwise Fourier/comass estimate and integrated surface deduction, without a general Hilbert-valued differential-form API. |

The [Section 4 map](section4.md) names the exact intermediate declarations.
The numerical interval following Proposition 4.7 is only partly certified:
Lean proves the strict lower enclosure `5.401544`; its upper enclosure
`5.401545` is neither needed for Theorem 1.2 nor claimed as verified.

## Exact headline interfaces

The statements quantify over a compact connected Riemannian surface modeled
on the two-dimensional half-space, with a circle isometry parametrizing the
whole boundary. Theorem 1.1 uses an order-one manifold structure. The two
nonlinear endpoints use a smooth manifold and a supplied
`RiemannianSurfaceOrientation`, a locally coherent tangent-plane orientation.
The Lean types are recorded verbatim in the
[machine-readable statement ledger](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/verification/current-manuscript.json).

No final endpoint assumes a controlled atlas, boundary phase, Stokes theorem,
comass bound, Jacobian budget, coverage result, or area conclusion. The Lean
proof constructs those data. The initial interpretation of the manuscript's
geometric language in these definitions remains a human statement-alignment
check; no claim is made that Lean checks prose or novelty.

## Numbered formulas and historical material

The machine ledger retains every numbered equation environment, its label,
page, and source text. Definitions of the profile, Fourier coordinates,
boundary action, and sharpened constants are the transcription inputs.
The finite identities and estimates used in the headline proofs are checked
from those inputs. Hilbert-space formulas inherit the partial scope of the
corresponding rows above.

The [27-item historical ledger](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/FORMALIZATION.md)
belongs to the earlier long draft. Its later barrier, resonance-hierarchy, and
spectral questions are outside the current 18-statement manuscript. Its open
items are retained as historical research obligations, not advertised as
completed formalization.
