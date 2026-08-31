# Manuscript-to-Lean statement ledger

This ledger records the formal status of every named mathematical item in
`fourier_resonant_filling_area_v3.tex`. “Verified” means that the stated claim
has a kernel-checked Lean theorem in this repository and is covered by the
package build and live axiom audit. “Partial” identifies the exact verified
core and the unverified bridge.

The ledger does **not** claim a proof of Gromov’s filling-area conjecture. The
manuscript's two headline lower bounds are strictly below the conjectural value
`2π`; both are now kernel-verified at the explicit interfaces recorded below.

| Manuscript item | Status | Lean scope and remaining boundary |
|---|---|---|
| Theorem 1.1, Universal Fourier bound | **Verified** | `riemannian_universal_fourier_bound` in `RiemannianUniversalFourierBound.lean` proves the `14 ζ(3) / π` lower bound for every compact connected Riemannian isometric filling whose boundary parametrization has the ambient boundary as its range. It combines the controlled-atlas Fubini/almost-everywhere bridge in `RiemannianProfileFourierAE.lean`, full `lemma54_riemannian_area`, the Givens disk areas, and the finite-to-infinite certificate. No differentiability, coverage, Jacobian-budget, or area conclusion is an assumption of the theorem. |
| Theorem 1.2, Explicit nonlinear improvement | **Verified** | `riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling` in `RiemannianExplicitNonlinearImprovement.lean` proves the strict bound `538982446 / 100000000 = 5.38982446` for compact connected Riemannian isometric fillings at the explicit orientation interface `R : ControlledRiemannianSurfaceOrientation M` and `H : ControlledRiemannianInducedBoundaryOrientation R boundary`. `R` supplies chart orientation signs; `H` supplies only outward-first local lift monotonicity. In particular, `H` contains no integral, winding, Stokes, comass, or area conclusion. The pinned manifold library has no conventional orientation API for manifolds with boundary, so this is the transparent formal meaning of the manuscript's oriented case. |
| Definition 2.1, odd profile and slack | **Verified** | Formalized in `DistanceProfile.lean` with antipodal, boundary, nonnegativity, and Lipschitz properties. |
| Eikonal identity for boundary distance functions | **Partial** | The exact Euclidean derivative-norm identity used by the planar model is proved in `ProfileFourier.lean`. `RiemannianLipschitzDerivative.lean` proves the sharp intrinsic upper bound `‖D f‖ ≤ K` at interior differentiability points. The broader raw-distance eikonal formulation remains open, but it is not a hypothesis of Theorem 1.1: `RiemannianProfileFourierAE.lean` proves the controlled-atlas Lipschitz/Fubini almost-everywhere route needed by that headline closure. |
| Lemma 3.1, Differentiating the coefficients | **Partial** | `hasFDerivAt_oddProfile_weightedIntegral` and the Fourier-coordinate derivative theorems in `ProfileFourier.lean` prove weak differentiation on `ℂ`. The exact broader manuscript formulation remains partial, while `RiemannianProfileFourierAE.lean` supplies the controlled-atlas product-measure argument and Fourier differentiability needed for the verified Theorem 1.1 path. |
| Proposition 3.2, Orthogonal Jacobian budget | **Partial** | The algebraic Bessel/Jacobian inequality and planar metric-profile derivative budget are verified in `JacobianBudget.lean` and `ProfileFourier.lean`; `RiemannianJacobianBudget.lean` proves the coordinate-free half-energy bridge. The named broader formulation remains partial, but the finite mixed-Givens Jacobian budget used by Theorem 1.1 is fully supplied in `RiemannianProfileFourierAE.lean`. |
| Lemma 4.1, Triangle-wave coefficients | **Verified** | Exact boundary Fourier coefficients are proved in `FourierBoundary.lean` and `ProfileFourier.lean`. |
| Lemma 5.1, Entries of the Givens product | **Verified** | Entry, orthogonality, and energy identities are proved in `Givens.lean`. |
| Lemma 5.2, First-harmonic dominance | **Verified** | All rowwise strict dominance estimates are proved in `Givens.lean` and exposed by `BoundaryCertificate.lean`. |
| Lemma 5.3, Dominant first harmonic | **Verified** | Injectivity, degree one, polynomial disk extension, Jordan-region identification, and exact Fourier area are proved across `DominantHarmonic*.lean`, `BoundaryDegree*.lean`, `GivensDisk*.lean`, and `JordanBoundary.lean`. |
| Lemma 5.4, Jordan coverage without orientation | **Verified** | `Lemma54.lean` proves the odd boundary-degree obstruction from the exact compact connected Hausdorff half-space-manifold hypotheses and a continuous injective parametrization of the whole ambient boundary. `JordanSchoenfliesCoverage.lean` uses the pinned relative Jordan--Schönflies theorem to define the canonical bounded component `Ω_C`, proves that it is open, connected, bounded, and exactly a complement component, derives its odd radial degree internally, and proves `Ω_C ⊆ G(M)` for every continuous extension with embedded boundary trace. `Lemma54Area.lean` strengthens this to interior preimages and proves the manuscript's full Riemannian conclusion: Euclidean area of `Ω_C` is at most the integral of the intrinsic two-Jacobian against the canonical Riemannian surface-area measure. No orientation or caller-supplied winding-number hypothesis remains. |
| Proposition 5.5, Finite universal certificate | **Verified** | `finite_universal_ennreal_of_givens_coverage_budget` gives the finite deduction. `RiemannianUniversalFourierBound.lean` supplies its coverage and Jacobian-budget hypotheses for every finite `N`; its stronger final theorem is `riemannian_universal_fourier_bound`. |
| Theorem 6.1, Antipodal defect | **Partial** | The pointwise defect budget and additive certificate propagation are verified on planar/chart interfaces. Intrinsic surface globalization remains unverified. |
| Lemma 7.1, Hilbert-valued Stokes | **Partial** | `ClosedOneForm.lean` proves fixed-endpoint homotopy invariance and disk/square Stokes/comass interfaces in finite-dimensional Euclidean targets. The infinite-dimensional Hilbert-valued surface theorem is not formalized. |
| Proposition 8.1, Separable nonlinear barrier | **Partial** | `PositiveLogSineKernel.lean` proves the squared-sine gap identity, positivity of both sine factors, strict positivity of the logarithmic kernel, and symmetry for `0 < t, s < π` with the necessary off-diagonal hypothesis `t ≠ s`. The Fourier-series identity, its diagonal/integrability treatment, and the scalar and Hilbert-valued quadratic-form optimization remain unverified. |
| Proposition 8.2, Holomorphic-disk barrier | **Partial** | `PolynomialDiskArea.lean` verifies the relevant holomorphic polynomial area identities. The complete Hilbert-space barrier statement and optimization are not formalized. |
| Proposition 9.1, Boundary action | **Verified** | Exact linear and quadratic odd-mode series are proved in `BoundaryActionSeries.lean`. |
| Lemma 10.1, Exact first variation | **Partial** | `Oriented.lean` verifies the scalar profile estimates used in the final bound. The exact Hardy autocorrelation first-variation identity is not represented as a Lean theorem. |
| Corollary 10.2, First-order stationarity | **Open feasible obligation** | Depends on the missing exact first-variation/autocorrelation theorem. |
| Proposition 11.1, Nonlinear comass bound | **Partial** | `nonlinear_comass_optimization` and the explicit `Cstar`, `Dstar`, and `Qstar` scalar estimates are verified. The broader analytic passage remains partial; the finite controlled-atlas passage at `λ = 0.03` required for Theorem 1.2 is closed. |
| Theorem 12.1, One-parameter nonlinear certificate | **Partial** | Boundary action, scalar comass division, and rigorous numerics are verified. The full one-parameter formulation remains partial, while its exact `λ = 0.03` controlled-orientation instance is closed by the verified Theorem 1.2 theorem. |
| Proposition 13.1, Infinite family of stationary resonances | **Open feasible obligation** | No Lean declaration currently encodes the general hierarchy and stationarity proof. |
| Lemma 14.1, High-mode test | **Partial** | `OneHighLeg.lean` exhibits the positive odd mode `m = 2J+1`, proves unit norm and anti-periodicity, and computes the exact symplectic value `1 + ∑ μⱼ²` of the occupied output coordinates. Identifying those coordinates with the differential of the full normalized nonlinear map, and hence with an arbitrary global ambient comass, remains unverified. |
| Theorem 14.2, Finite one-high-leg ceiling | **Partial** | `OneHighLeg.lean` defines the exact finite resonance matrix and boundary-action series, proves their quadratic-form identity, summability and weighted-Gram positivity, realizes the largest Rayleigh value as an eigenvalue, and proves the finite ceiling at the explicit high-mode interface. The infinite coefficient-space differential and global ambient-comass bridge remain unverified. |
| Lemma 14.3, Exact trace | **Partial** | `ResonanceTrace.lean` verifies nonnegative scalar double-series summability, Tonelli/antidiagonal reindexing, and the exact value `π/2 + 7ζ(3)/π + π³/24`. The ℓ² operator construction, Gram positivity, trace-class proof, and identification of this series with the operator trace remain unverified. |
| Theorem 14.4, Rigorous one-high-leg spectral ceiling | **Open feasible obligation** | The required operator/spectral estimate and numerical enclosure are absent. |
| Proposition 15.1, de Sitter identities | **Verified** | `DeSitterProfile.lean` proves the de Sitter quadric identity, the formal-velocity Lorentz speed, the pairwise Lorentz inner product, and Züst's coefficient-kernel identity. The interface takes the profile values and derivative value as explicit scalars and exposes every required nonzero sine denominator; it does not assert the separate almost-everywhere differentiability bridge for a Lipschitz profile. |

## Broader manuscript foundations outside the verified headline closures

The two headline theorem closures have no unmet project assumptions. The
following broader formulations remain tracked formalization gaps rather than
hidden hypotheses:

1. the general raw-distance eikonal/Rademacher formulation beyond the
   controlled-atlas Lipschitz/Fubini route used by Theorem 1.1;
2. a conventional manifold-with-boundary orientation and global
   differential-form/Stokes/comass API beyond the explicit controlled
   orientation interface used by Theorem 1.2.

The pinned mathlib revision contains Riemannian-manifold primitives but no
conventional orientation API for manifolds with boundary, surface
triangulation/classification theorem, relative Jordan--Schönflies theorem, or
ready-made manifold Stokes package. The project vendors and audits the exact
source closures needed for finite triangulability, faithful polygonal normal
forms, ambient Jordan straightening, controlled-atlas Fubini, and controlled
boundary Stokes. The relative-boundary classification, bounded-component
coverage, canonical Riemannian area measure, full Lemma 5.4 area inequality,
and both headline theorem closures are therefore proved without introducing
the broader formulations as project assumptions.

The 132-module transitive closure of
[`mccorvie/classification-of-surfaces`](https://github.com/mccorvie/classification-of-surfaces)
at commit `e3c7230fe78d7b056a415d9ecae6f77887046b32` is vendored under
`ClassificationOfSurfaces/`, with explicit Apache-2.0 provenance and Lean
4.29 compatibility notices. Its Radó theorem proves the existence of a finite
geometric triangulation, and the strengthened wrapper retains the
boundary-facewise invariant maintained during the proof. The new relative
normalization theorem proves that the faithful polygonal homeomorphism carries
the complete once-used-side locus to the canonical once-used-side locus.
`RadoBoundaryLocus.lean` first identifies that finite-cyclic locus exactly with
the complete valence-one edge locus of the original geometric triangulation.
`RadoAmbientBoundary.lean` identifies the valence-one locus with the ambient
manifold boundary. `CanonicalBoundaryLocus.lean` carries that complete locus
through the raw representative quotient, and
`CanonicalBoundaryConnectedness.lean` proves both that connectedness forces one
boundary block and that the resulting canonical loop is injective.
`Lemma54.lean` composes these results and identifies the supplied boundary
parametrization with the canonical loop up to a circle homeomorphism.
The pinned Jordan--Schönflies closure then straightens that loop to the model
square, where radial projection supplies an odd degree. Degree constancy
transports it over the whole bounded component. Finally,
`RiemannianInteriorAtlasArea.lean` and `Lemma54Area.lean` identify a finite
controlled interior atlas with canonical Riemannian surface area and prove the
intrinsic two-Jacobian inequality.

## Current trust evidence

- Lean `4.29.0`; mathlib `v4.29.0` at
  `8a178386ffc0f5fef0b77738bb5449d50efeea95`; JordanCurveTheorem at
  `e442525a662e9e3beb8205b9fa1fc99509076ded`.
- Theorem 1.1 merged receipt: GitHub Actions run
  [`33278266789`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33278266789)
  on merge commit `2e91793aac506118d24eb15733227f3693701bf5`.
- Theorem 1.2 exact-leaf receipt: GitHub Actions run
  [`33361483612`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33361483612)
  on receipt commit `171ceaa8ca2f086ddb481746e9769792b87b5578`.
- Consolidated source-only receipt: GitHub Actions run
  [`33363167477`](https://github.com/lowrank/conj-gromov-filling/actions/runs/33363167477)
  on exact source `7c19e1eb8e37b83a88190f15f9a65d4876797d74` passed the canonical
  umbrella and vendor checks, fail-closed proof-escape scan and injected-
  `sorry` negative control, full package build, and live audit.
- Live audit result: 6,304 declarations under `GromovFilling`; allowed axioms
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
