# Manuscript-to-Lean statement ledger

This ledger records the formal status of every named mathematical item in
`fourier_resonant_filling_area_v3.tex`. “Verified” means that the stated
finite, algebraic, planar, or numerical claim has a Lean theorem in this
repository and is covered by the package build and live axiom audit.
“Partial” identifies the exact verified core and the unverified bridge.

The ledger does **not** claim a proof of Gromov’s filling-area conjecture. The
manuscript proves lower bounds strictly below the conjectural value `2π`, and
its two headline lower bounds are not yet kernel-verified for arbitrary
Riemannian surfaces.

| Manuscript item | Status | Lean scope and remaining boundary |
|---|---|---|
| Theorem 1.1, Universal Fourier bound | **Partial** | `Universal.lean`, `Certificates.lean`, and `Numerics.lean` verify the finite-to-infinite deduction and exact constant. Coverage and Jacobian input for an arbitrary Riemannian surface remains unverified. |
| Theorem 1.2, Explicit nonlinear improvement | **Partial** | `Oriented.lean`, `BoundaryActionSeries.lean`, `Certificates.lean`, and `Numerics.lean` verify the scalar certificate and strict decimal conclusion from a calibrated Stokes/comass inequality. The global Riemannian-surface inequality remains unverified. |
| Definition 2.1, odd profile and slack | **Verified** | Formalized in `DistanceProfile.lean` with antipodal, boundary, nonnegativity, and Lipschitz properties. |
| Eikonal identity for boundary distance functions | **Partial** | The exact Euclidean derivative-norm identity used by the planar model is proved in `ProfileFourier.lean`. The Riemannian-manifold almost-everywhere eikonal theorem and product-measure bridge are not formalized. |
| Lemma 3.1, Differentiating the coefficients | **Partial** | `hasFDerivAt_oddProfile_weightedIntegral` and the Fourier-coordinate derivative theorems in `ProfileFourier.lean` prove weak differentiation on `ℂ`. The full surface-chart version is not formalized. |
| Proposition 3.2, Orthogonal Jacobian budget | **Partial** | The algebraic Bessel/Jacobian inequality and genuine planar metric-profile derivative budget are verified in `JacobianBudget.lean` and `ProfileFourier.lean`. Global intrinsic surface integration is not formalized. |
| Lemma 4.1, Triangle-wave coefficients | **Verified** | Exact boundary Fourier coefficients are proved in `FourierBoundary.lean` and `ProfileFourier.lean`. |
| Lemma 5.1, Entries of the Givens product | **Verified** | Entry, orthogonality, and energy identities are proved in `Givens.lean`. |
| Lemma 5.2, First-harmonic dominance | **Verified** | All rowwise strict dominance estimates are proved in `Givens.lean` and exposed by `BoundaryCertificate.lean`. |
| Lemma 5.3, Dominant first harmonic | **Verified** | Injectivity, degree one, polynomial disk extension, Jordan-region identification, and exact Fourier area are proved across `DominantHarmonic*.lean`, `BoundaryDegree*.lean`, `GivensDisk*.lean`, and `JordanBoundary.lean`. |
| Lemma 5.4, Jordan coverage without orientation | **Partial** | The finite mod-2 obstruction, arbitrary polygon-side pairing theorem, and glued-schema coverage deductions are verified. What remains is a classification/triangulation bridge from every compact one-boundary surface to such a schema. |
| Proposition 5.5, Finite universal certificate | **Partial** | `finite_universal_certificate` and its certificate wrappers verify the deduction from coverage plus Jacobian budgets. Those geometric budgets are not yet supplied for arbitrary Riemannian surfaces. |
| Theorem 6.1, Antipodal defect | **Partial** | The pointwise defect budget and additive certificate propagation are verified on planar/chart interfaces. Intrinsic surface globalization remains unverified. |
| Lemma 7.1, Hilbert-valued Stokes | **Partial** | `ClosedOneForm.lean` proves fixed-endpoint homotopy invariance and disk/square Stokes/comass interfaces in finite-dimensional Euclidean targets. The infinite-dimensional Hilbert-valued surface theorem is not formalized. |
| Proposition 8.1, Separable nonlinear barrier | **Partial** | `PositiveLogSineKernel.lean` proves the squared-sine gap identity, positivity of both sine factors, strict positivity of the logarithmic kernel, and symmetry for `0 < t, s < π` with the necessary off-diagonal hypothesis `t ≠ s`. The Fourier-series identity, its diagonal/integrability treatment, and the scalar and Hilbert-valued quadratic-form optimization remain unverified. |
| Proposition 8.2, Holomorphic-disk barrier | **Partial** | `PolynomialDiskArea.lean` verifies the relevant holomorphic polynomial area identities. The complete Hilbert-space barrier statement and optimization are not formalized. |
| Proposition 9.1, Boundary action | **Verified** | Exact linear and quadratic odd-mode series are proved in `BoundaryActionSeries.lean`. |
| Lemma 10.1, Exact first variation | **Partial** | `Oriented.lean` verifies the scalar profile estimates used in the final bound. The exact Hardy autocorrelation first-variation identity is not represented as a Lean theorem. |
| Corollary 10.2, First-order stationarity | **Open feasible obligation** | Depends on the missing exact first-variation/autocorrelation theorem. |
| Proposition 11.1, Nonlinear comass bound | **Partial** | `nonlinear_comass_optimization` and the explicit `Cstar`, `Dstar`, and `Qstar` scalar estimates are verified. The analytic passage from genuine surface profiles to its hypotheses is not formalized. |
| Theorem 12.1, One-parameter nonlinear certificate | **Partial** | Boundary action, scalar comass division, and rigorous numerics are verified conditional on the global Stokes/comass inequality. |
| Proposition 13.1, Infinite family of stationary resonances | **Open feasible obligation** | No Lean declaration currently encodes the general hierarchy and stationarity proof. |
| Lemma 14.1, High-mode test | **Open feasible obligation** | Not formalized. |
| Theorem 14.2, Finite one-high-leg ceiling | **Open feasible obligation** | Not formalized. |
| Lemma 14.3, Exact trace | **Open feasible obligation** | Not formalized. |
| Theorem 14.4, Rigorous one-high-leg spectral ceiling | **Open feasible obligation** | The required operator/spectral estimate and numerical enclosure are absent. |
| Proposition 15.1, de Sitter identities | **Verified** | `DeSitterProfile.lean` proves the de Sitter quadric identity, the formal-velocity Lorentz speed, the pairwise Lorentz inner product, and Züst's coefficient-kernel identity. The interface takes the profile values and derivative value as explicit scalars and exposes every required nonzero sine denominator; it does not assert the separate almost-everywhere differentiability bridge for a Lipschitz profile. |

## End-to-end foundations not supplied by the pinned libraries

The following are tracked formalization gaps rather than hidden hypotheses:

1. a classification or compatible arbitrarily-fine cell-decomposition theorem
   for every compact connected surface with one boundary component;
2. Rademacher/eikonal and parameter-integral differentiation on a
   two-dimensional Riemannian manifold with boundary;
3. globalization of the planar area formula through Riemannian charts,
   including identification of coordinate determinant density with `J₂`;
4. the global differential-form/Stokes/comass interface for the oriented
   argument.

The pinned mathlib revision contains Riemannian-manifold primitives but no
surface triangulation/classification theorem or ready-made manifold area
formula/Stokes package that closes these bridges. Introducing them as project
assumptions would produce a conditional shell, not an end-to-end verification,
so this project records them explicitly instead.

## Current trust evidence

- Lean `4.29.0`, mathlib `v4.29.0`, JordanCurveTheorem
  `e442525a662e9e3beb8205b9fa1fc99509076ded`.
- GitHub Actions run `33222433335` on merge commit
  `24a89cc64c589f1f8895e19697b37fdf56e674bd`: canonical umbrella check,
  fail-closed source scan, injected-`sorry` negative control, full package
  build, and live axiom audit.
- Live audit result: 4,002 declarations under `GromovFilling`; allowed axioms
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
