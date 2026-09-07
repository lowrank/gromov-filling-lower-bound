# Lean module map

The canonical umbrella is `GromovFilling.lean`. CI regenerates the expected
module list and fails if any source file is missing from the umbrella.

## Source families

| Family | Main modules | Role |
|---|---|---|
| Constants and limits | `Constants`, `Universal`, `Numerics` | exact constants, asymptotic passage, rational enclosures |
| Fourier boundary | `FourierBoundary`, `FourierArea`, `FourierBessel`, `BoundaryActionSeries`, `OneHighLeg`, `ResonanceTrace` | triangle wave, Green action, Bessel estimates, finite resonance algebra, exact scalar trace arithmetic |
| Metric profiles | `DistanceProfile`, `ProfileFourier`, `RiemannianLipschitzDerivative`, `RiemannianProfileFourierEnergy` | genuine distance-defined Fourier maps, planar derivatives, sharp intrinsic Lipschitz-to-derivative bounds, and the pointwise intrinsic odd-mode Fourier energy budget |
| Orthogonal mixing | `Givens`, `BoundaryCertificate`, `DominantHarmonic` | explicit rotations, dominance, injectivity |
| Degree and Jordan theory | `CircleDegree`, `BoundaryDegree`, `RadialDegreeStability`, `JordanBoundary`, `JordanSchoenfliesFoundation`, `JordanSchoenfliesCoverage` | degree, components, arbitrary Jordan straightening, canonical bounded regions, and odd-degree coverage |
| Polygonal topology | `ModTwoDegree`, `PolygonalSurfaceObstruction`, `FinePolygonalModel`, `GeneralSurfaceObstruction`, `SurfaceTriangulationFoundation`, `RadoBoundaryLocus`, `RadoAmbientBoundary`, `SurfaceClassificationFoundation`, `BoundaryLocusClassification`, `CanonicalBoundaryLocus`, `CanonicalBoundaryConnectedness`, `NormalFormBoundaryObstruction`, `Lemma54` | finite obstruction, mesh interfaces, arbitrary side pairings, exact ambient-boundary identification, boundary-relative classification, connected one-block reduction, canonical-loop injectivity, and the end-to-end compact-surface obstruction |
| Area and Jacobians | `EuclideanAreaFormula`, `ComplexAreaFormula`, `RiemannianTwoJacobian`, `RiemannianJacobianBudget`, `RiemannianAreaFormula`, `RiemannianChartArea`, `RiemannianAtlasArea`, `RiemannianChartTransition`, `RiemannianInteriorChart`, `RiemannianChartDisjointification`, `RiemannianInteriorAtlasArea`, `RiemannianStandardChart`, `JacobianBudget`, `ComplexJacobianBudget` | planar area formula, intrinsic pointwise `J₂`, Riemannian chain rule, controlled interior charts, disjoint atlas coverage, overlap invariance, canonical Riemannian surface area, and pointwise/integrated determinant budgets |
| Coverage | `SurfaceCoverage`, `MetricPlanarCoverage`, `RiemannianInteriorCoverage`, `Lemma54Area` | abstract and metric Jordan coverage, interior preimages, and the full Lemma 5.4 area inequality |
| Oriented argument | `ClosedOneForm`, `Oriented`, `GeometricClosedOneForm` | Stokes interfaces and scalar nonlinear optimization |
| Surface orientation and boundary gluing | `RiemannianSurfaceOrientation`, `RiemannianControlledBoundaryActiveCover`, `RiemannianControlledBoundaryDirectionOverlap`, `RiemannianControlledBoundaryAxisLiftOverlap`, `RiemannianControlledBoundaryConventionalDirectionGlobal`, `RiemannianControlledBoundaryConventionalInducedOrientation` | project-defined conventional tangent orientation, local lift directions, overlap transport, global direction gluing, and agreement with the supplied boundary parametrization or its reversal |
| Barrier identities | `PositiveLogSineKernel`, `PolynomialDiskArea`, `DeSitterProfile` | off-diagonal log-sine positivity, holomorphic disk areas, de Sitter algebra |
| Final assembly | `Certificates`, `PlanarCertificate`, `GeometricCertificates`, `RiemannianUniversalFourierBound`, `RiemannianNonlinearCertificate`, `RiemannianExplicitNonlinearImprovement`, `RiemannianConventionalNonlinearImprovement` | reusable finite and infinite certificates and the public Theorems 1.1, 1.2, and all-parameter Riemannian endpoints |

## Trust-sensitive files

- `lean-toolchain` pins Lean `4.29.0`.
- `lakefile.lean` pins mathlib and the Jordan curve package.
- `lake-manifest.json` records the exact dependency revisions.
- `ClassificationOfSurfaces/VENDOR.json` pins the Apache-2.0 compact-surface
  classification source closure and its Lean/mathlib compatibility target.
- `Wikipedia/VENDOR.json` and `SchoenfliesCompat/VENDOR.json` pin the
  Apache-2.0 Jordan--Schönflies and graph-compatibility closures, including
  their namespace-isolation and Lean/mathlib compatibility targets.
- `.github/workflows/ci.yml` enforces the package build, umbrella check,
  fail-closed source scan with negative control, and live axiom audit.
- `scripts/verify.sh` is the one-command local reproduction path.

Browse the complete source tree in the
[GitHub repository](https://github.com/lowrank/gromov-filling-lower-bound/tree/main/GromovFilling).

## Revised Section 4

`SharpenedOriented` proves the capped ellipse estimate and defines the revised certificate. `SharpenedInfiniteVariation` proves the cancelled correlation bound; `SharpenedProfileTail` supplies the weight-25 energy inequality; `SharpenedComass` combines them with the existing quadratic and orientation estimates. `SharpenedNumerics` proves the rational lower enclosure at `1/25`. `RiemannianSharpenedNonlinear` connects those estimates to the existing finite Stokes and surface-area construction and exports the revised headline theorems.
