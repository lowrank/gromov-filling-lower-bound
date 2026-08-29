# Lean module map

The canonical umbrella is `GromovFilling.lean`. CI regenerates the expected
module list and fails if any source file is missing from the umbrella.

## Source families

| Family | Main modules | Role |
|---|---|---|
| Constants and limits | `Constants`, `Universal`, `Numerics` | exact constants, asymptotic passage, rational enclosures |
| Fourier boundary | `FourierBoundary`, `FourierArea`, `FourierBessel`, `BoundaryActionSeries`, `OneHighLeg`, `ResonanceTrace` | triangle wave, Green action, Bessel estimates, finite resonance algebra, exact scalar trace arithmetic |
| Metric profiles | `DistanceProfile`, `ProfileFourier` | genuine distance-defined Fourier maps and planar derivatives |
| Orthogonal mixing | `Givens`, `BoundaryCertificate`, `DominantHarmonic` | explicit rotations, dominance, injectivity |
| Degree and Jordan theory | `CircleDegree`, `BoundaryDegree`, `RadialDegreeStability`, `JordanBoundary` | degree, components, and Jordan regions |
| Polygonal topology | `ModTwoDegree`, `PolygonalSurfaceObstruction`, `FinePolygonalModel`, `GeneralSurfaceObstruction`, `SurfaceTriangulationFoundation`, `RadoBoundaryLocus`, `RadoAmbientBoundary`, `SurfaceClassificationFoundation`, `BoundaryLocusClassification`, `CanonicalBoundaryLocus`, `CanonicalBoundaryConnectedness`, `NormalFormBoundaryObstruction`, `Lemma54` | finite obstruction, mesh interfaces, arbitrary side pairings, exact ambient-boundary identification, boundary-relative classification, connected one-block reduction, canonical-loop injectivity, and the end-to-end compact-surface obstruction |
| Area and Jacobians | `EuclideanAreaFormula`, `ComplexAreaFormula`, `RiemannianTwoJacobian`, `RiemannianAreaFormula`, `JacobianBudget`, `ComplexJacobianBudget` | planar area formula, intrinsic pointwise `J₂`, exact planar bridge, and determinant budgets |
| Coverage | `SurfaceCoverage`, `MetricPlanarCoverage` | Jordan-region coverage for abstract and metric Fourier maps |
| Oriented argument | `ClosedOneForm`, `Oriented`, `GeometricClosedOneForm` | Stokes interfaces and scalar nonlinear optimization |
| Barrier identities | `PositiveLogSineKernel`, `PolynomialDiskArea`, `DeSitterProfile` | off-diagonal log-sine positivity, holomorphic disk areas, de Sitter algebra |
| Final assembly | `Certificates`, `PlanarCertificate`, `GeometricCertificates` | reusable finite and infinite certificate endpoints |

## Trust-sensitive files

- `lean-toolchain` pins Lean `4.29.0`.
- `lakefile.lean` pins mathlib and the Jordan curve package.
- `lake-manifest.json` records the exact dependency revisions.
- `ClassificationOfSurfaces/VENDOR.json` pins the Apache-2.0 compact-surface
  classification source closure and its Lean/mathlib compatibility target.
- `.github/workflows/ci.yml` enforces the package build, umbrella check,
  fail-closed source scan with negative control, and live axiom audit.
- `scripts/verify.sh` is the one-command local reproduction path.

Browse the complete source tree in the
[GitHub repository](https://github.com/lowrank/conj-gromov-filling/tree/main/GromovFilling).
