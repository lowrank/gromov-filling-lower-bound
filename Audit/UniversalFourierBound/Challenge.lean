import Audit.UniversalFourierBound.Defs

/-!
# Comparator challenge: the universal Fourier bound (Theorem 1.1)

Statement only. Its definitions are in `Defs.lean`, which imports Mathlib alone
and copies them verbatim from `GromovFilling` (Constants, DistanceProfile, RiemannianTwoJacobian,
RiemannianChartArea, RiemannianAtlasArea, RiemannianChartDisjointification and
RiemannianInteriorAtlasArea), so that a reader can check the meaning of "area"
here without trusting the rest of the project:

* `twoJacobian L` is the absolute determinant of a linear map between real
  two-dimensional inner-product spaces, in orthonormal bases;
* a `ControlledInteriorAtlas` is a finite family of injective, Lipschitz, `C¹`
  parametrizations from open subsets of `ℂ` whose images are open, lie in the
  manifold interior, and cover it;
* `ControlledInteriorAtlas.areaMeasure` pushes Lebesgue measure on the
  first-occurrence pieces of the coordinate domains, weighted by the Riemannian
  two-Jacobian of the parametrization, to the manifold and sums over the charts.

Claim: a compact connected Riemannian surface (with boundary) whose boundary is
an isometric circle of circumference `2π` has a controlled interior atlas, and
every such atlas gives the whole surface area at least `14 ζ(3) / π`. In the
project, every controlled atlas computes the same measure
(`ControlledInteriorAtlas.areaMeasure_eq`), so this is Theorem 1.1 for the
canonical surface area.
-/

open Bundle MeasureTheory Set
open scoped BigOperators Bundle ENNReal Manifold NNReal

namespace GromovFillingAudit.UniversalFourierBound

noncomputable section

/-- **Theorem 1.1 (Universal Fourier bound).** A compact connected Riemannian
filling of an isometric circle of circumference `2π` has a controlled interior
atlas, and every such atlas gives it area at least `14 ζ(3) / π`. -/
theorem riemannian_universal_fourier_bound
    (S : Type*) [PseudoMetricSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S]
    [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S]
    [RiemannianBundle (fun x : S ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : S ↦
        TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) S]
    (boundary : UnitAddCircle → S)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S) :
    Nonempty (ControlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2) S) ∧
      ∀ A : ControlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2) S,
        ENNReal.ofReal universalConstant ≤
          A.areaMeasure (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set S) := by
  sorry

end

end GromovFillingAudit.UniversalFourierBound
