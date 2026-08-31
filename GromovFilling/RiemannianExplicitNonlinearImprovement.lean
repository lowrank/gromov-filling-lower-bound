import GromovFilling.RiemannianControlledBoundaryInducedPhase
import GromovFilling.RiemannianNonlinearCertificate

/-!
# Explicit nonlinear improvement for controlled oriented fillings

This is the manuscript-facing assembly of the oriented nonlinear theorem.
Compactness supplies a finite controlled boundary partition; the controlled
surface orientation and its induced outward-first boundary convention supply
the local phases; verified weak Stokes and the nonlinear certificate then
give the strict decimal lower bound.
-/

open Bundle Manifold Set
open scoped Bundle ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

/-- The explicit nonlinear improvement for a compact connected controlled
oriented Riemannian isometric filling.  Because the pinned manifold library
does not expose orientations for manifolds with boundary, orientation is
represented by `ControlledRiemannianSurfaceOrientation` together with its
honest induced-boundary compatibility datum. -/
theorem riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (H : ControlledRiemannianInducedBoundaryOrientation R boundary) :
    ENNReal.ofReal (538982446 / 100000000 : ℝ) <
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  let P : FiniteControlledBoundaryChartPartition M :=
    Classical.choice (nonempty_finiteControlledBoundaryChartPartition M)
  let B : ControlledBoundaryAtlasBoundaryPhase P
      (R.toBoundaryAtlasOrientation P) boundary :=
    Classical.choice
      (nonempty_controlledBoundaryAtlasBoundaryPhase_of_inducedBoundaryOrientation
        boundary hboundary hboundaryRange P R H)
  simpa only using B.surfaceArea_gt_point_zero_three hboundary

#print axioms
  riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling

end

end GromovFilling
