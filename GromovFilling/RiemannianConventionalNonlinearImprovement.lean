import GromovFilling.RiemannianControlledBoundaryConventionalInducedOrientation
import GromovFilling.RiemannianExplicitNonlinearImprovement

/-!
# Nonlinear improvement for conventionally oriented fillings

This module removes the explicit controlled induced-boundary-orientation
interface from the two manuscript-facing nonlinear statements.  A conventional
surface orientation gives that interface for the supplied boundary
parametrization or its reversal, and the surface-area conclusions are
unchanged by this harmless reparametrization.
-/

open Bundle Manifold Set
open scoped Bundle ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance conventionalNonlinearImprovementEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- The strict decimal nonlinear improvement for every compact connected
conventionally oriented Riemannian isometric filling. -/
theorem riemannianSurfaceArea_gt_point_zero_three_of_conventionally_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
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
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) :
    letI : Nonempty M := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (538982446 / 100000000 : ℝ) <
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  rcases O.controlledInducedBoundaryOrientation_or_reverse
      boundary hboundary hboundaryRange with H | H
  · exact riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling
      boundary hboundary hboundaryRange O.toControlledRiemannianSurfaceOrientation H
  · have hreverseRange : Set.range (reverseCircleBoundary boundary) =
        (modelWithCornersEuclideanHalfSpace 2).boundary M :=
      (range_reverseCircleBoundary boundary).trans hboundaryRange
    simpa only [reverseCircleBoundary_apply, neg_zero] using
      (riemannianSurfaceArea_gt_point_zero_three_of_controlled_oriented_isometric_filling
        (reverseCircleBoundary boundary) hboundary.reverse hreverseRange
        O.toControlledRiemannianSurfaceOrientation H)

/-- The all-parameter nonlinear master formula for every compact connected
conventionally oriented Riemannian isometric filling. -/
theorem riemannianNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
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
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    letI : Nonempty M := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (nonlinearCertificate lam) ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  rcases O.controlledInducedBoundaryOrientation_or_reverse
      boundary hboundary hboundaryRange with H | H
  · exact riemannianNonlinearCertificate_le_surfaceArea_of_controlled_oriented_isometric_filling
      boundary hboundary hboundaryRange O.toControlledRiemannianSurfaceOrientation
      H lam hlam0 hlam
  · have hreverseRange : Set.range (reverseCircleBoundary boundary) =
        (modelWithCornersEuclideanHalfSpace 2).boundary M :=
      (range_reverseCircleBoundary boundary).trans hboundaryRange
    simpa only [reverseCircleBoundary_apply, neg_zero] using
      (riemannianNonlinearCertificate_le_surfaceArea_of_controlled_oriented_isometric_filling
        (reverseCircleBoundary boundary) hboundary.reverse hreverseRange
        O.toControlledRiemannianSurfaceOrientation H lam hlam0 hlam)

#print axioms
  riemannianSurfaceArea_gt_point_zero_three_of_conventionally_oriented_isometric_filling
#print axioms
  riemannianNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling

end

end GromovFilling
