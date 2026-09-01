import GromovFilling.RiemannianHalfSpaceChartTransitionTrivializationDeterminant
import GromovFilling.RiemannianSurfaceOrientationCoordinateParity
import GromovFilling.RiemannianSurfaceOrientationTransport

/-!
# Conventional chart signs and transition determinants

This module combines the local orientation-coordinate parity theorem with
the derivative/trivialization determinant identification. The result applies
when the common point belongs to the selected controlled-chart image of each
chart; it deliberately leaves global chart-overlap selection separate.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianSurfaceOrientationTransitionParityEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Equal conventional controlled-chart signs force a positive determinant
for an extended-chart transition when its source point is represented in the
selected controlled image of each chart. -/
theorem RiemannianSurfaceOrientation.controlledChartSign_eq_transition_det_pos
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hAImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart a ''
        chosenControlledHalfSpaceComplexChartDomain a)
    (hBImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart b ''
        chosenControlledHalfSpaceComplexChartDomain b)
    (hsign : O.controlledChartSign a = O.controlledChartSign b) :
    0 < (fderivWithin ℝ
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z).det := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  let p : M := (extChartAt I a).symm z
  let D : E →L[ℝ] E :=
    fderivWithin ℝ
      (extChartAt I b ∘ (extChartAt I a).symm)
      ((extChartAt I a).symm ≫ extChartAt I b).source z
  change z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source at hz
  change p ∈ halfSpaceComplexExtChart a ''
    chosenControlledHalfSpaceComplexChartDomain a at hAImage
  change p ∈ halfSpaceComplexExtChart b ''
    chosenControlledHalfSpaceComplexChartDomain b at hBImage
  change 0 < D.det
  obtain ⟨hpa, hA⟩ :=
    RiemannianSurfaceOrientation.exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage
      O a p hAImage
  obtain ⟨hpb, hB⟩ :=
    RiemannianSurfaceOrientation.exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage
      O b p hBImage
  have hcoord := O.controlledChartSign_eq_coordChange_det_pos
    a b p hpa hpb hA hB hsign
  have hdet : LinearMap.det
      (((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b) p).toLinearEquiv : E →ₗ[ℝ] E) =
      D.det := by
    simpa only [I, E, p, D] using
      (trivialization_coordChange_det_eq_fderivWithin_extChartAt_transition_det
        a b hz)
  rw [hdet] at hcoord
  exact hcoord

/-- Opposite conventional controlled-chart signs force a negative determinant
for an extended-chart transition when its source point is represented in the
selected controlled image of each chart. -/
theorem RiemannianSurfaceOrientation.controlledChartSign_eq_neg_transition_det_neg
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hAImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart a ''
        chosenControlledHalfSpaceComplexChartDomain a)
    (hBImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart b ''
        chosenControlledHalfSpaceComplexChartDomain b)
    (hsign : O.controlledChartSign a = -O.controlledChartSign b) :
    (fderivWithin ℝ
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z).det < 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  let p : M := (extChartAt I a).symm z
  let D : E →L[ℝ] E :=
    fderivWithin ℝ
      (extChartAt I b ∘ (extChartAt I a).symm)
      ((extChartAt I a).symm ≫ extChartAt I b).source z
  change z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source at hz
  change p ∈ halfSpaceComplexExtChart a ''
    chosenControlledHalfSpaceComplexChartDomain a at hAImage
  change p ∈ halfSpaceComplexExtChart b ''
    chosenControlledHalfSpaceComplexChartDomain b at hBImage
  change D.det < 0
  obtain ⟨hpa, hA⟩ :=
    RiemannianSurfaceOrientation.exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage
      O a p hAImage
  obtain ⟨hpb, hB⟩ :=
    RiemannianSurfaceOrientation.exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage
      O b p hBImage
  have hcoord := O.controlledChartSign_eq_neg_coordChange_det_neg
    a b p hpa hpb hA hB hsign
  have hdet : LinearMap.det
      (((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b) p).toLinearEquiv : E →ₗ[ℝ] E) =
      D.det := by
    simpa only [I, E, p, D] using
      (trivialization_coordChange_det_eq_fderivWithin_extChartAt_transition_det
        a b hz)
  rw [hdet] at hcoord
  exact hcoord

#print axioms RiemannianSurfaceOrientation.controlledChartSign_eq_transition_det_pos
#print axioms RiemannianSurfaceOrientation.controlledChartSign_eq_neg_transition_det_neg

end

end GromovFilling
