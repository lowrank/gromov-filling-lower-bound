import GromovFilling.RiemannianHalfSpaceChartTransitionTangent
import GromovFilling.RiemannianSurfaceOrientationOverlap

/-!
# Tangent-trivialization determinants for half-space chart transitions

The derivative of an extended half-space chart transition agrees on its
actual overlap source with the tangent-bundle coordinate change.  This module
records the equality of their determinants.  It contains no orientation,
boundary-axis, or global boundary-direction assertion.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- On an overlap of two extended half-space charts, the determinant of the
tangent-bundle coordinate change is the determinant of the derivative used
by the boundary-transition layer. -/
theorem trivialization_coordChange_det_eq_fderivWithin_extChartAt_transition_det
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source) :
    LinearMap.det
      (((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z)).toLinearEquiv :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) =
      (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z).det := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  change z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source at hz
  change LinearMap.det
      (((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b)
        ((extChartAt I a).symm z)).toLinearEquiv : E →ₗ[ℝ] E) =
      LinearMap.det
        (fderivWithin ℝ
          (extChartAt I b ∘ (extChartAt I a).symm)
          ((extChartAt I a).symm ≫ extChartAt I b).source z : E →ₗ[ℝ] E)
  have hzSplit : z ∈ (extChartAt I a).target ∧
      (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  have hpa : (extChartAt I a).symm z ∈
      (chartAt (EuclideanHalfSpace 2) a).source := by
    have hpAExt : (extChartAt I a).symm z ∈ (extChartAt I a).source :=
      (extChartAt I a).map_target hzSplit.1
    simpa only [extChartAt_source] using hpAExt
  have hpb : (extChartAt I a).symm z ∈
      (chartAt (EuclideanHalfSpace 2) b).source := by
    simpa only [extChartAt_source] using hzSplit.2
  have hcoord :
      (((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b)
        ((extChartAt I a).symm z)).toLinearEquiv : E →ₗ[ℝ] E) =
      (tangentCoordChange I a b ((extChartAt I a).symm z) : E →ₗ[ℝ] E) := by
    apply LinearMap.ext
    intro v
    simpa only [I] using
      (trivialization_coordChange_apply_eq_tangentCoordChange
        a b ((extChartAt I a).symm z) hpa hpb v)
  have hderivCLM :
      fderivWithin ℝ
        (extChartAt I b ∘ (extChartAt I a).symm)
        ((extChartAt I a).symm ≫ extChartAt I b).source z =
      tangentCoordChange I a b ((extChartAt I a).symm z) := by
    simpa only [I] using
      (fderivWithin_extChartAt_transition_eq_tangentCoordChange a b hz)
  have hderiv :
      (fderivWithin ℝ
        (extChartAt I b ∘ (extChartAt I a).symm)
        ((extChartAt I a).symm ≫ extChartAt I b).source z : E →ₗ[ℝ] E) =
      (tangentCoordChange I a b ((extChartAt I a).symm z) : E →ₗ[ℝ] E) :=
    congrArg (fun L : E →L[ℝ] E => (L : E →ₗ[ℝ] E)) hderivCLM
  calc
    LinearMap.det
        (((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) b)
          ((extChartAt I a).symm z)).toLinearEquiv : E →ₗ[ℝ] E) =
        LinearMap.det
          (tangentCoordChange I a b ((extChartAt I a).symm z) : E →ₗ[ℝ] E) :=
      congrArg LinearMap.det hcoord
    _ = LinearMap.det
          (fderivWithin ℝ
            (extChartAt I b ∘ (extChartAt I a).symm)
            ((extChartAt I a).symm ≫ extChartAt I b).source z : E →ₗ[ℝ] E) :=
      congrArg LinearMap.det hderiv.symm

#print axioms
  trivialization_coordChange_det_eq_fderivWithin_extChartAt_transition_det

end

end GromovFilling
