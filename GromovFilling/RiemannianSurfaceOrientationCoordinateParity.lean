import GromovFilling.RiemannianSurfaceOrientationConversion
import GromovFilling.RiemannianSurfaceOrientationOverlap

/-!
# Conventional chart signs and tangent-coordinate determinants

A conventional orientation gives a sign at each controlled chart center.  On
an overlap, the tangent-bundle coordinate change preserves the center
orientation when those signs agree and reverses it when they are opposite.
This module turns that orientation statement into determinant signs.  It is
purely local: it contains no boundary-axis, monotonicity, or global
induced-boundary assertion.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianSurfaceOrientationCoordinateParityEuclideanFinrankTwo :
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

/-- Equal conventional controlled chart signs force a positive determinant
for the tangent-coordinate change on any overlap where both local
orientations are identified with their chart centers. -/
theorem RiemannianSurfaceOrientation.controlledChartSign_eq_coordChange_det_pos
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b p : M)
    (hpa : p ∈ (chartAt (EuclideanHalfSpace 2) a).source)
    (hpb : p ∈ (chartAt (EuclideanHalfSpace 2) b).source)
    (hA : RiemannianSurfaceOrientation.trivializedOrientationAt O a ⟨p, hpa⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩)
    (hB : RiemannianSurfaceOrientation.trivializedOrientationAt O b ⟨p, hpb⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩)
    (hsign : O.controlledChartSign a = O.controlledChartSign b) :
    0 < LinearMap.det
      (((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b) p).toLinearEquiv :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  let e : E ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) a).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b) p
  change 0 < LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E)
  have htransport := O.center_trivializedOrientationAt_coordChange
    a b p hpa hpb hA hB
  change Orientation.map (Fin 2) e.toLinearEquiv
      (RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩) =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩ at htransport
  rcases O.controlledChartSign_eq_one_or_neg_one a with ha | ha <;>
    rcases O.controlledChartSign_eq_one_or_neg_one b with hb | hb
  · have hA0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
        O a ha
    have hB0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
        O b hb
    rw [hA0, hB0] at htransport
    exact (Orientation.map_eq_iff_det_pos halfSpaceComplexCoordinateOrientation
      e.toLinearEquiv (by simp)).mp htransport
  · rw [ha, hb] at hsign
    norm_num at hsign
  · rw [ha, hb] at hsign
    norm_num at hsign
  · have hA0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
        O a ha
    have hB0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
        O b hb
    rw [hA0, hB0, Orientation.map_neg] at htransport
    have hmap : Orientation.map (Fin 2) e.toLinearEquiv
        halfSpaceComplexCoordinateOrientation = halfSpaceComplexCoordinateOrientation :=
      neg_injective htransport
    exact (Orientation.map_eq_iff_det_pos halfSpaceComplexCoordinateOrientation
      e.toLinearEquiv (by simp)).mp hmap

/-- Opposite conventional controlled chart signs force a negative determinant
for the tangent-coordinate change on any overlap where both local
orientations are identified with their chart centers. -/
theorem RiemannianSurfaceOrientation.controlledChartSign_eq_neg_coordChange_det_neg
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b p : M)
    (hpa : p ∈ (chartAt (EuclideanHalfSpace 2) a).source)
    (hpb : p ∈ (chartAt (EuclideanHalfSpace 2) b).source)
    (hA : RiemannianSurfaceOrientation.trivializedOrientationAt O a ⟨p, hpa⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩)
    (hB : RiemannianSurfaceOrientation.trivializedOrientationAt O b ⟨p, hpb⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩)
    (hsign : O.controlledChartSign a = -O.controlledChartSign b) :
    LinearMap.det
      (((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b) p).toLinearEquiv :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) < 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  let e : E ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) a).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b) p
  change LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E) < 0
  have htransport := O.center_trivializedOrientationAt_coordChange
    a b p hpa hpb hA hB
  change Orientation.map (Fin 2) e.toLinearEquiv
      (RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩) =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩ at htransport
  rcases O.controlledChartSign_eq_one_or_neg_one a with ha | ha <;>
    rcases O.controlledChartSign_eq_one_or_neg_one b with hb | hb
  · rw [ha, hb] at hsign
    norm_num at hsign
  · have hA0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
        O a ha
    have hB0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
        O b hb
    rw [hA0, hB0] at htransport
    exact (Orientation.map_eq_neg_iff_det_neg halfSpaceComplexCoordinateOrientation
      e.toLinearEquiv (by simp)).mp htransport
  · have hA0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
        O a ha
    have hB0 :=
      RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
        O b hb
    rw [hA0, hB0, Orientation.map_neg] at htransport
    have hmap : Orientation.map (Fin 2) e.toLinearEquiv
        halfSpaceComplexCoordinateOrientation = -halfSpaceComplexCoordinateOrientation := by
      have hneg : -(-Orientation.map (Fin 2) e.toLinearEquiv
          halfSpaceComplexCoordinateOrientation) = -halfSpaceComplexCoordinateOrientation :=
        congrArg (fun q : Orientation ℝ E (Fin 2) => -q) htransport
      simpa only [neg_neg] using hneg
    exact (Orientation.map_eq_neg_iff_det_neg halfSpaceComplexCoordinateOrientation
      e.toLinearEquiv (by simp)).mp hmap
  · rw [ha, hb] at hsign
    norm_num at hsign

#print axioms
  RiemannianSurfaceOrientation.controlledChartSign_eq_coordChange_det_pos
#print axioms
  RiemannianSurfaceOrientation.controlledChartSign_eq_neg_coordChange_det_neg

end

end GromovFilling
