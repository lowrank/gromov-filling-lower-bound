import GromovFilling.RiemannianHalfSpaceChartTransition

/-!
# Determinant signs of boundary chart transitions

At a boundary-axis point, a half-space chart transition has strictly positive
inward-normal derivative and no normal component in the tangent direction.
This module records the resulting two-dimensional determinant calculation:
the sign of the transition determinant is exactly the sign of its tangential
coefficient.

It contains no conventional-orientation comparison or global boundary
orientation assertion.
-/

open Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

private theorem det_eq_normal_mul_tangent
    (D : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2))
    (h_tangent_normal :
      (D (EuclideanSpace.single 1 (1 : ℝ))) 0 = 0) :
    D.det =
      (D (EuclideanSpace.single 0 (1 : ℝ))) 0 *
        (D (EuclideanSpace.single 1 (1 : ℝ))) 1 := by
  change LinearMap.det D.toLinearMap = _
  rw [show LinearMap.det D.toLinearMap =
      (LinearMap.toMatrix
        (PiLp.basisFun 2 ℝ (Fin 2))
        (PiLp.basisFun 2 ℝ (Fin 2))
        D.toLinearMap).det from
    (LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2))
      D.toLinearMap).symm]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, h_tangent_normal]

private theorem det_pos_iff_tangent_pos
    (D : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2))
    (h_tangent_normal :
      (D (EuclideanSpace.single 1 (1 : ℝ))) 0 = 0)
    (h_normal_pos :
      0 < (D (EuclideanSpace.single 0 (1 : ℝ))) 0) :
    0 < D.det ↔
      0 < (D (EuclideanSpace.single 1 (1 : ℝ))) 1 := by
  rw [det_eq_normal_mul_tangent D h_tangent_normal,
    mul_pos_iff_of_pos_left h_normal_pos]

private theorem det_neg_iff_tangent_neg
    (D : EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2))
    (h_tangent_normal :
      (D (EuclideanSpace.single 1 (1 : ℝ))) 0 = 0)
    (h_normal_pos :
      0 < (D (EuclideanSpace.single 0 (1 : ℝ))) 0) :
    D.det < 0 ↔
      (D (EuclideanSpace.single 1 (1 : ℝ))) 1 < 0 := by
  rw [det_eq_normal_mul_tangent D h_tangent_normal]
  constructor
  · intro h
    have h' :
        (D (EuclideanSpace.single 0 (1 : ℝ))) 0 *
            (D (EuclideanSpace.single 1 (1 : ℝ))) 1 <
          (D (EuclideanSpace.single 0 (1 : ℝ))) 0 * 0 := by
      simpa using h
    exact (mul_lt_mul_iff_right₀ h_normal_pos).mp h'
  · intro h
    have h' :
        (D (EuclideanSpace.single 0 (1 : ℝ))) 0 *
            (D (EuclideanSpace.single 1 (1 : ℝ))) 1 <
          (D (EuclideanSpace.single 0 (1 : ℝ))) 0 * 0 :=
      (mul_lt_mul_iff_right₀ h_normal_pos).mpr h
    simpa using h'

/-- At a boundary-axis point, the determinant of a half-space chart
transition is positive exactly when its tangential derivative is positive. -/
theorem fderivWithin_extChartAt_axis_transition_det_pos_iff_tangent_pos
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    0 < (fderivWithin ℝ
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z).det ↔
      0 < (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let s : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((extChartAt I a).symm ≫ extChartAt I b).source
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fderivWithin ℝ T s z
  let e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1 : ℝ)
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  change 0 < D.det ↔ 0 < (D e1) 1
  apply det_pos_iff_tangent_pos
  · simpa [D, T, s, e1] using
      fderivWithin_extChartAt_axis_transition_tangent_normal_eq_zero
        a b hz hzAxis
  · simpa [D, T, s, e0] using
      fderivWithin_extChartAt_axis_transition_normal_normal_pos
        a b hz hzAxis

/-- At a boundary-axis point, the determinant of a half-space chart
transition is negative exactly when its tangential derivative is negative. -/
theorem fderivWithin_extChartAt_axis_transition_det_neg_iff_tangent_neg
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    (fderivWithin ℝ
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z).det < 0 ↔
      (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1 < 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let s : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((extChartAt I a).symm ≫ extChartAt I b).source
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fderivWithin ℝ T s z
  let e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1 : ℝ)
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  change D.det < 0 ↔ (D e1) 1 < 0
  apply det_neg_iff_tangent_neg
  · simpa [D, T, s, e1] using
      fderivWithin_extChartAt_axis_transition_tangent_normal_eq_zero
        a b hz hzAxis
  · simpa [D, T, s, e0] using
      fderivWithin_extChartAt_axis_transition_normal_normal_pos
        a b hz hzAxis

#print axioms fderivWithin_extChartAt_axis_transition_det_pos_iff_tangent_pos
#print axioms fderivWithin_extChartAt_axis_transition_det_neg_iff_tangent_neg

end

end GromovFilling
