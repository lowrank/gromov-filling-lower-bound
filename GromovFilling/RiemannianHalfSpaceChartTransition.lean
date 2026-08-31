import GromovFilling.RiemannianHalfSpaceChart
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Boundary axes under half-space chart transitions

An extended-chart transition between two charts of a manifold with boundary
preserves the model boundary face.  Its first derivative consequently
preserves the tangent boundary line and is nondegenerate along that line.
These are local ingredients for comparing induced boundary directions with
surface-orientation signs; the file contains no global orientation assertion.
-/

open Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

/-- If a point on the model boundary axis belongs to the source of two
extended charts, then its coordinate in the second chart is again on the
model boundary axis. -/
theorem extChartAt_axis_maps_to_axis
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).target)
    (hy : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      (chartAt (EuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) b
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z)) 0 = 0 := by
  let I := modelWithCornersEuclideanHalfSpace 2
  have hsourceAExt : (extChartAt I a).symm z ∈ (extChartAt I a).source :=
    (extChartAt I a).map_target hz
  have hsourceA : (extChartAt I a).symm z ∈ (chartAt (EuclideanHalfSpace 2) a).source := by
    simpa only [extChartAt_source] using hsourceAExt
  have hboundary : (extChartAt I a).symm z ∈ I.boundary M := by
    change I.IsBoundaryPoint ((extChartAt I a).symm z)
    rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (I := I) _]
    intro hinterior
    have hcoord : extChartAt I a ((extChartAt I a).symm z) ∈
        interior (extChartAt I a).target :=
      (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
        (chart_mem_atlas (EuclideanHalfSpace 2) a) hsourceA).mp hinterior
    rw [(extChartAt I a).right_inv hz] at hcoord
    have hrange : z ∈ interior (Set.range I) :=
      interior_mono (extChartAt_target_subset_range a) hcoord
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hrange
    have hpos : 0 < z 0 := by
      simpa only [mem_setOf_eq] using hrange
    rw [hzAxis] at hpos
    exact (lt_irrefl 0) hpos
  have hsourceBExt : (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [extChartAt_source] using hy
  have htargetB : extChartAt I b ((extChartAt I a).symm z) ∈
      (extChartAt I b).target :=
    (extChartAt I b).map_source hsourceBExt
  have hnonneg : 0 ≤ (extChartAt I b ((extChartAt I a).symm z)) 0 := by
    have hrange : extChartAt I b ((extChartAt I a).symm z) ∈ Set.range I :=
      extChartAt_target_subset_range b htargetB
    rw [range_modelWithCornersEuclideanHalfSpace] at hrange
    simpa only [mem_setOf_eq] using hrange
  apply le_antisymm ?_ hnonneg
  by_contra hnot
  have hpos : 0 < (extChartAt I b ((extChartAt I a).symm z)) 0 :=
    lt_of_not_ge hnot
  have hrangeInterior : extChartAt I b ((extChartAt I a).symm z) ∈
      interior (Set.range I) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa only [mem_setOf_eq] using hpos
  have htargetInterior : extChartAt I b ((extChartAt I a).symm z) ∈
      interior (extChartAt I b).target := by
    rw [interior_extChartAt_target_eq_inter_interior_range]
    exact ⟨htargetB, hrangeInterior⟩
  have hinterior : I.IsInteriorPoint ((extChartAt I a).symm z) :=
    (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
      (chart_mem_atlas (EuclideanHalfSpace 2) b) hy).mpr htargetInterior
  exact ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (I := I) _).mp
    hboundary) hinterior

/-- A smooth extended-chart transition preserves the tangent boundary line to
first order.  In the right-half-space model, its derivative sends the axis
direction to a vector with zero normal component. -/
theorem fderivWithin_extChartAt_axis_transition_tangent_normal_eq_zero
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
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
      (EuclideanSpace.single 1 (1 : ℝ))) 0 = 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let φ : PartialEquiv (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) :=
    (extChartAt I a).symm ≫ extChartAt I b
  let s : Set (EuclideanSpace ℝ (Fin 2)) := φ.source
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  change z ∈ s at hz
  change (fderivWithin ℝ T s z e1) 0 = 0
  have sourceMem (w : EuclideanSpace ℝ (Fin 2)) :
      w ∈ s ↔ w ∈ (extChartAt I a).target ∧
        (extChartAt I a).symm w ∈ (extChartAt I b).source := by
    simp only [s, φ, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
  have hzSplit := (sourceMem z).mp hz
  have hTaxis : (T z) 0 = 0 := by
    simpa only [T, Function.comp_apply] using
      extChartAt_axis_maps_to_axis a b hzSplit.1
        (by simpa only [extChartAt_source] using hzSplit.2) hzAxis
  have hnonneg : ∀ w ∈ s, 0 ≤ (T w) 0 := by
    intro w hw
    have hwSplit := (sourceMem w).mp hw
    have htarget : extChartAt I b ((extChartAt I a).symm w) ∈
        (extChartAt I b).target :=
      (extChartAt I b).map_source hwSplit.2
    have hrange : extChartAt I b ((extChartAt I a).symm w) ∈
        Set.range I := extChartAt_target_subset_range b htarget
    rw [range_modelWithCornersEuclideanHalfSpace] at hrange
    simpa only [T, Function.comp_apply, mem_setOf_eq] using hrange
  have hmin : IsLocalMinOn
      (fun w : EuclideanSpace ℝ (Fin 2) ↦ (T w) 0) s z := by
    apply IsMinOn.localize
    intro w hw
    rw [hTaxis]
    exact hnonneg w hw
  have hsNhds : s ∈ 𝓝[Set.range I] z := by
    change (I.extendCoordChange (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source ∈ 𝓝[Set.range I] z
    exact I.extendCoordChange_source_mem_nhdsWithin
      (e := chartAt (EuclideanHalfSpace 2) a)
      (e' := chartAt (EuclideanHalfSpace 2) b) hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hsNhds
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  have hδlt : δ < ε := by
    dsimp only [δ]
    linarith
  have hzRange : z ∈ Set.range I := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    simpa [hzAxis]
  have hplusRange : z + δ • e1 ∈ Set.range I := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp [e1, PiLp.add_apply, PiLp.smul_apply, hzAxis]
  have hminusRange : z + (-δ) • e1 ∈ Set.range I := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    simp [e1, PiLp.add_apply, PiLp.smul_apply, hzAxis]
  have hplusBall : z + δ • e1 ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, PiLp.norm_single]
    simpa only [Real.norm_eq_abs, abs_of_pos hδ, norm_one, mul_one] using hδlt
  have hminusBall : z + (-δ) • e1 ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, PiLp.norm_single]
    simpa only [Real.norm_eq_abs, abs_neg, abs_of_pos hδ, norm_one, mul_one] using hδlt
  have hconvex : Convex ℝ (Metric.ball z ε ∩ Set.range I) :=
    (convex_ball z ε).inter I.convex_range
  have hsegmentPlus : segment ℝ z (z + δ • e1) ⊆ s :=
    (hconvex.segment_subset ⟨mem_ball_self hε, hzRange⟩
      ⟨hplusBall, hplusRange⟩).trans hball
  have hsegmentMinus : segment ℝ z (z + (-δ) • e1) ⊆ s :=
    (hconvex.segment_subset ⟨mem_ball_self hε, hzRange⟩
      ⟨hminusBall, hminusRange⟩).trans hball
  have hconePlus : δ • e1 ∈ posTangentConeAt s z := by
    simpa only [add_sub_cancel_left] using
      sub_mem_posTangentConeAt_of_segment_subset hsegmentPlus
  have hconeMinus : -(δ • e1) ∈ posTangentConeAt s z := by
    simpa only [add_sub_cancel_left, neg_smul] using
      sub_mem_posTangentConeAt_of_segment_subset hsegmentMinus
  have hTderiv : HasFDerivWithinAt T (fderivWithin ℝ T s z) s z := by
    simpa only [I, T, s, φ, Function.comp_apply] using
      ((contDiffOn_ext_coord_change b a z hz).differentiableWithinAt
        one_ne_zero).hasFDerivWithinAt
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hpderiv : HasFDerivWithinAt
      (fun w : EuclideanSpace ℝ (Fin 2) ↦ (T w) 0)
      (p.comp (fderivWithin ℝ T s z)) s z := by
    simpa [p, Function.comp_apply] using
      p.hasFDerivAt.comp_hasFDerivWithinAt z hTderiv
  have hscaled : (p.comp (fderivWithin ℝ T s z)) (δ • e1) = 0 :=
    hmin.hasFDerivWithinAt_eq_zero hpderiv hconePlus hconeMinus
  have hscalar : δ * (fderivWithin ℝ T s z e1) 0 = 0 := by
    simpa [p, ContinuousLinearMap.comp_apply, PiLp.smul_apply, smul_eq_mul] using hscaled
  exact (mul_eq_zero.mp hscalar).resolve_left (ne_of_gt hδ)

/-- The tangential component of a smooth extended-chart transition is
nonzero on the boundary axis. -/
theorem fderivWithin_extChartAt_axis_transition_tangent_ne_zero
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
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
      (EuclideanSpace.single 1 (1 : ℝ))) 1 ≠ 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let s : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((extChartAt I a).symm ≫ extChartAt I b).source
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fderivWithin ℝ T s z
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  have hnormal :=
    fderivWithin_extChartAt_axis_transition_tangent_normal_eq_zero a b hz hzAxis
  have hzChange : z ∈ (I.extendCoordChange
      (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source := by
    change z ∈ (I.extendCoordChange (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source at hz
    exact hz
  have hInv0 := I.isInvertible_fderivWithin_extendCoordChange
    (e := chartAt (EuclideanHalfSpace 2) a)
    (e' := chartAt (EuclideanHalfSpace 2) b)
    one_ne_zero (chart_mem_maximalAtlas a) (chart_mem_maximalAtlas b) hzChange
  have hInv : D.IsInvertible := by
    simpa only [D, T, s, I, ModelWithCorners.extendCoordChange,
      extChartAt, Function.comp_apply] using hInv0
  intro hTan
  have hDzero : D e1 = 0 := by
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    exact ⟨by simpa [D, T, s, e1] using hnormal,
      by simpa [D, T, s, e1] using hTan⟩
  have hInj : Function.Injective D := hInv.injective
  have he1zero : e1 = 0 := hInj (by simpa using hDzero)
  have honezero : (1 : ℝ) = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v (1 : Fin 2)) he1zero
    simpa [e1] using h
  exact one_ne_zero honezero

#print axioms extChartAt_axis_maps_to_axis
#print axioms fderivWithin_extChartAt_axis_transition_tangent_normal_eq_zero
#print axioms fderivWithin_extChartAt_axis_transition_tangent_ne_zero

end

end GromovFilling
