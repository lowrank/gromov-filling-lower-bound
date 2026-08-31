import GromovFilling.RiemannianHalfSpaceChartTransition

/-!
# Boundary-axis neighborhoods for half-space chart transitions

An extended half-space chart transition is defined on a relative neighborhood
of each point in its overlap source.  At a boundary-axis point, that
neighborhood contains a closed interval of the boundary axis, and the
transition maps that interval back to the boundary axis.
-/

open Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

/-- Every boundary-axis point in an extended-chart transition source has a
closed boundary-axis interval inside that source, and the transition maps
the interval into the boundary axis. -/
theorem exists_axis_interval_subset_extChartAt_transition_source
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
      z + t • EuclideanSpace.single 1 (1 : ℝ) ∈
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (z + t • EuclideanSpace.single 1 (1 : ℝ))) 0 = 0 := by
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
  change ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
    z + t • e1 ∈ s ∧ (T (z + t • e1)) 0 = 0
  have hsNhds : s ∈ 𝓝[Set.range I] z := by
    change (I.extendCoordChange (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source ∈ 𝓝[Set.range I] z
    exact I.extendCoordChange_source_mem_nhdsWithin
      (e := chartAt (EuclideanHalfSpace 2) a)
      (e' := chartAt (EuclideanHalfSpace 2) b) hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hsNhds
  let r : ℝ := ε / 2
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have sourceMem (w : EuclideanSpace ℝ (Fin 2)) :
      w ∈ s ↔ w ∈ (extChartAt I a).target ∧
        (extChartAt I a).symm w ∈ (extChartAt I b).source := by
    simp only [s, φ, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
  refine ⟨r, hr, ?_⟩
  intro t ht
  rcases ht with ⟨htL, htR⟩
  have htL' : -(ε / 2) ≤ t := by
    simpa only [r] using htL
  have htR' : t ≤ ε / 2 := by
    simpa only [r] using htR
  have htAbs : |t| < ε := by
    rw [abs_lt]
    constructor <;> linarith
  have haxis : (z + t • e1) 0 = 0 := by
    simp [e1, PiLp.add_apply, PiLp.smul_apply, hzAxis]
  have hsource : z + t • e1 ∈ s := by
    apply hball
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        norm_smul, PiLp.norm_single]
      simpa only [Real.norm_eq_abs, norm_one, mul_one] using htAbs
    · rw [range_modelWithCornersEuclideanHalfSpace]
      simpa [haxis]
  refine ⟨hsource, ?_⟩
  have hsplit := (sourceMem _).mp hsource
  simpa only [T, Function.comp_apply] using
    extChartAt_axis_maps_to_axis a b hsplit.1
      (by simpa only [extChartAt_source] using hsplit.2) haxis

#print axioms exists_axis_interval_subset_extChartAt_transition_source

end

end GromovFilling
