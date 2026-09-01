import GromovFilling.RiemannianHalfSpaceChartControl
import GromovFilling.RiemannianHalfSpaceChartTransitionAxis

/-!
# Common controlled boundary-axis intervals for half-space chart transitions

At an overlapping boundary-axis point, two selected controlled half-space
chart domains contain a common short interval of the boundary axis.  The
interval stays in the transition source, its image stays in the second
controlled domain, and the transition preserves the boundary axis there.

This is the local domain-control ingredient for comparing boundary directions
through overlapping charts.  It makes no orientation assertion.
-/

open Bundle Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

/-- At a common boundary-axis point of two controlled half-space charts, a
short closed axis interval remains in both controlled domains under the
extended-chart transition. -/
theorem exists_commonControlledAxisInterval
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    (a b : M)
    (ca : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) a)
    (cb : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) b)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (hzA : z ∈ controlledHalfSpaceChartSet ca)
    (hzB : ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm) z) ∈
        controlledHalfSpaceChartSet cb) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
      z + t • EuclideanSpace.single 1 (1 : ℝ) ∈
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source ∧
      z + t • EuclideanSpace.single 1 (1 : ℝ) ∈
        controlledHalfSpaceChartSet ca ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (z + t • EuclideanSpace.single 1 (1 : ℝ))) ∈
          controlledHalfSpaceChartSet cb ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (z + t • EuclideanSpace.single 1 (1 : ℝ))) 0 = 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let phi : PartialEquiv (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) :=
    (extChartAt I a).symm ≫ extChartAt I b
  let s : Set (EuclideanSpace ℝ (Fin 2)) := phi.source
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  change z ∈ s at hz
  change z ∈ Metric.ball (extChartAt I a a) ca.r ∩ Set.range I at hzA
  change T z ∈ Metric.ball (extChartAt I b b) cb.r ∩ Set.range I at hzB
  change ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
    z + t • e1 ∈ s ∧
      z + t • e1 ∈ Metric.ball (extChartAt I a a) ca.r ∩ Set.range I ∧
      T (z + t • e1) ∈ Metric.ball (extChartAt I b b) cb.r ∩ Set.range I ∧
      (T (z + t • e1)) 0 = 0
  obtain ⟨r0, hr0, haxisInterval⟩ :=
    exists_axis_interval_subset_extChartAt_transition_source a b
      (by simpa only [I, phi, s] using hz) hzAxis
  have hTcont : ContinuousOn T s := by
    simpa only [I, T, s, phi, Function.comp_def] using
      (contDiffOn_ext_coord_change (n := 1) b a).continuousOn
  obtain ⟨epsA, hepsA, hballA⟩ := Metric.mem_nhds_iff.mp
    (isOpen_ball.mem_nhds hzA.1)
  obtain ⟨epsB, hepsB, hballB⟩ := Metric.mem_nhds_iff.mp
    (isOpen_ball.mem_nhds hzB.1)
  have hTpre : T ⁻¹' Metric.ball (T z) epsB ∈ 𝓝[s] z :=
    (hTcont z hz).preimage_mem_nhdsWithin
      (Metric.ball_mem_nhds _ hepsB)
  obtain ⟨epsT, hepsT, hballT⟩ := Metric.mem_nhdsWithin_iff.mp hTpre
  let r : ℝ := min r0 (min (epsA / 2) (epsT / 2))
  have hrle0 : r ≤ r0 := by
    dsimp only [r]
    exact min_le_left _ _
  have hrleA : r ≤ epsA / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrleT : r ≤ epsT / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hr0 (lt_min (by linarith) (by linarith))
  refine ⟨r, hr, ?_⟩
  intro t ht
  rcases ht with ⟨htL, htR⟩
  have ht0 : t ∈ Set.Icc (-r0) r0 := by
    constructor <;> linarith
  have htAbsA : |t| < epsA := by
    rw [abs_lt]
    constructor <;> linarith
  have htAbsT : |t| < epsT := by
    rw [abs_lt]
    constructor <;> linarith
  have hshiftA : z + t • e1 ∈ Metric.ball z epsA := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, PiLp.norm_single]
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using htAbsA
  have hshiftT : z + t • e1 ∈ Metric.ball z epsT := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, PiLp.norm_single]
    simpa only [Real.norm_eq_abs, norm_one, mul_one] using htAbsT
  have hsource : z + t • e1 ∈ s := by
    simpa only [I, phi, s, e1] using (haxisInterval t ht0).1
  have haxis : (T (z + t • e1)) 0 = 0 := by
    simpa only [I, T, e1, Function.comp_apply] using
      (haxisInterval t ht0).2
  have hsourceAxis : (z + t • e1) 0 = 0 := by
    simp [e1, PiLp.add_apply, PiLp.smul_apply, hzAxis]
  have hA : z + t • e1 ∈
      Metric.ball (extChartAt I a a) ca.r ∩ Set.range I := by
    refine ⟨hballA hshiftA, ?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    simpa [hsourceAxis]
  have hTnear : T (z + t • e1) ∈ Metric.ball (T z) epsB :=
    hballT ⟨hshiftT, hsource⟩
  have hB : T (z + t • e1) ∈
      Metric.ball (extChartAt I b b) cb.r ∩ Set.range I := by
    refine ⟨hballB hTnear, ?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    simpa [haxis]
  exact ⟨hsource, hA, hB, haxis⟩

#print axioms exists_commonControlledAxisInterval

end

end GromovFilling
