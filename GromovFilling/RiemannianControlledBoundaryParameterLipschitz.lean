import GromovFilling.RiemannianControlledBoundaryParameter
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Lipschitz real lifts of controlled boundary parameters

The quantitative inverse-chart control makes the canonical circle parameter
Lipschitz wherever a controlled boundary cutoff stays nonzero.  A continuous
real lift is then locally Lipschitz because the quotient map `ℝ → ℝ/ℤ` is an
isometry on intervals of radius at most one half.  Compactness upgrades this
to a single Lipschitz constant on a closed interval, and hence to absolute
continuity.
-/

open Bundle Filter Function Manifold Metric Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance controlledBoundaryParameterLipschitzEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- On any set where a controlled cutoff stays nonzero, the canonical
boundary parameter is Lipschitz.  The constant is the controlled inverse-chart
constant divided by the metric circumference factor `2π`. -/
theorem exists_lipschitzOnWith_controlledBoundaryChartParameter_of_cutoff_ne_zero
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (s : Set ℝ)
    (hcutoff : ∀ y ∈ s,
      controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (controlledBoundaryChartParameter boundary P i) s := by
  let c := chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) (P.center i)
  let K : ℝ := (c.C : ℝ) / (2 * Real.pi)
  refine ⟨Real.toNNReal K, LipschitzOnWith.of_dist_le' ?_⟩
  intro y hy z hz
  have hyCutoff := hcutoff y hy
  have hzCutoff := hcutoff z hz
  have hyInner : (y * Complex.I : ℂ) ∈
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) :=
    support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
      P i ⟨hyCutoff, real_mul_I_mem_complexRightClosedHalfPlane y⟩
  have hzInner : (z * Complex.I : ℂ) ∈
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) :=
    support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
      P i ⟨hzCutoff, real_mul_I_mem_complexRightClosedHalfPlane z⟩
  have hyOuter : (y * Complex.I : ℂ) ∈
      controlledHalfSpaceOuterClosedHalfBall (P.center i) :=
    controlledHalfSpaceInnerClosedBall_inter_rightClosed_subset_outerClosed
      (P.center i)
      ⟨hyInner, real_mul_I_mem_complexRightClosedHalfPlane y⟩
  have hzOuter : (z * Complex.I : ℂ) ∈
      controlledHalfSpaceOuterClosedHalfBall (P.center i) :=
    controlledHalfSpaceInnerClosedBall_inter_rightClosed_subset_outerClosed
      (P.center i)
      ⟨hzInner, real_mul_I_mem_complexRightClosedHalfPlane z⟩
  have hyControlled : (y * Complex.I : ℂ) ∈
      controlledHalfSpaceComplexChartDomain c := by
    simpa only [c, chosenControlledHalfSpaceComplexChartDomain] using
      controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain
        (P.center i) hyOuter
  have hzControlled : (z * Complex.I : ℂ) ∈
      controlledHalfSpaceComplexChartDomain c := by
    simpa only [c, chosenControlledHalfSpaceComplexChartDomain] using
      controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain
        (P.center i) hzOuter
  have hchartBound :
      dist
          (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
          (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) ≤
        (c.C : ℝ) * dist (y * Complex.I : ℂ) (z * Complex.I) :=
    (lipschitzOnWith_controlledHalfSpaceComplexChart c).dist_le_mul
      (y * Complex.I) hyControlled (z * Complex.I) hzControlled
  have hmetric := hboundary
    (controlledBoundaryChartParameter boundary P i y)
    (controlledBoundaryChartParameter boundary P i z)
  rw [boundary_controlledBoundaryChartParameter_of_cutoff_ne_zero
      boundary hboundaryRange P i y hyCutoff,
    boundary_controlledBoundaryChartParameter_of_cutoff_ne_zero
      boundary hboundaryRange P i z hzCutoff] at hmetric
  have hpi : 0 < (2 * Real.pi : ℝ) :=
    mul_pos (by norm_num) Real.pi_pos
  have hparameterEq :
      dist (controlledBoundaryChartParameter boundary P i y)
          (controlledBoundaryChartParameter boundary P i z) =
        dist
            (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
            (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) /
          (2 * Real.pi) := by
    apply (eq_div_iff hpi.ne').2
    calc
      dist (controlledBoundaryChartParameter boundary P i y)
            (controlledBoundaryChartParameter boundary P i z) *
          (2 * Real.pi) =
          (2 * Real.pi) *
            dist (controlledBoundaryChartParameter boundary P i y)
              (controlledBoundaryChartParameter boundary P i z) := by ring
      _ = dist
          (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
          (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) :=
        hmetric.symm
  have haxisDist :
      dist (y * Complex.I : ℂ) (z * Complex.I) = dist y z := by
    rw [Complex.dist_of_re_eq (by simp)]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
  calc
    dist (controlledBoundaryChartParameter boundary P i y)
        (controlledBoundaryChartParameter boundary P i z) =
        dist
            (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
            (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) /
          (2 * Real.pi) := hparameterEq
    _ ≤ ((c.C : ℝ) * dist (y * Complex.I : ℂ) (z * Complex.I)) /
          (2 * Real.pi) :=
      div_le_div_of_nonneg_right hchartBound hpi.le
    _ = K * dist y z := by
      rw [haxisDist]
      dsimp only [K]
      ring

/-- A continuous real lift of a Lipschitz circle-valued map is locally
Lipschitz on the set where it projects to that map. -/
private theorem locallyLipschitzOn_real_lift_of_lipschitzOnWith_projection
    {s : Set ℝ} {parameter : ℝ → UnitAddCircle} {lift : ℝ → ℝ}
    {K : ℝ≥0}
    (hliftContinuous : Continuous lift)
    (hliftProject : ∀ y ∈ s, ((lift y : ℝ) : UnitAddCircle) = parameter y)
    (hparameter : LipschitzOnWith K parameter s) :
    LocallyLipschitzOn s lift := by
  intro x hx
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  let t : Set ℝ :=
    s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ)
  refine ⟨K, t, ?_, ?_⟩
  · exact inter_mem_nhdsWithin s
      (hliftContinuous.continuousAt
        (Metric.ball_mem_nhds (lift x) hquarter))
  · apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    change y ∈ s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ) at hy
    change z ∈ s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ) at hz
    have hyDist : dist (lift y) (lift x) < (1 / 4 : ℝ) :=
      Metric.mem_ball.mp hy.2
    have hzDist : dist (lift z) (lift x) < (1 / 4 : ℝ) :=
      Metric.mem_ball.mp hz.2
    have hyzDist : dist (lift y) (lift z) < (1 / 2 : ℝ) := by
      calc
        dist (lift y) (lift z) ≤
            dist (lift y) (lift x) + dist (lift x) (lift z) :=
          dist_triangle _ _ _
        _ < (1 / 4 : ℝ) + 1 / 4 := by
          apply add_lt_add hyDist
          simpa only [dist_comm] using hzDist
        _ = 1 / 2 := by norm_num
    have hhalf : |lift y - lift z| ≤ (1 / 2 : ℝ) := by
      rw [← Real.dist_eq]
      exact hyzDist.le
    calc
      dist (lift y) (lift z) = |lift y - lift z| := Real.dist_eq _ _
      _ = ‖((lift y - lift z : ℝ) : UnitAddCircle)‖ :=
        ((AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2
          (by simpa only [abs_one] using hhalf)).symm
      _ = dist (((lift y : ℝ) : UnitAddCircle))
          (((lift z : ℝ) : UnitAddCircle)) := by
        rw [dist_eq_norm, ← AddCircle.coe_sub]
      _ = dist (parameter y) (parameter z) := by
        rw [hliftProject y hy.1, hliftProject z hz.1]
      _ ≤ (K : ℝ) * dist y z :=
        hparameter.dist_le_mul y hy.1 z hz.1

/-- On a compact nonzero chart-axis interval, the canonical parameter has a
real lift that is globally Lipschitz, absolutely continuous, and strictly
increasing or strictly decreasing. -/
theorem exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_on_Icc
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (a b : ℝ) (hab : a ≤ b)
    (hcutoff : ∀ y ∈ Set.Icc a b,
      controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0) :
    ∃ C : ℝ≥0, ∃ lift : ℝ → ℝ,
      Continuous lift ∧
      LipschitzOnWith C lift (Set.Icc a b) ∧
      AbsolutelyContinuousOnInterval lift a b ∧
      (∀ y ∈ Set.Icc a b,
        ((lift y : ℝ) : UnitAddCircle) =
          controlledBoundaryChartParameter boundary P i y) ∧
      (StrictMonoOn lift (Set.Icc a b) ∨
        StrictAntiOn lift (Set.Icc a b)) := by
  obtain ⟨lift, hliftContinuous, hliftProject⟩ :=
    exists_continuous_real_lift_controlledBoundaryChartParameter_on_Icc
      boundary hboundary hboundaryRange P i a b hab hcutoff
  obtain ⟨Kparameter, hparameter⟩ :=
    exists_lipschitzOnWith_controlledBoundaryChartParameter_of_cutoff_ne_zero
      boundary hboundary hboundaryRange P i (Set.Icc a b) hcutoff
  have hliftLocallyLipschitz : LocallyLipschitzOn (Set.Icc a b) lift :=
    locallyLipschitzOn_real_lift_of_lipschitzOnWith_projection
      hliftContinuous hliftProject hparameter
  obtain ⟨Klift, hliftLipschitz⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc hliftLocallyLipschitz
  have hliftAbsolutelyContinuous :
      AbsolutelyContinuousOnInterval lift a b := by
    have hliftLipschitzUIcc :
        LipschitzOnWith Klift lift (Set.uIcc a b) := by
      simpa only [Set.uIcc_of_le hab] using hliftLipschitz
    exact hliftLipschitzUIcc.absolutelyContinuousOnInterval
  have hparameterInjective : Set.InjOn
      (controlledBoundaryChartParameter boundary P i) (Set.Icc a b) :=
    injOn_controlledBoundaryChartParameter_of_cutoff_ne_zero
      boundary hboundaryRange P i (Set.Icc a b) hcutoff
  have hliftInjective : Set.InjOn lift (Set.Icc a b) := by
    intro y hy z hz hyz
    apply hparameterInjective hy hz
    calc
      controlledBoundaryChartParameter boundary P i y =
          ((lift y : ℝ) : UnitAddCircle) := (hliftProject y hy).symm
      _ = ((lift z : ℝ) : UnitAddCircle) :=
        congrArg (fun r : ℝ ↦ (r : UnitAddCircle)) hyz
      _ = controlledBoundaryChartParameter boundary P i z :=
        hliftProject z hz
  refine ⟨Klift, lift, hliftContinuous, hliftLipschitz,
    hliftAbsolutelyContinuous, hliftProject, ?_⟩
  exact hliftContinuous.continuousOn.strictMonoOn_of_injOn_Icc'
    hab hliftInjective

#print axioms
  exists_lipschitzOnWith_controlledBoundaryChartParameter_of_cutoff_ne_zero
#print axioms
  exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_on_Icc

end

end GromovFilling
