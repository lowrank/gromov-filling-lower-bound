import GromovFilling.LocalizedWeakStokes
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lipschitz weak Stokes on a planar half-plane

This file turns localized whole-plane weak Stokes into a boundary formula.
The key device is the one-Lipschitz retraction `(x, y) ↦ (max x 0, y)`:
after precomposition, a half-plane map is constant in the exterior normal
direction.  A smooth step across the exterior strip therefore produces the
boundary action exactly, without a trace-limit argument.
-/

open Filter Function MeasureTheory Set
open scoped BigOperators ContDiff NNReal Pointwise Topology

namespace GromovFilling

noncomputable section

/-- Retraction of the plane onto the closed right half-plane. -/
def planarHalfPlaneRetraction (z : ℝ × ℝ) : ℝ × ℝ :=
  (max z.1 0, z.2)

/-- The planar half-plane retraction is one-Lipschitz. -/
theorem lipschitzWith_planarHalfPlaneRetraction :
    LipschitzWith 1 planarHalfPlaneRetraction := by
  simpa [planarHalfPlaneRetraction] using
    (LipschitzWith.prod_fst.max_const 0).prodMk LipschitzWith.prod_snd

/-- A fixed smooth step which is zero on `(-∞, -1]` and one on `[0, ∞)`. -/
def exteriorHalfPlaneStep (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1)

theorem exteriorHalfPlaneStep_eq_zero {x : ℝ} (hx : x ≤ -1) :
    exteriorHalfPlaneStep x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  dsimp only [exteriorHalfPlaneStep]
  linarith

theorem exteriorHalfPlaneStep_eq_one {x : ℝ} (hx : 0 ≤ x) :
    exteriorHalfPlaneStep x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  simpa [exteriorHalfPlaneStep] using add_le_add_right hx 1

theorem contDiff_exteriorHalfPlaneStep :
    ContDiff ℝ ∞ exteriorHalfPlaneStep := by
  exact Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

/-- The standard smooth transition is globally Lipschitz. -/
theorem exists_lipschitzWith_smoothTransition :
    ∃ C : ℝ≥0, LipschitzWith C Real.smoothTransition := by
  obtain ⟨C, hC⟩ :=
    ((Real.smoothTransition.contDiff.contDiffOn :
        ContDiffOn ℝ 1 Real.smoothTransition (Icc 0 1)).exists_lipschitzOnWith
      one_ne_zero (convex_Icc 0 1) isCompact_Icc)
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [← Real.smoothTransition.projIcc (x := x),
    ← Real.smoothTransition.projIcc (x := y)]
  have hproj : dist (↑(Set.projIcc 0 1 zero_le_one x) : ℝ)
      (↑(Set.projIcc 0 1 zero_le_one y) : ℝ) ≤ dist x y := by
    simpa using
      (LipschitzWith.projIcc zero_le_one).dist_le_mul x y
  exact (hC.dist_le_mul _ (Set.projIcc 0 1 zero_le_one x).property
    _ (Set.projIcc 0 1 zero_le_one y).property).trans
      (mul_le_mul_of_nonneg_left hproj C.coe_nonneg)

/-- The fixed exterior step is globally Lipschitz. -/
theorem exists_lipschitzWith_exteriorHalfPlaneStep :
    ∃ C : ℝ≥0, LipschitzWith C exteriorHalfPlaneStep := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_smoothTransition
  refine ⟨C, ?_⟩
  simpa [exteriorHalfPlaneStep, Function.comp_def] using
    hC.comp (LipschitzWith.id.add (LipschitzWith.const 1))

theorem deriv_exteriorHalfPlaneStep_eq_zero_of_lt_neg_one
    {x : ℝ} (hx : x < -1) :
    deriv exteriorHalfPlaneStep x = 0 := by
  have heq : exteriorHalfPlaneStep =ᶠ[𝓝 x] (fun _ : ℝ ↦ 0) := by
    filter_upwards [(Iio_mem_nhds hx)] with y hy
    exact exteriorHalfPlaneStep_eq_zero hy.le
  rw [heq.deriv_eq]
  simp

theorem deriv_exteriorHalfPlaneStep_eq_zero_of_pos
    {x : ℝ} (hx : 0 < x) :
    deriv exteriorHalfPlaneStep x = 0 := by
  have heq : exteriorHalfPlaneStep =ᶠ[𝓝 x] (fun _ : ℝ ↦ 1) := by
    filter_upwards [(Ioi_mem_nhds hx)] with y hy
    exact exteriorHalfPlaneStep_eq_one hy.le
  rw [heq.deriv_eq]
  simp

theorem hasCompactSupport_deriv_exteriorHalfPlaneStep :
    HasCompactSupport (deriv exteriorHalfPlaneStep) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 0))
  intro x hx
  rw [mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · exact deriv_exteriorHalfPlaneStep_eq_zero_of_lt_neg_one (lt_of_not_ge hx)
  · exact deriv_exteriorHalfPlaneStep_eq_zero_of_pos (lt_of_not_ge hx)

theorem integrable_deriv_exteriorHalfPlaneStep :
    Integrable (deriv exteriorHalfPlaneStep) := by
  exact Continuous.integrable_of_hasCompactSupport
    (contDiff_exteriorHalfPlaneStep.continuous_deriv (by simp))
    hasCompactSupport_deriv_exteriorHalfPlaneStep

/-- The derivative of the exterior step has total mass one on the exterior
half-line. -/
theorem integral_Iio_deriv_exteriorHalfPlaneStep :
    ∫ x in Iio (0 : ℝ), deriv exteriorHalfPlaneStep x = 1 := by
  have htendsto : Tendsto exteriorHalfPlaneStep atBot (𝓝 0) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Iic_mem_atBot (-1 : ℝ)] with x hx
    exact exteriorHalfPlaneStep_eq_zero hx
  have hFTC : ∫ x in Iic (0 : ℝ), deriv exteriorHalfPlaneStep x =
      exteriorHalfPlaneStep 0 - 0 :=
    integral_Iic_of_hasDerivAt_of_tendsto
    (a := 0) (m := 0) (f := exteriorHalfPlaneStep)
    (f' := deriv exteriorHalfPlaneStep)
    contDiff_exteriorHalfPlaneStep.continuous.continuousWithinAt
    (fun x _ ↦
      (contDiff_exteriorHalfPlaneStep.differentiable (by simp) x).hasDerivAt)
    integrable_deriv_exteriorHalfPlaneStep.integrableOn htendsto
  rw [setIntegral_congr_set (Iio_ae_eq_Iic :
    Iio (0 : ℝ) =ᵐ[volume] Iic 0), hFTC]
  norm_num [exteriorHalfPlaneStep]

/-- Constant-across-the-boundary extension obtained from the half-plane
retraction. -/
def halfPlaneConstantExtension {Y : Type*} (f : (ℝ × ℝ) → Y) :
    (ℝ × ℝ) → Y :=
  f ∘ planarHalfPlaneRetraction

theorem LipschitzWith.halfPlaneConstantExtension
    {Y : Type*} [PseudoEMetricSpace Y] {f : (ℝ × ℝ) → Y} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    LipschitzWith C (halfPlaneConstantExtension f) := by
  simpa [halfPlaneConstantExtension] using
    hf.comp lipschitzWith_planarHalfPlaneRetraction

theorem halfPlaneConstantExtension_eq_self
    {Y : Type*} (f : (ℝ × ℝ) → Y) {z : ℝ × ℝ} (hz : 0 ≤ z.1) :
    halfPlaneConstantExtension f z = f z := by
  simp [halfPlaneConstantExtension, planarHalfPlaneRetraction,
    max_eq_left hz]

theorem halfPlaneConstantExtension_eq_boundary
    {Y : Type*} (f : (ℝ × ℝ) → Y) {z : ℝ × ℝ} (hz : z.1 ≤ 0) :
    halfPlaneConstantExtension f z = f (0, z.2) := by
  simp [halfPlaneConstantExtension, planarHalfPlaneRetraction,
    max_eq_right hz]

/-- On the open half-plane, constant extension does not change any line
derivative. -/
theorem lineDeriv_halfPlaneConstantExtension_eq_self
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : (ℝ × ℝ) → Y) {z p : ℝ × ℝ} (hz : 0 < z.1) :
    lineDeriv ℝ (halfPlaneConstantExtension f) z p =
      lineDeriv ℝ f z p := by
  unfold lineDeriv
  apply Filter.EventuallyEq.deriv_eq
  have hret : halfPlaneConstantExtension f =ᶠ[𝓝 z] f := by
    have hright : {w : ℝ × ℝ | 0 < w.1} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hz
    filter_upwards [hright] with w hw
    exact halfPlaneConstantExtension_eq_self f hw.le
  have hpath : Tendsto (fun t : ℝ ↦ z + t • p) (𝓝 0) (𝓝 z) := by
    have hc : ContinuousAt (fun t : ℝ ↦ z + t • p) 0 :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    change Tendsto (fun t : ℝ ↦ z + t • p) (𝓝 0)
      (𝓝 ((fun t : ℝ ↦ z + t • p) 0)) at hc
    simpa only [zero_smul, add_zero] using hc
  exact hret.comp_tendsto hpath

/-- In the exterior open half-plane the constant extension has zero normal
line derivative, even when the boundary trace is only Lipschitz. -/
theorem lineDeriv_halfPlaneConstantExtension_normal_eq_zero
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : (ℝ × ℝ) → Y) {z : ℝ × ℝ} (hz : z.1 < 0) :
    lineDeriv ℝ (halfPlaneConstantExtension f) z (1, 0) = 0 := by
  unfold lineDeriv
  have hcurve :
      (fun t : ℝ ↦ halfPlaneConstantExtension f
        (z + t • (1, 0))) =ᶠ[𝓝 0]
      (fun _ : ℝ ↦ f (0, z.2)) := by
    have hnhds : Iio (-z.1) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by linarith)
    filter_upwards [hnhds] with t ht
    rw [halfPlaneConstantExtension_eq_boundary]
    · simp
    · norm_num
      change t < -z.1 at ht
      linarith [ht]
  rw [hcurve.deriv_eq]
  simp

/-- In the exterior open half-plane, the tangential line derivative is the
one-dimensional line derivative of the boundary trace. -/
theorem lineDeriv_halfPlaneConstantExtension_tangent_eq_boundary
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : (ℝ × ℝ) → Y) {z : ℝ × ℝ} (hz : z.1 < 0) :
    lineDeriv ℝ (halfPlaneConstantExtension f) z (0, 1) =
      lineDeriv ℝ (fun y : ℝ ↦ f (0, y)) z.2 1 := by
  unfold lineDeriv
  congr 1
  funext t
  rw [halfPlaneConstantExtension_eq_boundary]
  · simp
  · simpa using hz.le

/-- The compact cutoff used to expose the right-half-plane boundary. -/
def halfPlaneStokesCutoff (ρ : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) : ℝ :=
  exteriorHalfPlaneStep z.1 * halfPlaneConstantExtension ρ z

theorem halfPlaneStokesCutoff_eq_self
    (ρ : (ℝ × ℝ) → ℝ) {z : ℝ × ℝ} (hz : 0 ≤ z.1) :
    halfPlaneStokesCutoff ρ z = ρ z := by
  rw [halfPlaneStokesCutoff, exteriorHalfPlaneStep_eq_one hz,
    halfPlaneConstantExtension_eq_self ρ hz, one_mul]

theorem halfPlaneStokesCutoff_eq_exterior
    (ρ : (ℝ × ℝ) → ℝ) {z : ℝ × ℝ} (hz : z.1 ≤ 0) :
    halfPlaneStokesCutoff ρ z =
      exteriorHalfPlaneStep z.1 * ρ (0, z.2) := by
  rw [halfPlaneStokesCutoff,
    halfPlaneConstantExtension_eq_boundary ρ hz]

/-- The exterior-step cutoff is compactly supported whenever the original
half-plane cutoff is compactly supported. -/
theorem hasCompactSupport_halfPlaneStokesCutoff
    {ρ : (ℝ × ℝ) → ℝ} (hρCompact : HasCompactSupport ρ) :
    HasCompactSupport (halfPlaneStokesCutoff ρ) := by
  let K : Set (ℝ × ℝ) :=
    Metric.closedBall (0 : ℝ × ℝ) 1 + tsupport ρ
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℝ × ℝ) 1).add hρCompact.isCompact
  apply HasCompactSupport.intro hK
  intro z hzK
  by_contra hzNonzero
  have hstep : exteriorHalfPlaneStep z.1 ≠ 0 := by
    intro hzero
    exact hzNonzero (by simp [halfPlaneStokesCutoff, hzero])
  have hρ : ρ (planarHalfPlaneRetraction z) ≠ 0 := by
    intro hzero
    exact hzNonzero (by simp [halfPlaneStokesCutoff,
      halfPlaneConstantExtension, hzero])
  have hretSupport : planarHalfPlaneRetraction z ∈ tsupport ρ :=
    subset_tsupport ρ hρ
  have hx : -1 < z.1 := by
    by_contra h
    exact hstep (exteriorHalfPlaneStep_eq_zero (le_of_not_gt h))
  have hoffset : z - planarHalfPlaneRetraction z ∈
      Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : 0 ≤ z.1
    · simp [planarHalfPlaneRetraction, max_eq_left hz]
    · have hzneg : z.1 < 0 := lt_of_not_ge hz
      rw [show planarHalfPlaneRetraction z = (0, z.2) by
        simp [planarHalfPlaneRetraction, max_eq_right hzneg.le]]
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.norm_def, sub_zero,
        sub_self, norm_zero, Real.norm_eq_abs, abs_of_neg hzneg]
      rw [max_eq_left (by linarith)]
      linarith
  apply hzK
  refine ⟨z - planarHalfPlaneRetraction z, hoffset,
    planarHalfPlaneRetraction z, hretSupport, ?_⟩
  exact sub_add_cancel z (planarHalfPlaneRetraction z)

/-- The exterior-step cutoff is globally Lipschitz. -/
theorem exists_lipschitzWith_halfPlaneStokesCutoff
    {ρ : (ℝ × ℝ) → ℝ} {Cρ : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρCompact : HasCompactSupport ρ) :
    ∃ C, LipschitzWith C (halfPlaneStokesCutoff ρ) := by
  obtain ⟨Cs, hs⟩ := exists_lipschitzWith_exteriorHalfPlaneStep
  let s : (ℝ × ℝ) → ℝ := fun z ↦ exteriorHalfPlaneStep z.1
  let r : (ℝ × ℝ) → ℝ := halfPlaneConstantExtension ρ
  have hsPlane : LipschitzWith Cs s := by
    simpa only [s, Function.comp_apply, mul_one] using
      hs.comp LipschitzWith.prod_fst
  have hr : LipschitzWith Cρ r :=
    LipschitzWith.halfPlaneConstantExtension hρ
  obtain ⟨Bρ, hBρ⟩ :=
    hρ.continuous.bounded_above_of_compact_support hρCompact
  let L : ℝ := (Cρ : ℝ) + |Bρ| * (Cs : ℝ)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  refine ⟨Real.toNNReal L, LipschitzWith.of_dist_le' ?_⟩
  intro x y
  have hsBound (z : ℝ × ℝ) : |s z| ≤ 1 := by
    dsimp only [s, exteriorHalfPlaneStep]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hrBound (z : ℝ × ℝ) : |r z| ≤ |Bρ| := by
    calc
      |r z| = ‖ρ (planarHalfPlaneRetraction z)‖ := by
        simp [r, halfPlaneConstantExtension, Real.norm_eq_abs]
      _ ≤ Bρ := hBρ (planarHalfPlaneRetraction z)
      _ ≤ |Bρ| := le_abs_self Bρ
  have hsDist : |s x - s y| ≤ (Cs : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hsPlane.dist_le_mul x y
  have hrDist : |r x - r y| ≤ (Cρ : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hr.dist_le_mul x y
  rw [Real.dist_eq]
  change |s x * r x - s y * r y| ≤ L * dist x y
  calc
    |s x * r x - s y * r y| =
        |s x * (r x - r y) + r y * (s x - s y)| := by ring_nf
    _ ≤ |s x * (r x - r y)| + |r y * (s x - s y)| := abs_add_le _ _
    _ = |s x| * |r x - r y| + |r y| * |s x - s y| := by
      rw [abs_mul, abs_mul]
    _ ≤ |s x| * ((Cρ : ℝ) * dist x y) +
        |r y| * ((Cs : ℝ) * dist x y) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hrDist (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hsDist (abs_nonneg _))
    _ ≤ 1 * ((Cρ : ℝ) * dist x y) +
        |Bρ| * ((Cs : ℝ) * dist x y) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hsBound x)
          (mul_nonneg Cρ.coe_nonneg dist_nonneg))
        (mul_le_mul_of_nonneg_right (hrBound y)
          (mul_nonneg Cs.coe_nonneg dist_nonneg))
    _ = L * dist x y := by
      dsimp only [L]
      ring

/-- On the open half-plane, the step cutoff and all of its line derivatives
agree with the original cutoff. -/
theorem lineDeriv_halfPlaneStokesCutoff_eq_self
    (ρ : (ℝ × ℝ) → ℝ) {z p : ℝ × ℝ} (hz : 0 < z.1) :
    lineDeriv ℝ (halfPlaneStokesCutoff ρ) z p =
      lineDeriv ℝ ρ z p := by
  unfold lineDeriv
  apply Filter.EventuallyEq.deriv_eq
  have heq : halfPlaneStokesCutoff ρ =ᶠ[𝓝 z] ρ := by
    have hright : {w : ℝ × ℝ | 0 < w.1} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hz
    filter_upwards [hright] with w hw
    exact halfPlaneStokesCutoff_eq_self ρ hw.le
  have hpath : Tendsto (fun t : ℝ ↦ z + t • p) (𝓝 0) (𝓝 z) := by
    have hc : ContinuousAt (fun t : ℝ ↦ z + t • p) 0 :=
      continuousAt_const.add (continuousAt_id.smul continuousAt_const)
    change Tendsto (fun t : ℝ ↦ z + t • p) (𝓝 0)
      (𝓝 ((fun t : ℝ ↦ z + t • p) 0)) at hc
    simpa only [zero_smul, add_zero] using hc
  exact heq.comp_tendsto hpath

/-- In the exterior open half-plane, the normal derivative of the cutoff is
the derivative of the step times the boundary trace of the cutoff. -/
theorem lineDeriv_halfPlaneStokesCutoff_normal_eq_exterior
    (ρ : (ℝ × ℝ) → ℝ) {z : ℝ × ℝ} (hz : z.1 < 0) :
    lineDeriv ℝ (halfPlaneStokesCutoff ρ) z (1, 0) =
      deriv exteriorHalfPlaneStep z.1 * ρ (0, z.2) := by
  unfold lineDeriv
  have hcurve :
      (fun t : ℝ ↦ halfPlaneStokesCutoff ρ (z + t • (1, 0))) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ exteriorHalfPlaneStep (z.1 + t) * ρ (0, z.2)) := by
    have hnhds : Iio (-z.1) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by linarith)
    filter_upwards [hnhds] with t ht
    rw [halfPlaneStokesCutoff_eq_exterior]
    · simp
    · norm_num
      change t < -z.1 at ht
      linarith
  rw [hcurve.deriv_eq, deriv_mul_const_field]
  have hshift : HasDerivAt (fun t : ℝ ↦ z.1 + t) 1 0 := by
    simpa using
      (hasDerivAt_const (x := 0) z.1).add (hasDerivAt_id (x := 0))
  have hcomp :=
    (contDiff_exteriorHalfPlaneStep.differentiable (by simp) z.1).hasDerivAt.scomp_of_eq
      0 hshift (by simp)
  have hcomp' : HasDerivAt
      (fun t : ℝ ↦ exteriorHalfPlaneStep (z.1 + t))
      (deriv exteriorHalfPlaneStep z.1) 0 := by
    simpa only [Function.comp_apply, one_smul] using hcomp
  rw [hcomp'.deriv]

/-- In the exterior open half-plane, the tangential derivative of the
cutoff is the step times the boundary-trace derivative. -/
theorem lineDeriv_halfPlaneStokesCutoff_tangent_eq_exterior
    (ρ : (ℝ × ℝ) → ℝ) {z : ℝ × ℝ} (hz : z.1 < 0) :
    lineDeriv ℝ (halfPlaneStokesCutoff ρ) z (0, 1) =
      exteriorHalfPlaneStep z.1 *
        lineDeriv ℝ (fun y : ℝ ↦ ρ (0, y)) z.2 1 := by
  unfold lineDeriv
  have hfun : (fun t : ℝ ↦ halfPlaneStokesCutoff ρ
      (z + t • (0, 1))) =
      (fun t : ℝ ↦ exteriorHalfPlaneStep z.1 * ρ (0, z.2 + t)) := by
    funext t
    rw [halfPlaneStokesCutoff_eq_exterior]
    · simp
    · simpa using hz.le
  rw [hfun, deriv_const_mul_field]
  simp only [smul_eq_mul, mul_one]

/-- Constant extension preserves the finite weak derivative in the open
half-plane. -/
theorem finiteComplexWeakLineDerivative_halfPlaneConstantExtension_eq_self
    {ι : Type*} [Fintype ι] (F : (ℝ × ℝ) → ι → ℂ)
    {z p : ℝ × ℝ} (hz : 0 < z.1) :
    finiteComplexWeakLineDerivative (halfPlaneConstantExtension F) z p =
      finiteComplexWeakLineDerivative F z p := by
  funext i
  apply Complex.ext
  · exact lineDeriv_halfPlaneConstantExtension_eq_self
      (fun w ↦ (F w i).re) hz
  · exact lineDeriv_halfPlaneConstantExtension_eq_self
      (fun w ↦ (F w i).im) hz

/-- The finite weak normal derivative of the constant extension vanishes in
the exterior open half-plane. -/
theorem finiteComplexWeakLineDerivative_halfPlaneConstantExtension_normal_eq_zero
    {ι : Type*} [Fintype ι] (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : z.1 < 0) :
    finiteComplexWeakLineDerivative (halfPlaneConstantExtension F) z (1, 0) = 0 := by
  funext i
  apply Complex.ext
  · change lineDeriv ℝ
      (halfPlaneConstantExtension (fun w ↦ (F w i).re)) z (1, 0) = 0
    exact lineDeriv_halfPlaneConstantExtension_normal_eq_zero _ hz
  · change lineDeriv ℝ
      (halfPlaneConstantExtension (fun w ↦ (F w i).im)) z (1, 0) = 0
    exact lineDeriv_halfPlaneConstantExtension_normal_eq_zero _ hz

/-- The exterior tangential weak derivative is exactly the weak derivative
of the one-dimensional boundary trace. -/
theorem finiteComplexWeakLineDerivative_halfPlaneConstantExtension_tangent_eq_boundary
    {ι : Type*} [Fintype ι] (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : z.1 < 0) :
    finiteComplexWeakLineDerivative (halfPlaneConstantExtension F) z (0, 1) =
      finiteComplexWeakLineDerivative (fun y : ℝ ↦ F (0, y)) z.2 1 := by
  funext i
  apply Complex.ext
  · exact lineDeriv_halfPlaneConstantExtension_tangent_eq_boundary
      (fun w ↦ (F w i).re) hz
  · exact lineDeriv_halfPlaneConstantExtension_tangent_eq_boundary
      (fun w ↦ (F w i).im) hz

/-- Weak finite symplectic density in the standard oriented product frame. -/
def finiteComplexWeakSymplecticDensity
    {ι : Type*} [Fintype ι] (F : (ℝ × ℝ) → ι → ℂ)
    (z : ℝ × ℝ) : ℝ :=
  standardComplexSymplectic
    (finiteComplexWeakLineDerivative F z (1, 0))
    (finiteComplexWeakLineDerivative F z (0, 1))

/-- Cutoff-derivative term in localized finite weak Stokes. -/
def finiteComplexWeakPrimitiveError
    {ι : Type*} [Fintype ι] (ρ : (ℝ × ℝ) → ℝ)
    (F : (ℝ × ℝ) → ι → ℂ) (z : ℝ × ℝ) : ℝ :=
  lineDeriv ℝ ρ z (0, 1) *
      standardComplexSymplecticPrimitive
        (F z) (finiteComplexWeakLineDerivative F z (1, 0)) -
    lineDeriv ℝ ρ z (1, 0) *
      standardComplexSymplecticPrimitive
        (F z) (finiteComplexWeakLineDerivative F z (0, 1))

/-- Boundary action density for the increasing second-coordinate
parametrization of the line `x = 0`. -/
def finiteComplexWeakBoundaryActionDensity
    {ι : Type*} [Fintype ι] (ρ : (ℝ × ℝ) → ℝ)
    (F : (ℝ × ℝ) → ι → ℂ) (y : ℝ) : ℝ :=
  ρ (0, y) * standardComplexSymplecticPrimitive
    (F (0, y))
    (finiteComplexWeakLineDerivative (fun t : ℝ ↦ F (0, t)) y 1)

/-- Compact cutoff makes the finite weak symplectic density integrable. -/
theorem integrable_cutoff_mul_finiteComplexWeakSymplecticDensity
    {ι : Type*} [Fintype ι]
    {ρ : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (fun z ↦ ρ z * finiteComplexWeakSymplecticDensity F z) := by
  have hRe (i : ι) := lipschitzWith_complex_re_coordinate hF i
  have hIm (i : ι) := lipschitzWith_complex_im_coordinate hF i
  have hterm (i : ι) : Integrable (fun z : ℝ × ℝ ↦
      ρ z *
        (lineDeriv ℝ (fun w ↦ (F w i).re) z (1, 0) *
            lineDeriv ℝ (fun w ↦ (F w i).im) z (0, 1) -
          lineDeriv ℝ (fun w ↦ (F w i).re) z (0, 1) *
            lineDeriv ℝ (fun w ↦ (F w i).im) z (1, 0))) := by
    have hPQ := integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      volume hρ.continuous hρCompact (hRe i) (hIm i) (1, 0) (0, 1)
    have hQP := integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      volume hρ.continuous hρCompact (hRe i) (hIm i) (0, 1) (1, 0)
    simpa only [mul_sub, mul_assoc] using hPQ.sub hQP
  rw [show (fun z ↦ ρ z * finiteComplexWeakSymplecticDensity F z) =
      fun z ↦ ∑ i : ι, ρ z *
        (lineDeriv ℝ (fun w ↦ (F w i).re) z (1, 0) *
            lineDeriv ℝ (fun w ↦ (F w i).im) z (0, 1) -
          lineDeriv ℝ (fun w ↦ (F w i).re) z (0, 1) *
            lineDeriv ℝ (fun w ↦ (F w i).im) z (1, 0)) by
    funext z
    rw [finiteComplexWeakSymplecticDensity,
      standardComplexSymplectic_finiteComplexWeakLineDerivative,
      Finset.mul_sum]]
  exact integrable_finset_sum _ fun i _ ↦ hterm i

/-- The cutoff-derivative primitive error is integrable. -/
theorem integrable_finiteComplexWeakPrimitiveError
    {ι : Type*} [Fintype ι]
    {ρ : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (finiteComplexWeakPrimitiveError ρ F) := by
  have hRe (i : ι) := lipschitzWith_complex_re_coordinate hF i
  have hIm (i : ι) := lipschitzWith_complex_im_coordinate hF i
  have hterm (i : ι) : Integrable (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) *
      ((F z i).im *
          (lineDeriv ℝ ρ z (1, 0) *
              lineDeriv ℝ (fun w ↦ (F w i).re) z (0, 1) -
            lineDeriv ℝ ρ z (0, 1) *
              lineDeriv ℝ (fun w ↦ (F w i).re) z (1, 0)) -
        (F z i).re *
          (lineDeriv ℝ ρ z (1, 0) *
              lineDeriv ℝ (fun w ↦ (F w i).im) z (0, 1) -
            lineDeriv ℝ ρ z (0, 1) *
              lineDeriv ℝ (fun w ↦ (F w i).im) z (1, 0)))) := by
    have hImPQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      volume (hIm i).continuous hρ hρCompact (hRe i) (1, 0) (0, 1)
    have hImQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      volume (hIm i).continuous hρ hρCompact (hRe i) (0, 1) (1, 0)
    have hRePQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      volume (hRe i).continuous hρ hρCompact (hIm i) (1, 0) (0, 1)
    have hReQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      volume (hRe i).continuous hρ hρCompact (hIm i) (0, 1) (1, 0)
    simpa only [Pi.sub_apply, mul_sub, mul_assoc] using
      ((hImPQ.sub hImQP).sub (hRePQ.sub hReQP)).const_mul (1 / 2 : ℝ)
  rw [show finiteComplexWeakPrimitiveError ρ F =
      fun z ↦ ∑ i : ι, (1 / 2 : ℝ) *
        ((F z i).im *
            (lineDeriv ℝ ρ z (1, 0) *
                lineDeriv ℝ (fun w ↦ (F w i).re) z (0, 1) -
              lineDeriv ℝ ρ z (0, 1) *
                lineDeriv ℝ (fun w ↦ (F w i).re) z (1, 0)) -
          (F z i).re *
            (lineDeriv ℝ ρ z (1, 0) *
                lineDeriv ℝ (fun w ↦ (F w i).im) z (0, 1) -
              lineDeriv ℝ ρ z (0, 1) *
                lineDeriv ℝ (fun w ↦ (F w i).im) z (1, 0))) by
    funext z
    exact cutoffSymplecticPrimitiveError_eq_sum ρ F z (1, 0) (0, 1)]
  exact integrable_finset_sum _ fun i _ ↦ hterm i

theorem LipschitzWith.boundaryTrace
    {Y : Type*} [PseudoEMetricSpace Y]
    {f : (ℝ × ℝ) → Y} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith C (fun y : ℝ ↦ f (0, y)) := by
  have hline : LipschitzWith 1 (fun y : ℝ ↦ ((0 : ℝ), y)) :=
    by
      simpa using (LipschitzWith.const 0).prodMk LipschitzWith.id
  simpa only [Function.comp_apply, mul_one] using hf.comp hline

theorem HasCompactSupport.boundaryTrace
    {f : (ℝ × ℝ) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun y : ℝ ↦ f (0, y)) := by
  let K : Set ℝ := Prod.snd '' tsupport f
  have hK : IsCompact K := hf.isCompact.image continuous_snd
  apply HasCompactSupport.intro hK
  intro y hy
  by_contra hne
  apply hy
  exact ⟨(0, y), subset_tsupport f hne, rfl⟩

/-- Compact localization makes the boundary action density integrable. -/
theorem integrable_finiteComplexWeakBoundaryActionDensity
    {ι : Type*} [Fintype ι]
    {ρ : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (finiteComplexWeakBoundaryActionDensity ρ F) := by
  let r : ℝ → ℝ := fun y ↦ ρ (0, y)
  let G : ℝ → ι → ℂ := fun y ↦ F (0, y)
  have hr : LipschitzWith Cρ r := LipschitzWith.boundaryTrace hρ
  have hrCompact : HasCompactSupport r := HasCompactSupport.boundaryTrace hρCompact
  have hG : LipschitzWith CF G := LipschitzWith.boundaryTrace hF
  have hRe (i : ι) := lipschitzWith_complex_re_coordinate hG i
  have hIm (i : ι) := lipschitzWith_complex_im_coordinate hG i
  have hterm (i : ι) : Integrable (fun y : ℝ ↦ (1 / 2 : ℝ) *
      (r y * (G y i).re * lineDeriv ℝ (fun t ↦ (G t i).im) y 1 -
        r y * (G y i).im * lineDeriv ℝ (fun t ↦ (G t i).re) y 1)) := by
    have hCoeffRe : Integrable (fun y : ℝ ↦ r y * (G y i).re) :=
      Continuous.integrable_of_hasCompactSupport
        (hr.continuous.mul (hRe i).continuous) hrCompact.mul_right
    have hCoeffIm : Integrable (fun y : ℝ ↦ r y * (G y i).im) :=
      Continuous.integrable_of_hasCompactSupport
        (hr.continuous.mul (hIm i).continuous) hrCompact.mul_right
    have hFirst := hCoeffRe.mul_of_top_left ((hIm i).memLp_lineDeriv (μ := volume) 1)
    have hSecond := hCoeffIm.mul_of_top_left ((hRe i).memLp_lineDeriv (μ := volume) 1)
    exact (hFirst.sub hSecond).const_mul (1 / 2 : ℝ)
  rw [show finiteComplexWeakBoundaryActionDensity ρ F =
      fun y ↦ ∑ i : ι, (1 / 2 : ℝ) *
        (r y * (G y i).re * lineDeriv ℝ (fun t ↦ (G t i).im) y 1 -
          r y * (G y i).im * lineDeriv ℝ (fun t ↦ (G t i).re) y 1) by
    funext y
    rw [finiteComplexWeakBoundaryActionDensity,
      standardComplexSymplecticPrimitive_apply]
    unfold standardComplexSymplectic finiteComplexWeakLineDerivative
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, r, G]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  exact integrable_finset_sum _ fun i _ ↦ hterm i

theorem halfPlaneStokesCutoff_mul_density_eq_interior
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : 0 < z.1) :
    halfPlaneStokesCutoff ρ z *
        finiteComplexWeakSymplecticDensity
          (halfPlaneConstantExtension F) z =
      ρ z * finiteComplexWeakSymplecticDensity F z := by
  rw [halfPlaneStokesCutoff_eq_self ρ hz.le]
  unfold finiteComplexWeakSymplecticDensity
  rw [finiteComplexWeakLineDerivative_halfPlaneConstantExtension_eq_self F hz,
    finiteComplexWeakLineDerivative_halfPlaneConstantExtension_eq_self F hz]

theorem halfPlaneStokesCutoff_mul_density_eq_zero_exterior
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : z.1 < 0) :
    halfPlaneStokesCutoff ρ z *
        finiteComplexWeakSymplecticDensity
          (halfPlaneConstantExtension F) z = 0 := by
  unfold finiteComplexWeakSymplecticDensity
  rw [finiteComplexWeakLineDerivative_halfPlaneConstantExtension_normal_eq_zero F hz]
  simp [standardComplexSymplectic]

theorem finiteComplexWeakPrimitiveError_eq_interior
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : 0 < z.1) :
    finiteComplexWeakPrimitiveError
        (halfPlaneStokesCutoff ρ) (halfPlaneConstantExtension F) z =
      finiteComplexWeakPrimitiveError ρ F z := by
  unfold finiteComplexWeakPrimitiveError
  rw [lineDeriv_halfPlaneStokesCutoff_eq_self ρ hz,
    lineDeriv_halfPlaneStokesCutoff_eq_self ρ hz,
    halfPlaneConstantExtension_eq_self F hz.le,
    finiteComplexWeakLineDerivative_halfPlaneConstantExtension_eq_self F hz,
    finiteComplexWeakLineDerivative_halfPlaneConstantExtension_eq_self F hz]

/-- The exterior localized error is the negative step derivative times the
boundary action density.  This is the signed outward-normal convention for
the right half-plane and increasing boundary coordinate. -/
theorem finiteComplexWeakPrimitiveError_eq_exterior
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ)
    {z : ℝ × ℝ} (hz : z.1 < 0) :
    finiteComplexWeakPrimitiveError
        (halfPlaneStokesCutoff ρ) (halfPlaneConstantExtension F) z =
      -deriv exteriorHalfPlaneStep z.1 *
        finiteComplexWeakBoundaryActionDensity ρ F z.2 := by
  unfold finiteComplexWeakPrimitiveError
  rw [lineDeriv_halfPlaneStokesCutoff_tangent_eq_exterior ρ hz,
    lineDeriv_halfPlaneStokesCutoff_normal_eq_exterior ρ hz,
    halfPlaneConstantExtension_eq_boundary F hz.le,
    finiteComplexWeakLineDerivative_halfPlaneConstantExtension_normal_eq_zero F hz,
    finiteComplexWeakLineDerivative_halfPlaneConstantExtension_tangent_eq_boundary F hz]
  simp only [map_zero, mul_zero, zero_sub,
    finiteComplexWeakBoundaryActionDensity]
  ring

/-- Open right half-plane in product coordinates. -/
def planarRightOpenHalfPlane : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)

/-- Open exterior half-plane in product coordinates. -/
def planarLeftOpenHalfPlane : Set (ℝ × ℝ) :=
  Iio (0 : ℝ) ×ˢ (univ : Set ℝ)

theorem measurableSet_planarRightOpenHalfPlane :
    MeasurableSet planarRightOpenHalfPlane :=
  measurableSet_Ioi.prod MeasurableSet.univ

theorem measurableSet_planarLeftOpenHalfPlane :
    MeasurableSet planarLeftOpenHalfPlane :=
  measurableSet_Iio.prod MeasurableSet.univ

theorem compl_planarRightOpenHalfPlane :
    planarRightOpenHalfPlaneᶜ = Iic (0 : ℝ) ×ˢ (univ : Set ℝ) := by
  ext z
  simp [planarRightOpenHalfPlane]

theorem compl_planarRightOpenHalfPlane_ae_eq_left :
    planarRightOpenHalfPlaneᶜ =ᵐ[volume] planarLeftOpenHalfPlane := by
  rw [Measure.volume_eq_prod]
  have hprod : (Iic (0 : ℝ) ×ˢ (univ : Set ℝ)) =ᵐ[volume.prod volume]
      (Iio (0 : ℝ) ×ˢ (univ : Set ℝ)) := (Measure.set_prod_ae_eq
    (Iio_ae_eq_Iic : Iio (0 : ℝ) =ᵐ[volume] Iic 0)
    (ae_eq_refl (μ := volume) (univ : Set ℝ))).symm
  filter_upwards [hprod] with z hz
  apply propext
  change (z ∈ planarRightOpenHalfPlaneᶜ ↔ z ∈ planarLeftOpenHalfPlane)
  have hz' : (z ∈ Iic (0 : ℝ) ×ˢ (univ : Set ℝ) ↔
      z ∈ Iio (0 : ℝ) ×ˢ (univ : Set ℝ)) := Iff.of_eq hz
  simpa only [planarRightOpenHalfPlane, planarLeftOpenHalfPlane,
    Set.mem_compl_iff, Set.mem_prod, mem_Ioi, mem_Iic, mem_Iio,
    mem_univ, and_true, not_lt] using hz'

/-- An integrable planar function splits into its two open half-plane
integrals; the boundary line is null. -/
theorem integral_eq_setIntegral_right_add_left
    {f : (ℝ × ℝ) → ℝ} (hf : Integrable f) :
    ∫ z, f z =
      (∫ z in planarRightOpenHalfPlane, f z) +
        ∫ z in planarLeftOpenHalfPlane, f z := by
  rw [← integral_add_compl measurableSet_planarRightOpenHalfPlane hf]
  congr 1
  exact setIntegral_congr_set compl_planarRightOpenHalfPlane_ae_eq_left

/-- The localized density of the constant extension has exactly the
original right-half-plane integral. -/
theorem setIntegral_halfPlaneStokesCutoff_density_right
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ) :
    (∫ z in planarRightOpenHalfPlane,
        halfPlaneStokesCutoff ρ z *
          finiteComplexWeakSymplecticDensity
            (halfPlaneConstantExtension F) z) =
      ∫ z in planarRightOpenHalfPlane,
        ρ z * finiteComplexWeakSymplecticDensity F z := by
  apply setIntegral_congr_fun measurableSet_planarRightOpenHalfPlane
  intro z hz
  exact halfPlaneStokesCutoff_mul_density_eq_interior ρ F hz.1

theorem setIntegral_halfPlaneStokesCutoff_density_left_eq_zero
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ) :
    (∫ z in planarLeftOpenHalfPlane,
        halfPlaneStokesCutoff ρ z *
          finiteComplexWeakSymplecticDensity
            (halfPlaneConstantExtension F) z) = 0 := by
  apply setIntegral_eq_zero_of_ae_eq_zero
  filter_upwards with z hz
  exact halfPlaneStokesCutoff_mul_density_eq_zero_exterior ρ F hz.1

theorem setIntegral_finiteComplexWeakPrimitiveError_right
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ) :
    (∫ z in planarRightOpenHalfPlane,
        finiteComplexWeakPrimitiveError
          (halfPlaneStokesCutoff ρ) (halfPlaneConstantExtension F) z) =
      ∫ z in planarRightOpenHalfPlane,
        finiteComplexWeakPrimitiveError ρ F z := by
  apply setIntegral_congr_fun measurableSet_planarRightOpenHalfPlane
  intro z hz
  exact finiteComplexWeakPrimitiveError_eq_interior ρ F hz.1

/-- The exterior strip factors as the unit-mass step derivative times the
one-dimensional boundary action. -/
theorem setIntegral_finiteComplexWeakPrimitiveError_left
    {ι : Type*} [Fintype ι]
    (ρ : (ℝ × ℝ) → ℝ) (F : (ℝ × ℝ) → ι → ℂ) :
    (∫ z in planarLeftOpenHalfPlane,
        finiteComplexWeakPrimitiveError
          (halfPlaneStokesCutoff ρ) (halfPlaneConstantExtension F) z) =
      -∫ y : ℝ, finiteComplexWeakBoundaryActionDensity ρ F y := by
  calc
    (∫ z in planarLeftOpenHalfPlane,
        finiteComplexWeakPrimitiveError
          (halfPlaneStokesCutoff ρ) (halfPlaneConstantExtension F) z) =
        ∫ z in planarLeftOpenHalfPlane,
          (-deriv exteriorHalfPlaneStep z.1) *
            finiteComplexWeakBoundaryActionDensity ρ F z.2 := by
      apply setIntegral_congr_fun measurableSet_planarLeftOpenHalfPlane
      intro z hz
      exact finiteComplexWeakPrimitiveError_eq_exterior ρ F hz.1
    _ = (∫ x in Iio (0 : ℝ), -deriv exteriorHalfPlaneStep x) *
          ∫ y in (univ : Set ℝ),
            finiteComplexWeakBoundaryActionDensity ρ F y := by
      rw [planarLeftOpenHalfPlane, Measure.volume_eq_prod]
      exact setIntegral_prod_mul
        (fun x : ℝ ↦ -deriv exteriorHalfPlaneStep x)
        (finiteComplexWeakBoundaryActionDensity ρ F) (Iio 0) univ
    _ = -∫ y : ℝ, finiteComplexWeakBoundaryActionDensity ρ F y := by
      rw [integral_neg, integral_Iio_deriv_exteriorHalfPlaneStep,
        setIntegral_univ]
      ring

/-- **Localized Lipschitz weak Stokes on the right half-plane.**  For the
increasing second-coordinate boundary parametrization, the outward-normal
orientation contributes the displayed minus sign. -/
theorem integral_rightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq
    {ι : Type*} [Fintype ι]
    {ρ : (ℝ × ℝ) → ℝ} {F : (ℝ × ℝ) → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    (∫ z in planarRightOpenHalfPlane,
        ρ z * finiteComplexWeakSymplecticDensity F z) =
      (∫ z in planarRightOpenHalfPlane,
        finiteComplexWeakPrimitiveError ρ F z) -
        ∫ y : ℝ, finiteComplexWeakBoundaryActionDensity ρ F y := by
  obtain ⟨CR, hR⟩ :=
    exists_lipschitzWith_halfPlaneStokesCutoff hρ hρCompact
  let G : (ℝ × ℝ) → ι → ℂ := halfPlaneConstantExtension F
  have hG : LipschitzWith CF G :=
    LipschitzWith.halfPlaneConstantExtension hF
  have hRCompact := hasCompactSupport_halfPlaneStokesCutoff hρCompact
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hglobal := integral_cutoff_mul_standardComplexSymplectic_weak_eq
    volume hR hRCompact hG (1, 0) (0, 1)
  change (∫ z : ℝ × ℝ,
      halfPlaneStokesCutoff ρ z * finiteComplexWeakSymplecticDensity G z) =
    ∫ z : ℝ × ℝ,
      finiteComplexWeakPrimitiveError (halfPlaneStokesCutoff ρ) G z at hglobal
  have hLeftInt : Integrable (fun z : ℝ × ℝ ↦
      halfPlaneStokesCutoff ρ z * finiteComplexWeakSymplecticDensity G z) :=
    integrable_cutoff_mul_finiteComplexWeakSymplecticDensity
      hR hRCompact hG
  have hRightInt : Integrable
      (finiteComplexWeakPrimitiveError (halfPlaneStokesCutoff ρ) G) :=
    integrable_finiteComplexWeakPrimitiveError hR hRCompact hG
  rw [integral_eq_setIntegral_right_add_left hLeftInt,
    integral_eq_setIntegral_right_add_left hRightInt,
    show G = halfPlaneConstantExtension F from rfl,
    setIntegral_halfPlaneStokesCutoff_density_right,
    setIntegral_halfPlaneStokesCutoff_density_left_eq_zero,
    setIntegral_finiteComplexWeakPrimitiveError_right,
    setIntegral_finiteComplexWeakPrimitiveError_left] at hglobal
  linarith

#print axioms integral_rightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq

end

end GromovFilling
