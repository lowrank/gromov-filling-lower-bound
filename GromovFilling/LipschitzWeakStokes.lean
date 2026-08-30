import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Planar weak Stokes for Lipschitz coordinates

This file proves the Euclidean weak Stokes layer needed by the finite resonant
calibrations.  It first treats one globally Lipschitz scalar coordinate and
one compactly supported `C²` scalar coordinate.  Rademacher integration by
parts moves each weak derivative from the Lipschitz factor to the smooth
factor, where symmetry of the second derivative makes the two mixed terms
agree.  Normalized shrinking-bump mollification and dominated convergence
then give the identity for two Lipschitz scalar coordinates when the second
has compact support.
-/

open Filter Function MeasureTheory
open scoped ContDiff Convolution NNReal Pointwise

namespace GromovFilling

noncomputable section

/-- A canonical sequence of smooth bumps centered at the origin whose outer
radius is `2 / (n + 1)`. -/
def shrinkingContDiffBump
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) : ContDiffBump (0 : E) where
  rIn := ((n + 1 : ℕ) : ℝ)⁻¹
  rOut := 2 * ((n + 1 : ℕ) : ℝ)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    linarith

@[simp] theorem shrinkingContDiffBump_rIn
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) :
    (shrinkingContDiffBump E n).rIn = ((n + 1 : ℕ) : ℝ)⁻¹ := rfl

@[simp] theorem shrinkingContDiffBump_rOut
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] (n : ℕ) :
    (shrinkingContDiffBump E n).rOut =
      2 * ((n + 1 : ℕ) : ℝ)⁻¹ := rfl

theorem tendsto_shrinkingContDiffBump_rOut_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] :
    Tendsto (fun n : ℕ ↦ (shrinkingContDiffBump E n).rOut)
      Filter.atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  simpa only [shrinkingContDiffBump_rOut, mul_zero] using
    tendsto_const_nhds.mul hinv

/-- Convolution with the normalized shrinking bump. -/
def lipschitzMollification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [MeasurableSpace E]
    (mu : Measure E) (v : E → ℝ) (n : ℕ) : E → ℝ :=
  (shrinkingContDiffBump E n).normed mu ⋆[ContinuousLinearMap.mul ℝ ℝ, mu] v

private theorem real_convolution_mul_eq_lsmul
    {E : Type*} [MeasurableSpace E] [Sub E]
    (mu : Measure E) (f g : E → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, mu] g =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] g := by
  funext x
  change (∫ t : E, f t * g (x - t) ∂mu) =
    ∫ t : E, f t • g (x - t) ∂mu
  simp only [smul_eq_mul]

/-- Every Lipschitz mollification is smooth. -/
theorem contDiff_lipschitzMollification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} {C : ℝ≥0} (hv : LipschitzWith C v) (n : ℕ) :
    ContDiff ℝ ∞ (lipschitzMollification mu v n) := by
  exact (shrinkingContDiffBump E n).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ)
    (shrinkingContDiffBump E n).contDiff_normed hv.continuous.locallyIntegrable

/-- Mollification preserves compact support up to the compact Minkowski sum
with the support of the bump. -/
theorem hasCompactSupport_lipschitzMollification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} (hvCompact : HasCompactSupport v) (n : ℕ) :
    HasCompactSupport (lipschitzMollification mu v n) := by
  exact (shrinkingContDiffBump E n).hasCompactSupport_normed.convolution
    (ContinuousLinearMap.mul ℝ ℝ) hvCompact

/-- Normalized shrinking-bump convolution converges pointwise to every
continuous function. -/
theorem tendsto_lipschitzMollification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} (hv : Continuous v) (x : E) :
    Tendsto (fun n : ℕ ↦ lipschitzMollification mu v n x)
      atTop (nhds (v x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (tendsto_shrinkingContDiffBump_rOut_zero E) hv x

/-- The derivative of a Lipschitz mollification is convolution with the
Rademacher line derivative of the original function. -/
theorem fderiv_lipschitzMollification_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} {C : ℝ≥0} (hv : LipschitzWith C v)
    (n : ℕ) (x q : E) :
    fderiv ℝ (lipschitzMollification mu v n) x q =
      ((shrinkingContDiffBump E n).normed mu
        ⋆[ContinuousLinearMap.mul ℝ ℝ, mu]
          (fun y : E ↦ lineDeriv ℝ v y q)) x := by
  let k : E → ℝ := (shrinkingContDiffBump E n).normed mu
  let gx : E → ℝ := fun y ↦ k (x - y)
  have hkSmooth : ContDiff ℝ ∞ k :=
    (shrinkingContDiffBump E n).contDiff_normed
  have hkCompact : HasCompactSupport k :=
    (shrinkingContDiffBump E n).hasCompactSupport_normed
  have hvLocal : LocallyIntegrable v mu := hv.continuous.locallyIntegrable
  have hderiv := hkCompact.hasFDerivAt_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (hkSmooth.of_le (by simp)) hvLocal x
  obtain ⟨D, hkLip⟩ :=
    hkSmooth.lipschitzWith_of_hasCompactSupport hkCompact (by simp)
  have hsub : LipschitzWith 1 (fun y : E ↦ x - y) := by
    simpa using (LipschitzWith.const x).sub LipschitzWith.id
  have hgxLip : LipschitzWith D gx := by
    simpa only [gx, Function.comp_apply, mul_one] using hkLip.comp hsub
  have hgxCompact : HasCompactSupport gx := by
    simpa only [gx, Function.comp_apply] using
      hkCompact.comp_homeomorph (Homeomorph.subLeft x)
  have hgxLine (y : E) :
      lineDeriv ℝ gx y (-q) = fderiv ℝ k (x - y) q := by
    have hkDiff : DifferentiableAt ℝ k (x - y) :=
      hkSmooth.differentiable (by simp) (x - y)
    have hcomp := hkDiff.hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have hline := (hcomp.hasLineDerivAt (-q)).lineDeriv
    simpa only [gx, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      neg_neg] using hline
  have hibp := hv.integral_lineDeriv_mul_eq (μ := mu) hgxLip hgxCompact q
  have hconvExists := (hkCompact.fderiv ℝ).convolutionExists_left
    (ContinuousLinearMap.precompL E (ContinuousLinearMap.mul ℝ ℝ))
    (hkSmooth.continuous_fderiv (by simp)) hvLocal
  have hconvInt : Integrable
      (fun y : E ↦
        (ContinuousLinearMap.precompL E (ContinuousLinearMap.mul ℝ ℝ))
          (fderiv ℝ k (x - y)) (v y)) mu :=
    (hconvExists x).integrable_swap
  change fderiv ℝ
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ, mu] v) x q =
    (k ⋆[ContinuousLinearMap.mul ℝ ℝ, mu]
      (fun y : E ↦ lineDeriv ℝ v y q)) x
  rw [hderiv.fderiv]
  rw [convolution_eq_swap, convolution_eq_swap]
  rw [ContinuousLinearMap.integral_apply hconvInt q]
  change
    ∫ y : E, fderiv ℝ k (x - y) q * v y ∂mu =
      ∫ y : E, k (x - y) * lineDeriv ℝ v y q ∂mu
  calc
    ∫ y : E, fderiv ℝ k (x - y) q * v y ∂mu =
        ∫ y : E, lineDeriv ℝ gx y (-q) * v y ∂mu := by
      apply integral_congr_ae
      filter_upwards with y
      rw [hgxLine y]
    _ = ∫ y : E, lineDeriv ℝ v y q * gx y ∂mu := hibp.symm
    _ = ∫ y : E, k (x - y) * lineDeriv ℝ v y q ∂mu := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [gx]
      ring

/-- The derivatives of the mollifications converge almost everywhere to
the Rademacher line derivative of the original Lipschitz function. -/
theorem ae_tendsto_fderiv_lipschitzMollification_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} {C : ℝ≥0} (hv : LipschitzWith C v) (q : E) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n : ℕ ↦ fderiv ℝ (lipschitzMollification mu v n) x q)
      atTop (nhds (lineDeriv ℝ v x q)) := by
  have hradius := tendsto_shrinkingContDiffBump_rOut_zero E
  have hratio : ∀ᶠ n : ℕ in atTop,
      (shrinkingContDiffBump E n).rOut ≤
        2 * (shrinkingContDiffBump E n).rIn := by
    filter_upwards with n
    simp only [shrinkingContDiffBump_rOut, shrinkingContDiffBump_rIn,
      le_rfl]
  have hconv :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := mu) (K := 2) hradius hratio
      (hv.locallyIntegrable_lineDeriv q)
  filter_upwards [hconv] with x hx
  simpa only [fderiv_lipschitzMollification_apply mu hv,
    real_convolution_mul_eq_lsmul] using hx

/-- Mollification does not increase the directional derivative bound of a
Lipschitz function. -/
theorem norm_fderiv_lipschitzMollification_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} {C : ℝ≥0} (hv : LipschitzWith C v)
    (n : ℕ) (x q : E) :
    ‖fderiv ℝ (lipschitzMollification mu v n) x q‖ ≤
      (C : ℝ) * ‖q‖ := by
  rw [fderiv_lipschitzMollification_apply mu hv,
    real_convolution_mul_eq_lsmul]
  have h := dist_convolution_le
    (μ := mu) (x₀ := x)
    (R := (shrinkingContDiffBump E n).rOut)
    (ε := (C : ℝ) * ‖q‖) (z₀ := (0 : ℝ))
    (mul_nonneg C.coe_nonneg (norm_nonneg q))
    (shrinkingContDiffBump E n).support_normed_eq.subset
    (shrinkingContDiffBump E n).nonneg_normed
    (shrinkingContDiffBump E n).integral_normed
    (aestronglyMeasurable_lineDeriv hv.continuous mu)
    (fun y _hy ↦ by
      simpa only [dist_zero_right] using
        (norm_lineDeriv_le_of_lipschitz ℝ hv :
          ‖lineDeriv ℝ v y q‖ ≤ (C : ℝ) * ‖q‖))
  simpa only [dist_zero_right] using h

/-- All derivatives in the mollification sequence vanish outside one fixed
compact enlargement of the support of the original function. -/
theorem fderiv_lipschitzMollification_apply_eq_zero_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {v : E → ℝ} (hvCompact : HasCompactSupport v)
    (n : ℕ) (x q : E)
    (hx : x ∉ Metric.closedBall (0 : E) 2 + tsupport v) :
    fderiv ℝ (lipschitzMollification mu v n) x q = 0 := by
  have hradius : (shrinkingContDiffBump E n).rOut ≤ 2 := by
    rw [shrinkingContDiffBump_rOut]
    have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hone
    nlinarith
  have hkernel : support ((shrinkingContDiffBump E n).normed mu) ⊆
      Metric.closedBall (0 : E) 2 := by
    rw [(shrinkingContDiffBump E n).support_normed_eq]
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hradius)
  have hsupport : support (lipschitzMollification mu v n) ⊆
      Metric.closedBall (0 : E) 2 + tsupport v := by
    exact (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans
      (Set.add_subset_add hkernel subset_closure)
  have hcompact : IsCompact (Metric.closedBall (0 : E) 2 + tsupport v) :=
    (isCompact_closedBall (0 : E) 2).add hvCompact.isCompact
  have htsupport : tsupport (lipschitzMollification mu v n) ⊆
      Metric.closedBall (0 : E) 2 + tsupport v :=
    closure_minimal hsupport hcompact.isClosed
  have hxTsupport : x ∉ tsupport (lipschitzMollification mu v n) :=
    fun hx' ↦ hx (htsupport hx')
  rw [fderiv_of_notMem_tsupport ℝ hxTsupport]
  rfl

/-- Multiplying by a fixed Rademacher derivative, the derivatives of the
mollifications converge under the integral sign.  Compact support supplies
one integrable dominating function for the whole sequence. -/
theorem tendsto_integral_lineDeriv_mul_fderiv_lipschitzMollification
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {u v : E → ℝ} {Cu Cv : ℝ≥0}
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    Tendsto
      (fun n : ℕ ↦ ∫ x : E,
        lineDeriv ℝ u x p *
          fderiv ℝ (lipschitzMollification mu v n) x q ∂mu)
      atTop
      (nhds (∫ x : E,
        lineDeriv ℝ u x p * lineDeriv ℝ v x q ∂mu)) := by
  let K : Set E := Metric.closedBall (0 : E) 2 + tsupport v
  let A : ℝ := ((Cu : ℝ) * ‖p‖) * ((Cv : ℝ) * ‖q‖)
  let bound : E → ℝ := K.indicator (fun _ ↦ A)
  have hKCompact : IsCompact K :=
    (isCompact_closedBall (0 : E) 2).add hvCompact.isCompact
  have hFMeasurable (n : ℕ) : AEStronglyMeasurable
      (fun x : E ↦ lineDeriv ℝ u x p *
        fderiv ℝ (lipschitzMollification mu v n) x q) mu := by
    have hDerivativeContinuous : Continuous
        (fun x : E ↦ fderiv ℝ
          (lipschitzMollification mu v n) x q) := by
      exact ((contDiff_lipschitzMollification mu hv n).continuous_fderiv
        (by simp)).clm_apply continuous_const
    exact (aestronglyMeasurable_lineDeriv hu.continuous mu).mul
      hDerivativeContinuous.aestronglyMeasurable
  have hBoundIntegrable : Integrable bound mu := by
    change Integrable (K.indicator (fun _ : E ↦ A)) mu
    rw [integrable_indicator_iff hKCompact.measurableSet]
    exact integrableOn_const hKCompact.measure_lt_top.ne
  have hBound (n : ℕ) : ∀ᵐ x ∂mu,
      ‖lineDeriv ℝ u x p *
        fderiv ℝ (lipschitzMollification mu v n) x q‖ ≤ bound x := by
    filter_upwards with x
    by_cases hx : x ∈ K
    · change ‖lineDeriv ℝ u x p *
          fderiv ℝ (lipschitzMollification mu v n) x q‖ ≤
        K.indicator (fun _ : E ↦ A) x
      rw [Set.indicator_of_mem hx, norm_mul]
      dsimp only [A]
      gcongr
      · exact (norm_lineDeriv_le_of_lipschitz ℝ hu :
          ‖lineDeriv ℝ u x p‖ ≤ (Cu : ℝ) * ‖p‖)
      · exact norm_fderiv_lipschitzMollification_apply_le mu hv n x q
    · change ‖lineDeriv ℝ u x p *
          fderiv ℝ (lipschitzMollification mu v n) x q‖ ≤
        K.indicator (fun _ : E ↦ A) x
      rw [Set.indicator_of_notMem hx,
        fderiv_lipschitzMollification_apply_eq_zero_of_not_mem
          mu hvCompact n x q hx,
        mul_zero, norm_zero]
  have hLimit : ∀ᵐ x ∂mu, Tendsto
      (fun n : ℕ ↦ lineDeriv ℝ u x p *
        fderiv ℝ (lipschitzMollification mu v n) x q)
      atTop
      (nhds (lineDeriv ℝ u x p * lineDeriv ℝ v x q)) := by
    filter_upwards [ae_tendsto_fderiv_lipschitzMollification_apply mu hv q]
      with x hx
    exact tendsto_const_nhds.mul hx
  exact tendsto_integral_of_dominated_convergence bound hFMeasurable
    hBoundIntegrable hBound hLimit

/-- A line derivative vanishes away from the topological support. -/
theorem lineDeriv_eq_zero_of_not_mem_tsupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (x q : E) (hx : x ∉ tsupport f) :
    lineDeriv ℝ f x q = 0 := by
  exact ((HasFDerivAt.of_notMem_tsupport ℝ hx).hasLineDerivAt q).lineDeriv

/-- The product of two Rademacher line derivatives is integrable when the
second Lipschitz function is compactly supported. -/
theorem integrable_lineDeriv_mul_lineDeriv_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu]
    {u v : E → ℝ} {Cu Cv : ℝ≥0}
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    Integrable
      (fun x : E ↦ lineDeriv ℝ u x p * lineDeriv ℝ v x q) mu := by
  let A : ℝ := ((Cu : ℝ) * ‖p‖) * ((Cv : ℝ) * ‖q‖)
  let bound : E → ℝ := (tsupport v).indicator (fun _ ↦ A)
  have hBoundIntegrable : Integrable bound mu := by
    change Integrable ((tsupport v).indicator (fun _ : E ↦ A)) mu
    rw [integrable_indicator_iff hvCompact.isCompact.measurableSet]
    exact integrableOn_const hvCompact.isCompact.measure_lt_top.ne
  have hMeasurable : AEStronglyMeasurable
      (fun x : E ↦ lineDeriv ℝ u x p * lineDeriv ℝ v x q) mu :=
    (aestronglyMeasurable_lineDeriv hu.continuous mu).mul
      (aestronglyMeasurable_lineDeriv hv.continuous mu)
  apply hBoundIntegrable.mono' hMeasurable
  filter_upwards with x
  by_cases hx : x ∈ tsupport v
  · change ‖lineDeriv ℝ u x p * lineDeriv ℝ v x q‖ ≤
      (tsupport v).indicator (fun _ : E ↦ A) x
    rw [Set.indicator_of_mem hx, norm_mul]
    dsimp only [A]
    gcongr
    · exact (norm_lineDeriv_le_of_lipschitz ℝ hu :
        ‖lineDeriv ℝ u x p‖ ≤ (Cu : ℝ) * ‖p‖)
    · exact (norm_lineDeriv_le_of_lipschitz ℝ hv :
        ‖lineDeriv ℝ v x q‖ ≤ (Cv : ℝ) * ‖q‖)
  · change ‖lineDeriv ℝ u x p * lineDeriv ℝ v x q‖ ≤
      (tsupport v).indicator (fun _ : E ↦ A) x
    rw [Set.indicator_of_notMem hx,
      lineDeriv_eq_zero_of_not_mem_tsupport x q hx,
      mul_zero, norm_zero]

/-- The two mixed Jacobian terms have the same integral when one scalar
coordinate is globally Lipschitz and the other is compactly supported and
`C²`.  This is the mixed-regularity core of weak planar Stokes. -/
theorem integral_lineDeriv_mul_fderiv_swap_of_lipschitzWith_of_contDiff_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {u v : E → ℝ} {C : ℝ≥0}
    (hu : LipschitzWith C u) (hv : ContDiff ℝ 2 v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    ∫ x : E, lineDeriv ℝ u x p * fderiv ℝ v x q ∂mu =
      ∫ x : E, lineDeriv ℝ u x q * fderiv ℝ v x p ∂mu := by
  let gp : E → ℝ := fun x ↦ fderiv ℝ v x p
  let gq : E → ℝ := fun x ↦ fderiv ℝ v x q
  have hDv : ContDiff ℝ 1 (fderiv ℝ v) :=
    hv.fderiv_right (m := 1) (by norm_num)
  have hgp : ContDiff ℝ 1 gp := by
    exact hDv.clm_apply contDiff_const
  have hgq : ContDiff ℝ 1 gq := by
    exact hDv.clm_apply contDiff_const
  have hgpCompact : HasCompactSupport gp := by
    exact hvCompact.fderiv_apply ℝ p
  have hgqCompact : HasCompactSupport gq := by
    exact hvCompact.fderiv_apply ℝ q
  obtain ⟨Cp, hgpLip⟩ :=
    hgp.lipschitzWith_of_hasCompactSupport hgpCompact (by norm_num)
  obtain ⟨Cq, hgqLip⟩ :=
    hgq.lipschitzWith_of_hasCompactSupport hgqCompact (by norm_num)
  have hmixed (x : E) :
      lineDeriv ℝ gq x (-p) = lineDeriv ℝ gp x (-q) := by
    have hDvx : DifferentiableAt ℝ (fderiv ℝ v) x :=
      (hDv.differentiable one_ne_zero) x
    have hq :=
      (ContinuousLinearMap.apply ℝ ℝ q).hasFDerivAt.comp x hDvx.hasFDerivAt
    have hp :=
      (ContinuousLinearMap.apply ℝ ℝ p).hasFDerivAt.comp x hDvx.hasFDerivAt
    have hqLine := (hq.hasLineDerivAt (-p)).lineDeriv
    have hpLine := (hp.hasLineDerivAt (-q)).lineDeriv
    have hqLine' : lineDeriv ℝ gq x (-p) =
        ((ContinuousLinearMap.apply ℝ ℝ q).comp
          (fderiv ℝ (fderiv ℝ v) x)) (-p) := by
      simpa only [gq, Function.comp_apply] using hqLine
    have hpLine' : lineDeriv ℝ gp x (-q) =
        ((ContinuousLinearMap.apply ℝ ℝ p).comp
          (fderiv ℝ (fderiv ℝ v) x)) (-q) := by
      simpa only [gp, Function.comp_apply] using hpLine
    rw [hqLine', hpLine']
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, map_neg]
    rw [(hv.contDiffAt.isSymmSndFDerivAt (by norm_num) p q)]
  calc
    ∫ x : E, lineDeriv ℝ u x p * fderiv ℝ v x q ∂mu =
        ∫ x : E, lineDeriv ℝ gq x (-p) * u x ∂mu := by
      simpa only [gq] using hu.integral_lineDeriv_mul_eq hgqLip hgqCompact p
    _ = ∫ x : E, lineDeriv ℝ gp x (-q) * u x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hmixed x]
    _ = ∫ x : E, lineDeriv ℝ u x q * fderiv ℝ v x p ∂mu := by
      symm
      simpa only [gp] using hu.integral_lineDeriv_mul_eq hgpLip hgpCompact q

/-- Equivalently, the integrated mixed Jacobian of a Lipschitz scalar
coordinate and a compactly supported `C²` scalar coordinate is zero. -/
theorem integral_lipschitz_contDiff_jacobian_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {u v : E → ℝ} {C : ℝ≥0}
    (hu : LipschitzWith C u) (hv : ContDiff ℝ 2 v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    ∫ x : E,
        lineDeriv ℝ u x p * fderiv ℝ v x q -
          lineDeriv ℝ u x q * fderiv ℝ v x p ∂mu = 0 := by
  let gp : E → ℝ := fun x ↦ fderiv ℝ v x p
  let gq : E → ℝ := fun x ↦ fderiv ℝ v x q
  have hDcont : Continuous (fderiv ℝ v) :=
    hv.continuous_fderiv (by norm_num)
  have hgpCont : Continuous gp := hDcont.clm_apply continuous_const
  have hgqCont : Continuous gq := hDcont.clm_apply continuous_const
  have hgpCompact : HasCompactSupport gp := hvCompact.fderiv_apply ℝ p
  have hgqCompact : HasCompactSupport gq := hvCompact.fderiv_apply ℝ q
  have htermPQ : Integrable
      (fun x : E ↦ lineDeriv ℝ u x p * fderiv ℝ v x q) mu := by
    have hgqInt : Integrable gq mu :=
      hgqCont.integrable_of_hasCompactSupport hgqCompact
    simpa only [gq, mul_comm] using
      hgqInt.mul_of_top_left (hu.memLp_lineDeriv (μ := mu) p)
  have htermQP : Integrable
      (fun x : E ↦ lineDeriv ℝ u x q * fderiv ℝ v x p) mu := by
    have hgpInt : Integrable gp mu :=
      hgpCont.integrable_of_hasCompactSupport hgpCompact
    simpa only [gp, mul_comm] using
      hgpInt.mul_of_top_left (hu.memLp_lineDeriv (μ := mu) q)
  rw [integral_sub htermPQ htermQP,
    integral_lineDeriv_mul_fderiv_swap_of_lipschitzWith_of_contDiff_two
      mu hu hv hvCompact p q,
    sub_self]

/-- Weak planar Stokes for two globally Lipschitz scalar coordinates, one
of which has compact support.  Both weak derivatives are Rademacher line
derivatives. -/
theorem integral_lineDeriv_mul_lineDeriv_swap_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {u v : E → ℝ} {Cu Cv : ℝ≥0}
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    ∫ x : E, lineDeriv ℝ u x p * lineDeriv ℝ v x q ∂mu =
      ∫ x : E, lineDeriv ℝ u x q * lineDeriv ℝ v x p ∂mu := by
  have hLeft :=
    tendsto_integral_lineDeriv_mul_fderiv_lipschitzMollification
      mu hu hv hvCompact p q
  have hRight :=
    tendsto_integral_lineDeriv_mul_fderiv_lipschitzMollification
      mu hu hv hvCompact q p
  apply tendsto_nhds_unique_of_eventuallyEq hLeft hRight
  filter_upwards with n
  exact integral_lineDeriv_mul_fderiv_swap_of_lipschitzWith_of_contDiff_two
    mu hu
    ((contDiff_lipschitzMollification mu hv n).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from
        WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    (hasCompactSupport_lipschitzMollification mu hvCompact n) p q

/-- Equivalently, the integrated weak Jacobian of two Lipschitz scalar
coordinates is zero when the second coordinate is compactly supported. -/
theorem integral_lipschitz_lipschitz_jacobian_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {u v : E → ℝ} {Cu Cv : ℝ≥0}
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (hvCompact : HasCompactSupport v) (p q : E) :
    ∫ x : E,
        lineDeriv ℝ u x p * lineDeriv ℝ v x q -
          lineDeriv ℝ u x q * lineDeriv ℝ v x p ∂mu = 0 := by
  have htermPQ := integrable_lineDeriv_mul_lineDeriv_of_lipschitzWith
    mu hu hv hvCompact p q
  have htermQP := integrable_lineDeriv_mul_lineDeriv_of_lipschitzWith
    mu hu hv hvCompact q p
  rw [integral_sub htermPQ htermQP,
    integral_lineDeriv_mul_lineDeriv_swap_of_lipschitzWith
      mu hu hv hvCompact p q,
    sub_self]

#print axioms fderiv_lipschitzMollification_apply
#print axioms ae_tendsto_fderiv_lipschitzMollification_apply
#print axioms norm_fderiv_lipschitzMollification_apply_le
#print axioms fderiv_lipschitzMollification_apply_eq_zero_of_not_mem
#print axioms tendsto_integral_lineDeriv_mul_fderiv_lipschitzMollification
#print axioms integral_lineDeriv_mul_fderiv_swap_of_lipschitzWith_of_contDiff_two
#print axioms integral_lipschitz_contDiff_jacobian_eq_zero
#print axioms integral_lineDeriv_mul_lineDeriv_swap_of_lipschitzWith
#print axioms integral_lipschitz_lipschitz_jacobian_eq_zero

end

end GromovFilling
