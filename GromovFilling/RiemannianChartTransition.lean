import GromovFilling.RiemannianChartArea

/-!
# Reparametrization invariance of Riemannian chart-area contributions

This file proves the overlap calculation needed to glue the chart measures.
For an injective differentiable change of complex coordinates, the manifold
chain rule and the planar change-of-variables theorem show that the
Jacobian-weighted chart contribution is unchanged.

The hypotheses deliberately expose the measurability interfaces still needed
to instantiate the result with standard smooth manifold charts.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactChartTransition :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The density of a reparametrized surface chart is the old chart density
times the absolute determinant of the planar coordinate change. -/
theorem riemannianChartDensity_comp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ → ℂ) (F : ℂ → M) (z : ℂ)
    (he : DifferentiableAt ℝ e z)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F (e z)) :
    riemannianChartDensity I (F ∘ e) z =
      ENNReal.ofReal |(fderiv ℝ e z).det| *
        riemannianChartDensity I F (e z) := by
  rw [riemannianChartDensity, riemannianChartDensity,
    riemannianTwoJacobianBetween_comp 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) I
      e F z he.mdifferentiableAt hF,
    ENNReal.ofReal_mul
      (riemannianTwoJacobianBetween_nonneg 𝓘(ℝ, ℂ) I F (e z)),
    riemannianTwoJacobianBetween_complex_eq_abs_det_fderiv]
  exact mul_comm _ _

/-- Integration against a chart-area contribution is unchanged by an
injective differentiable reparametrization of its coordinate domain.  Only
almost-everywhere measurability on the two coordinate pieces is required. -/
theorem lintegral_riemannianChartAreaMeasure_comp_of_aemeasurable
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ → ℂ) (F : ℂ → M) (s : Set ℂ)
    (hs : MeasurableSet s)
    (heDiff : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (hFdiff : ∀ z ∈ s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I F (e z))
    (hFcompMeas : AEMeasurable (F ∘ e) (volume.restrict s))
    (hFmeas : AEMeasurable F (volume.restrict (e '' s)))
    (hDensityCompMeas :
      AEMeasurable (riemannianChartDensity I (F ∘ e))
        (volume.restrict s))
    (hDensityMeas : AEMeasurable (riemannianChartDensity I F)
      (volume.restrict (e '' s)))
    (q : M → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ x, q x ∂riemannianChartAreaMeasure I (F ∘ e) s =
      ∫⁻ x, q x ∂riemannianChartAreaMeasure I F (e '' s) := by
  calc
    ∫⁻ x, q x ∂riemannianChartAreaMeasure I (F ∘ e) s =
        ∫⁻ z in s,
          riemannianChartDensity I (F ∘ e) z * q (F (e z)) ∂volume := by
      simpa only [Function.comp_apply] using
        lintegral_riemannianChartAreaMeasure_of_aemeasurable
          I (F ∘ e) s hFcompMeas hDensityCompMeas q hq
    _ = ∫⁻ z in s,
          ENNReal.ofReal |(fderiv ℝ e z).det| *
            (riemannianChartDensity I F (e z) * q (F (e z))) ∂volume := by
      apply setLIntegral_congr_fun hs
      intro z hz
      change riemannianChartDensity I (F ∘ e) z * q (F (e z)) = _
      rw [riemannianChartDensity_comp I e F z (heDiff z hz)
        (hFdiff z hz)]
      simp only [mul_assoc]
    _ = ∫⁻ w in e '' s,
          riemannianChartDensity I F w * q (F w) ∂volume := by
      symm
      exact lintegral_image_eq_lintegral_abs_det_fderiv_mul
        volume hs
          (fun z hz ↦ (heDiff z hz).hasFDerivAt.hasFDerivWithinAt)
          heInj (fun w ↦ riemannianChartDensity I F w * q (F w))
    _ = ∫⁻ x, q x ∂riemannianChartAreaMeasure I F (e '' s) := by
      symm
      exact lintegral_riemannianChartAreaMeasure_of_aemeasurable I F (e '' s)
        hFmeas hDensityMeas q hq

/-- The Jacobian-weighted chart-area measure itself is invariant under an
injective differentiable change of complex coordinates, assuming only local
almost-everywhere measurability. -/
theorem riemannianChartAreaMeasure_comp_of_aemeasurable
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ → ℂ) (F : ℂ → M) (s : Set ℂ)
    (hs : MeasurableSet s)
    (heDiff : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (hFdiff : ∀ z ∈ s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I F (e z))
    (hFcompMeas : AEMeasurable (F ∘ e) (volume.restrict s))
    (hFmeas : AEMeasurable F (volume.restrict (e '' s)))
    (hDensityCompMeas :
      AEMeasurable (riemannianChartDensity I (F ∘ e))
        (volume.restrict s))
    (hDensityMeas : AEMeasurable (riemannianChartDensity I F)
      (volume.restrict (e '' s))) :
    riemannianChartAreaMeasure I (F ∘ e) s =
      riemannianChartAreaMeasure I F (e '' s) := by
  rw [Measure.ext_iff_lintegral]
  intro q hq
  exact lintegral_riemannianChartAreaMeasure_comp_of_aemeasurable I e F s hs
    heDiff heInj hFdiff hFcompMeas hFmeas hDensityCompMeas
      hDensityMeas q hq

/-- Measurable-data specialization of
`lintegral_riemannianChartAreaMeasure_comp_of_aemeasurable`. -/
theorem lintegral_riemannianChartAreaMeasure_comp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ → ℂ) (F : ℂ → M) (s : Set ℂ)
    (hs : MeasurableSet s)
    (heDiff : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (heMeas : Measurable e)
    (hFdiff : ∀ z ∈ s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I F (e z))
    (hFmeas : Measurable F)
    (hDensityCompMeas :
      Measurable (riemannianChartDensity I (F ∘ e)))
    (hDensityMeas : Measurable (riemannianChartDensity I F))
    (q : M → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ x, q x ∂riemannianChartAreaMeasure I (F ∘ e) s =
      ∫⁻ x, q x ∂riemannianChartAreaMeasure I F (e '' s) := by
  exact lintegral_riemannianChartAreaMeasure_comp_of_aemeasurable
    I e F s hs heDiff heInj hFdiff
      (hFmeas.comp heMeas).aemeasurable.restrict
      hFmeas.aemeasurable.restrict
      hDensityCompMeas.aemeasurable.restrict
      hDensityMeas.aemeasurable.restrict q hq

/-- Measurable-data specialization of
`riemannianChartAreaMeasure_comp_of_aemeasurable`. -/
theorem riemannianChartAreaMeasure_comp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ → ℂ) (F : ℂ → M) (s : Set ℂ)
    (hs : MeasurableSet s)
    (heDiff : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (heMeas : Measurable e)
    (hFdiff : ∀ z ∈ s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I F (e z))
    (hFmeas : Measurable F)
    (hDensityCompMeas :
      Measurable (riemannianChartDensity I (F ∘ e)))
    (hDensityMeas : Measurable (riemannianChartDensity I F)) :
    riemannianChartAreaMeasure I (F ∘ e) s =
      riemannianChartAreaMeasure I F (e '' s) := by
  exact riemannianChartAreaMeasure_comp_of_aemeasurable
    I e F s hs heDiff heInj hFdiff
      (hFmeas.comp heMeas).aemeasurable.restrict
      hFmeas.aemeasurable.restrict
      hDensityCompMeas.aemeasurable.restrict
      hDensityMeas.aemeasurable.restrict

end

end GromovFilling
