import GromovFilling.RiemannianChartArea
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Signed integration against a Riemannian chart-area measure

The chart-area construction is a pushforward of planar volume weighted by
the intrinsic two-Jacobian.  The existing chart formula is stated for
nonnegative `lintegral`s.  Localized Stokes needs the corresponding Bochner
integral identity for signed real densities, so this module records the
vector-valued identity and its real-valued specialization.
-/

open Bundle MeasureTheory
open scoped Bundle ENNReal Manifold

namespace GromovFilling

noncomputable section

/-- Bochner integration against a chart-area measure is planar integration
weighted by the real value of the chart two-Jacobian density. -/
theorem integral_riemannianChartAreaMeasure_of_aestronglyMeasurable
    {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ℂ → M) (s : Set ℂ)
    (hF : AEMeasurable F (volume.restrict s))
    (hDensity : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
    (q : M → V)
    (hq : AEStronglyMeasurable q
      (riemannianChartAreaMeasure I F s)) :
    (∫ y, q y ∂riemannianChartAreaMeasure I F s) =
      ∫ z in s, (riemannianChartDensity I F z).toReal • q (F z)
        ∂volume := by
  rw [riemannianChartAreaMeasure] at hq ⊢
  have hFweighted : AEMeasurable F
      ((volume.restrict s).withDensity
        (riemannianChartDensity I F)) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [integral_map hFweighted hq]
  have hDensityTop :
      ∀ᵐ z ∂volume.restrict s,
        riemannianChartDensity I F z < ∞ := by
    filter_upwards with z
    simp only [riemannianChartDensity, ENNReal.ofReal_lt_top]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hDensity hDensityTop]

/-- Real-valued signed chart integration, written with multiplication rather
than scalar action. -/
theorem integral_riemannianChartAreaMeasure_real
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ)
    (hF : AEMeasurable F (volume.restrict s))
    (hDensity : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
    (q : M → ℝ)
    (hq : AEStronglyMeasurable q
      (riemannianChartAreaMeasure I F s)) :
    (∫ y, q y ∂riemannianChartAreaMeasure I F s) =
      ∫ z in s,
        (riemannianChartDensity I F z).toReal * q (F z) ∂volume := by
  simpa only [smul_eq_mul] using
    (integral_riemannianChartAreaMeasure_of_aestronglyMeasurable
      I F s hF hDensity q hq)

/-- Weighted planar integrability transfers to integrability against the
chart-area measure when the parametrization is a measurable embedding on its
coordinate domain. -/
theorem integrable_riemannianChartAreaMeasure_real_of_integrable_weighted
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : MeasurableSet s)
    (hFcont : ContinuousOn F s) (hFinj : Set.InjOn F s)
    (hDensity : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
    (q : M → ℝ)
    (hq : Integrable (fun z ↦
      (riemannianChartDensity I F z).toReal * q (F z))
        (volume.restrict s)) :
    Integrable q (riemannianChartAreaMeasure I F s) := by
  let d : ℂ → ℝ≥0∞ := riemannianChartDensity I F
  let ν : Measure ℂ := (volume.restrict s).withDensity d
  have hFembed : MeasurableEmbedding (s.restrict F) :=
    hFcont.measurableEmbedding hs hFinj
  have hFbase : AEMeasurable F (volume.restrict s) :=
    hFcont.aemeasurable hs
  have hdTop : ∀ᵐ z ∂volume.restrict s, d z < ∞ := by
    filter_upwards with z
    simp only [d, riemannianChartDensity, ENNReal.ofReal_lt_top]
  have hqFweighted : Integrable (fun z ↦ q (F z)) ν := by
    apply (integrable_withDensity_iff_integrable_smul₀'
      hDensity hdTop).2
    simpa only [d, ν, smul_eq_mul] using hq
  have hFweighted : AEMeasurable F ν := by
    exact hFbase.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict s) d)
  have hνmem : ∀ᵐ z ∂ν, z ∈ s := by
    exact (Measure.ae_le_iff_absolutelyContinuous.mpr
      (withDensity_absolutelyContinuous (volume.restrict s) d))
        (ae_restrict_mem hs)
  have hνrestrict : ν.restrict s = ν :=
    Measure.restrict_eq_self_of_ae_mem hνmem
  let μs : Measure s := Measure.comap ((↑) : s → ℂ) ν
  have hcoeMap : μs.map ((↑) : s → ℂ) = ν := by
    rw [show μs = Measure.comap ((↑) : s → ℂ) ν by rfl,
      map_comap_subtype_coe hs, hνrestrict]
  have hqSubtype : Integrable (q ∘ s.restrict F) μs := by
    have hqRestrict : Integrable (fun z ↦ q (F z)) (ν.restrict s) := by
      rw [hνrestrict]
      exact hqFweighted
    have hqComap :=
      (integrableOn_iff_comap_subtypeVal hs).1 hqRestrict
    simpa only [μs, Function.comp_apply, Set.restrict_apply] using hqComap
  have hqMappedSubtype : Integrable q (μs.map (s.restrict F)) :=
    hFembed.integrable_map_iff.2 hqSubtype
  have hFafterCoe : AEMeasurable F
      (μs.map ((↑) : s → ℂ)) := by
    rw [hcoeMap]
    exact hFweighted
  have hmap : μs.map (s.restrict F) = ν.map F := by
    change μs.map (F ∘ ((↑) : s → ℂ)) = ν.map F
    rw [← hFafterCoe.map_map_of_aemeasurable
      measurable_subtype_coe.aemeasurable]
    exact congrArg (Measure.map F) hcoeMap
  simpa only [riemannianChartAreaMeasure, ν, hmap] using hqMappedSubtype

#print axioms
  integral_riemannianChartAreaMeasure_of_aestronglyMeasurable
#print axioms integral_riemannianChartAreaMeasure_real
#print axioms
  integrable_riemannianChartAreaMeasure_real_of_integrable_weighted

end

end GromovFilling
