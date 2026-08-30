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

#print axioms
  integral_riemannianChartAreaMeasure_of_aestronglyMeasurable
#print axioms integral_riemannianChartAreaMeasure_real

end

end GromovFilling
