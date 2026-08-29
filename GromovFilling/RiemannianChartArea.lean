import GromovFilling.RiemannianAreaFormula
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Area measure and the area inequality on one Riemannian chart

This file constructs the measure contributed by a single parametrized
Riemannian chart.  It is the pushforward of planar volume weighted by the
intrinsic two-Jacobian of the parametrization.  The manifold chain rule then
turns the planar area inequality into an exact local surface statement.

The construction is local.  Proving that compatible chart contributions glue
to a canonical global Riemannian area measure remains a separate step.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactChartArea :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The `ℝ≥0∞`-valued area density of a parametrization from the Euclidean
complex plane into a two-dimensional Riemannian manifold. -/
def riemannianChartDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (riemannianTwoJacobianBetween 𝓘(ℝ, ℂ) I F z)

/-- The area measure contributed by one parametrized chart domain.  Planar
volume is first restricted to the coordinate set, then weighted by the
intrinsic Jacobian of the parametrization, and finally pushed to the
manifold. -/
def riemannianChartAreaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) : Measure M :=
  Measure.map F
    ((volume.restrict s).withDensity (riemannianChartDensity I F))

/-- The manifold chain rule in the multiplicative `ℝ≥0∞` form used by the
chart-area measure. -/
theorem ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (G : M → ℂ) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : MDifferentiableAt I 𝓘(ℝ, ℂ) G (F z)) :
    ENNReal.ofReal
        (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F) z) =
      riemannianChartDensity I F z *
        ENNReal.ofReal (riemannianTwoJacobian I G (F z)) := by
  rw [riemannianTwoJacobian_comp 𝓘(ℝ, ℂ) I F G z hF hG,
    ENNReal.ofReal_mul (riemannianTwoJacobian_nonneg I G (F z))]
  simp only [riemannianChartDensity, mul_comm]

/-- Integration against a single chart-area measure is exactly weighted
planar integration on its coordinate domain. -/
theorem lintegral_riemannianChartAreaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ)
    (hF : Measurable F)
    (hDensity : Measurable (riemannianChartDensity I F))
    (q : M → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ y, q y ∂riemannianChartAreaMeasure I F s =
      ∫⁻ z in s, riemannianChartDensity I F z * q (F z) ∂volume := by
  rw [riemannianChartAreaMeasure, lintegral_map hq hF]
  have hqF : Measurable (fun z ↦ q (F z)) := hq.comp hF
  rw [lintegral_withDensity_eq_lintegral_mul _ hDensity hqF]
  rfl

/-- Local planar image-area inequality in intrinsic Riemannian `J₂`
notation. -/
theorem complex_volume_image_le_lintegral_riemannianTwoJacobian_of_isOpen
    (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤
      ∫⁻ z in s,
        ENNReal.ofReal
          (riemannianTwoJacobian 𝓘(ℝ, ℂ) f z) ∂volume := by
  simpa only [riemannianTwoJacobian_complex_eq_abs_det_fderiv] using
    complex_volume_image_le_lintegral_abs_det_fderiv_of_isOpen
      f s hs hf

/-- The area inequality on one Riemannian chart.  The image of the chart
piece under a surface map is controlled by the integral of the surface
Jacobian against the chart-induced area measure. -/
theorem complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (G : M → ℂ) (s : Set ℂ) (hs : IsOpen s)
    {K : ℝ≥0} (hLipschitz : LipschitzOnWith K (G ∘ F) s)
    (hFdiff : ∀ z ∈ s, MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hGdiff : ∀ z ∈ s,
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F z))
    (hFmeas : Measurable F)
    (hDensityMeas : Measurable (riemannianChartDensity I F))
    (hJacobianMeas : Measurable (fun x ↦
      ENNReal.ofReal (riemannianTwoJacobian I G x))) :
    volume (G '' (F '' s)) ≤
      ∫⁻ x,
        ENNReal.ofReal (riemannianTwoJacobian I G x)
          ∂riemannianChartAreaMeasure I F s := by
  rw [Set.image_image]
  calc
    volume ((fun z ↦ G (F z)) '' s) ≤
        ∫⁻ z in s,
          ENNReal.ofReal
            (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F) z) ∂volume := by
      exact complex_volume_image_le_lintegral_riemannianTwoJacobian_of_isOpen
        (G ∘ F) s hs hLipschitz
    _ = ∫⁻ z in s,
          riemannianChartDensity I F z *
            ENNReal.ofReal (riemannianTwoJacobian I G (F z)) ∂volume := by
      apply setLIntegral_congr_fun hs.measurableSet
      intro z hz
      exact ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
        I F G z (hFdiff z hz) (hGdiff z hz)
    _ = ∫⁻ x,
          ENNReal.ofReal (riemannianTwoJacobian I G x)
            ∂riemannianChartAreaMeasure I F s := by
      symm
      exact lintegral_riemannianChartAreaMeasure I F s hFmeas
        hDensityMeas _ hJacobianMeas

end

end GromovFilling
