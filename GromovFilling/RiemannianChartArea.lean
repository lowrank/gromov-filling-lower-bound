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

/-- Restricting a chart-area measure in the manifold is the same as
restricting its coordinate domain to the corresponding preimage. -/
theorem restrict_riemannianChartAreaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : MeasurableSet s)
    (t : Set M) (ht : MeasurableSet t)
    (hF : AEMeasurable F (volume.restrict s)) :
    (riemannianChartAreaMeasure I F s).restrict t =
      riemannianChartAreaMeasure I F (s ∩ F ⁻¹' t) := by
  unfold riemannianChartAreaMeasure
  have hFweighted : AEMeasurable F
      ((volume.restrict s).withDensity (riemannianChartDensity I F)) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [Measure.restrict_map_of_aemeasurable hFweighted ht,
    restrict_withDensity' (F ⁻¹' t) (riemannianChartDensity I F),
    Measure.restrict_restrict' hs, inter_comm]

/-- A chart-area contribution is supported on the image of its coordinate
set.  Consequently, restricting it to any measurable superset of that image
does not change the measure. -/
theorem restrict_riemannianChartAreaMeasure_of_image_subset
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : MeasurableSet s)
    (t : Set M) (ht : MeasurableSet t)
    (hF : AEMeasurable F (volume.restrict s))
    (hst : F '' s ⊆ t) :
    (riemannianChartAreaMeasure I F s).restrict t =
      riemannianChartAreaMeasure I F s := by
  rw [restrict_riemannianChartAreaMeasure I F s hs t ht hF]
  congr 2
  exact inter_eq_left.2 fun z hz ↦ hst ⟨z, hz, rfl⟩

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
theorem lintegral_riemannianChartAreaMeasure_of_aemeasurable
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
    (q : M → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ y, q y ∂riemannianChartAreaMeasure I F s =
      ∫⁻ z in s, riemannianChartDensity I F z * q (F z) ∂volume := by
  rw [riemannianChartAreaMeasure]
  have hFweighted : AEMeasurable F
      ((volume.restrict s).withDensity (riemannianChartDensity I F)) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [lintegral_map' hq.aemeasurable hFweighted]
  have hqF : AEMeasurable (fun z ↦ q (F z)) (volume.restrict s) :=
    hq.comp_aemeasurable hF
  rw [lintegral_withDensity_eq_lintegral_mul₀ hDensity hqF]
  rfl

/-- Integration against a chart-area measure when the integrand is only
almost everywhere measurable for that measure.  This is the natural
regularity available for the intrinsic Jacobian of a Lipschitz map. -/
theorem lintegral_riemannianChartAreaMeasure_of_aemeasurable_integrand
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
    (q : M → ℝ≥0∞)
    (hq : AEMeasurable q (riemannianChartAreaMeasure I F s)) :
    ∫⁻ y, q y ∂riemannianChartAreaMeasure I F s =
      ∫⁻ z in s, riemannianChartDensity I F z * q (F z) ∂volume := by
  rw [riemannianChartAreaMeasure] at hq ⊢
  have hFweighted : AEMeasurable F
      ((volume.restrict s).withDensity (riemannianChartDensity I F)) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [lintegral_map' hq hFweighted]
  have hqF : AEMeasurable (fun z ↦ q (F z))
      ((volume.restrict s).withDensity (riemannianChartDensity I F)) :=
    hq.comp_aemeasurable hFweighted
  rw [lintegral_withDensity_eq_lintegral_mul₀' hDensity hqF]
  rfl

/-- Measurable-data specialization of
`lintegral_riemannianChartAreaMeasure_of_aemeasurable`. -/
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
  exact lintegral_riemannianChartAreaMeasure_of_aemeasurable
    I F s hF.aemeasurable.restrict hDensity.aemeasurable.restrict q hq

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

/-- Intrinsic-Jacobian restatement of the planar area inequality on a
measurable subset of an open Lipschitz domain. -/
theorem complex_volume_image_le_lintegral_riemannianTwoJacobian_of_measurableSet_subset_isOpen
    (f : ℂ → ℂ) (s U : Set ℂ) (hs : MeasurableSet s)
    (hU : IsOpen U) (hsU : s ⊆ U)
    {K : ℝ≥0} (hf : LipschitzOnWith K f U) :
    volume (f '' s) ≤
      ∫⁻ z in s,
        ENNReal.ofReal
          (riemannianTwoJacobian 𝓘(ℝ, ℂ) f z) ∂volume := by
  simpa only [riemannianTwoJacobian_complex_eq_abs_det_fderiv] using
    complex_volume_image_le_lintegral_abs_det_fderiv_of_measurableSet_subset_isOpen
      f s U hs hU hsU hf

/-- The area inequality on one Riemannian chart.  The image of the chart
piece under a surface map is controlled by the integral of the surface
Jacobian against the chart-induced area measure. -/
theorem complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_aemeasurable
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
    (hFmeas : AEMeasurable F (volume.restrict s))
    (hDensityMeas : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
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
      exact lintegral_riemannianChartAreaMeasure_of_aemeasurable
        I F s hFmeas hDensityMeas _ hJacobianMeas

/-- The one-chart Riemannian area inequality on a measurable chart piece
contained in an open domain on which the pulled-back map is Lipschitz. -/
theorem complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_aemeasurable_of_measurableSet_subset_isOpen
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (G : M → ℂ) (s U : Set ℂ)
    (hs : MeasurableSet s) (hU : IsOpen U) (hsU : s ⊆ U)
    {K : ℝ≥0} (hLipschitz : LipschitzOnWith K (G ∘ F) U)
    (hFdiff : ∀ z ∈ s, MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hGdiff : ∀ z ∈ s,
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F z))
    (hFmeas : AEMeasurable F (volume.restrict s))
    (hDensityMeas : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
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
      exact
        complex_volume_image_le_lintegral_riemannianTwoJacobian_of_measurableSet_subset_isOpen
          (G ∘ F) s U hs hU hsU hLipschitz
    _ = ∫⁻ z in s,
          riemannianChartDensity I F z *
            ENNReal.ofReal (riemannianTwoJacobian I G (F z)) ∂volume := by
      apply setLIntegral_congr_fun hs
      intro z hz
      exact ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
        I F G z (hFdiff z hz) (hGdiff z hz)
    _ = ∫⁻ x,
          ENNReal.ofReal (riemannianTwoJacobian I G x)
            ∂riemannianChartAreaMeasure I F s := by
      symm
      exact lintegral_riemannianChartAreaMeasure_of_aemeasurable
        I F s hFmeas hDensityMeas _ hJacobianMeas

/-- The one-chart area inequality from an almost-everywhere intrinsic chain
rule.  This is the bridge used for Lipschitz maps: Rademacher supplies the
chain identity almost everywhere, rather than pointwise differentiability
on the whole chart piece. -/
theorem complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_ae_chain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (G : M → ℂ) (s U : Set ℂ)
    (hs : MeasurableSet s) (hU : IsOpen U) (hsU : s ⊆ U)
    {K : ℝ≥0} (hLipschitz : LipschitzOnWith K (G ∘ F) U)
    (hFmeas : AEMeasurable F (volume.restrict s))
    (hDensityMeas : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
    (q : M → ℝ≥0∞)
    (hq : AEMeasurable q (riemannianChartAreaMeasure I F s))
    (hchain : ∀ᵐ z ∂volume.restrict s,
      ENNReal.ofReal
          (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F) z) =
        riemannianChartDensity I F z * q (F z)) :
    volume (G '' (F '' s)) ≤
      ∫⁻ x, q x ∂riemannianChartAreaMeasure I F s := by
  rw [Set.image_image]
  calc
    volume ((fun z ↦ G (F z)) '' s) ≤
        ∫⁻ z in s,
          ENNReal.ofReal
            (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F) z) ∂volume := by
      exact
        complex_volume_image_le_lintegral_riemannianTwoJacobian_of_measurableSet_subset_isOpen
          (G ∘ F) s U hs hU hsU hLipschitz
    _ = ∫⁻ z in s,
          riemannianChartDensity I F z * q (F z) ∂volume :=
      lintegral_congr_ae hchain
    _ = ∫⁻ x, q x ∂riemannianChartAreaMeasure I F s := by
      symm
      exact lintegral_riemannianChartAreaMeasure_of_aemeasurable_integrand
        I F s hFmeas hDensityMeas q hq

/-- The almost-everywhere differentiability specialization of
`complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_ae_chain`.
It exposes precisely the two remaining Lipschitz tasks: prove manifold
differentiability almost everywhere and prove local almost-everywhere
measurability of the intrinsic Jacobian. -/
theorem complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_ae_mdifferentiable
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (G : M → ℂ) (s U : Set ℂ)
    (hs : MeasurableSet s) (hU : IsOpen U) (hsU : s ⊆ U)
    {K : ℝ≥0} (hLipschitz : LipschitzOnWith K (G ∘ F) U)
    (hFmeas : AEMeasurable F (volume.restrict s))
    (hDensityMeas : AEMeasurable
      (riemannianChartDensity I F) (volume.restrict s))
    (hJacobianMeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I G x))
      (riemannianChartAreaMeasure I F s))
    (hDiff : ∀ᵐ z ∂volume.restrict s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I F z ∧
        MDifferentiableAt I 𝓘(ℝ, ℂ) G (F z)) :
    volume (G '' (F '' s)) ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianChartAreaMeasure I F s := by
  apply
    complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_ae_chain
      I F G s U hs hU hsU hLipschitz hFmeas hDensityMeas _ hJacobianMeas
  filter_upwards [hDiff] with z hz
  exact ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
    I F G z hz.1 hz.2

/-- Measurable-data specialization of
`complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_aemeasurable`. -/
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
  exact
    complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_aemeasurable
      I F G s hs hLipschitz hFdiff hGdiff
      hFmeas.aemeasurable.restrict hDensityMeas.aemeasurable.restrict
      hJacobianMeas

end

end GromovFilling
