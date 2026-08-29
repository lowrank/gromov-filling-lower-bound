import GromovFilling.RiemannianChartArea
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Measurability of Riemannian chart densities

The intrinsic two-Jacobian is defined using arbitrary orthonormal bases in
each tangent fiber.  Its Gram formula removes those choices: for a map from
the complex plane, the density is the square root of the Gram determinant of
the two derivative vectors obtained from the fixed basis `1, I`.

For a continuously differentiable chart map and a continuous Riemannian
metric, those two derivative-vector sections are continuous.  Their inner
products, the Gram determinant, and hence the chart density are continuous
on every open chart piece.  This discharges the local almost-everywhere
measurability hypothesis used by the chart-area and transition theorems.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal InnerProductSpace Manifold NNReal

namespace GromovFilling

noncomputable section

/-- The `i`th derivative vector of a parametrized Riemannian chart, using
the fixed orthonormal basis `1, I` of the complex source. -/
def riemannianChartGramVector
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (F : ℂ → M) (i : Fin 2) (z : ℂ) : TangentSpace I (F z) :=
  mfderiv 𝓘(ℝ, ℂ) I F z (Complex.orthonormalBasisOneI i)

/-- The derivative vector bundled with its base point in the target tangent
bundle. -/
def riemannianChartGramVectorSection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (F : ℂ → M) (i : Fin 2) (z : ℂ) : TangentBundle I M :=
  ⟨F z, riemannianChartGramVector I F i z⟩

/-- The Gram determinant of the two chart derivative vectors. -/
def riemannianChartGramDet
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (F : ℂ → M) (z : ℂ) : ℝ :=
  ⟪riemannianChartGramVector I F 0 z,
      riemannianChartGramVector I F 0 z⟫_ℝ *
    ⟪riemannianChartGramVector I F 1 z,
      riemannianChartGramVector I F 1 z⟫_ℝ -
    ⟪riemannianChartGramVector I F 0 z,
      riemannianChartGramVector I F 1 z⟫_ℝ ^ 2

private theorem tangentSpace_finrank_eq_two_chartDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [hE : Fact (Module.finrank ℝ E = 2)] (x : M) :
    Module.finrank ℝ (TangentSpace I x) = 2 := by
  simpa only [TangentSpace] using hE.out

/-- The chart density is the nonnegative square root of its Gram
determinant. -/
theorem riemannianChartDensity_eq_ofReal_sqrt_gram
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (z : ℂ) :
    riemannianChartDensity I F z =
      ENNReal.ofReal √(riemannianChartGramDet I F z) := by
  letI : Fact (Module.finrank ℝ
      (TangentSpace 𝓘(ℝ, ℂ) z) = 2) :=
    ⟨by simpa only [TangentSpace] using Complex.finrank_real_complex⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two_chartDensity I (F z)⟩
  let e : OrthonormalBasis (Fin 2) ℝ
      (TangentSpace 𝓘(ℝ, ℂ) z) :=
    Complex.orthonormalBasisOneI
  let o : Orientation ℝ (TangentSpace I (F z)) (Fin 2) :=
    (canonicalOrthonormalBasisTwo (TangentSpace I (F z))).toBasis.orientation
  change ENNReal.ofReal
      (twoJacobian (mfderiv 𝓘(ℝ, ℂ) I F z)) = _
  rw [twoJacobian_eq_sqrt_gram e o]
  simp only [riemannianChartGramDet, riemannianChartGramVector,
    real_inner_self_eq_norm_sq, e]

/-- A `C¹` map on an open complex set has continuous Gram-vector
sections there. -/
theorem continuousOn_riemannianChartGramVectorSection
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (F : ℂ → M) (s : Set ℂ) (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) I 1 F s) (i : Fin 2) :
    ContinuousOn (riemannianChartGramVectorSection I F i) s := by
  let V : ℂ → TangentBundle 𝓘(ℝ, ℂ) ℂ :=
    fun z ↦ ⟨z, Complex.orthonormalBasisOneI i⟩
  have hVmdiff : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent ∞ V := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact contDiff_const
  have hTM := hF.continuousOn_tangentMapWithin (by simp) hs.uniqueMDiffOn
  have hwithin : ContinuousOn
      (fun z ↦ tangentMapWithin 𝓘(ℝ, ℂ) I F s (V z)) s := by
    apply hTM.comp' hVmdiff.continuous.continuousOn
    intro z hz
    change z ∈ s
    exact hz
  apply hwithin.congr
  intro z hz
  ext
  · rfl
  · simp only [riemannianChartGramVectorSection,
      riemannianChartGramVector, tangentMapWithin_snd, V]
    rw [mfderivWithin_of_isOpen hs hz]

/-- Continuous Gram-vector sections make the chart density continuous on
the chart piece and therefore almost everywhere measurable for restricted
planar volume. -/
theorem aemeasurable_riemannianChartDensity_of_continuousOn_gramVectors
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : IsOpen s)
    (hv : ∀ i, ContinuousOn
      (riemannianChartGramVectorSection I F i) s) :
    AEMeasurable (riemannianChartDensity I F) (volume.restrict s) := by
  have h00 := (hv 0).inner_bundle (hv 0)
  have h11 := (hv 1).inner_bundle (hv 1)
  have h01 := (hv 0).inner_bundle (hv 1)
  have hgram : ContinuousOn (riemannianChartGramDet I F) s := by
    simpa only [riemannianChartGramDet] using
      (h00.mul h11).sub (h01.pow 2)
  have hexplicit : ContinuousOn
      (fun z ↦ ENNReal.ofReal √(riemannianChartGramDet I F z)) s :=
    ENNReal.continuous_ofReal.comp_continuousOn hgram.sqrt
  exact (hexplicit.congr fun z _hz ↦
    riemannianChartDensity_eq_ofReal_sqrt_gram I F z).aemeasurable
      hs.measurableSet

/-- A continuously differentiable parametrization on an open chart piece
has an almost everywhere measurable intrinsic area density. -/
theorem aemeasurable_riemannianChartDensity_of_contMDiffOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) I 1 F s) :
    AEMeasurable (riemannianChartDensity I F) (volume.restrict s) :=
  aemeasurable_riemannianChartDensity_of_continuousOn_gramVectors
    I F s hs (continuousOn_riemannianChartGramVectorSection I F s hs hF)

end

end GromovFilling
