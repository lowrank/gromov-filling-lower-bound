import GromovFilling.RiemannianChartArea

/-!
# The Riemannian area inequality for a countable chart family

This file sums the Jacobian-weighted measures contributed by a countable
family of parametrized Riemannian charts.  The one-chart area inequality then
globalizes to any planar set covered by the chartwise images.

This sum is an atlas-contribution measure, not yet the canonical Riemannian
area measure: overlapping chart pieces may be counted more than once.  The
remaining geometric step is to prove overlap invariance (or first disjointify
the chart images) and identify the resulting measure with intrinsic surface
area.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactAtlasArea :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The sum of the Jacobian-weighted area measures contributed by a family of
parametrized complex-plane chart pieces.  Overlaps are deliberately retained,
so this definition is immediately useful for upper bounds without asserting
chart independence. -/
def riemannianAtlasAreaMeasure
    {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) : Measure M :=
  Measure.sum (fun i ↦ riemannianChartAreaMeasure I (F i) (pieces i))

/-- Integration against the atlas-contribution measure is the sum of the
integrals against its chart contributions. -/
theorem lintegral_riemannianAtlasAreaMeasure
    {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) (q : M → ℝ≥0∞) :
    ∫⁻ x, q x ∂riemannianAtlasAreaMeasure I F pieces =
      ∑' i, ∫⁻ x, q x ∂riemannianChartAreaMeasure I (F i) (pieces i) := by
  exact lintegral_sum_measure q
    (fun i ↦ riemannianChartAreaMeasure I (F i) (pieces i))

/-- Countable-atlas globalization of the local area inequality from an
almost-everywhere chain identity.  The integration pieces may be measurable
subsets of larger open domains on which the pulled-back maps are Lipschitz;
this is the form needed after disjointifying an open chart cover. -/
theorem complex_volume_le_lintegral_riemannianAtlasAreaMeasure_of_ae_chain
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces domains : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, MeasurableSet (pieces i))
    (hdomains : ∀ i, IsOpen (domains i))
    (hsubset : ∀ i, pieces i ⊆ domains i)
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (domains i))
    (hFmeas : ∀ i, AEMeasurable (F i) (volume.restrict (pieces i)))
    (hDensityMeas : ∀ i, AEMeasurable
      (riemannianChartDensity I (F i)) (volume.restrict (pieces i)))
    (q : M → ℝ≥0∞)
    (hq : ∀ i, AEMeasurable q
      (riemannianChartAreaMeasure I (F i) (pieces i)))
    (hchain : ∀ i, ∀ᵐ z ∂volume.restrict (pieces i),
      ENNReal.ofReal
          (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F i) z) =
        riemannianChartDensity I (F i) z * q (F i z))
    (hcoverage : omega ⊆ ⋃ i, G '' (F i '' pieces i)) :
    volume omega ≤ ∫⁻ x, q x ∂riemannianAtlasAreaMeasure I F pieces := by
  calc
    volume omega ≤ volume (⋃ i, G '' (F i '' pieces i)) :=
      measure_mono hcoverage
    _ ≤ ∑' i, volume (G '' (F i '' pieces i)) :=
      measure_iUnion_le (fun i ↦ G '' (F i '' pieces i))
    _ ≤ ∑' i, ∫⁻ x, q x
          ∂riemannianChartAreaMeasure I (F i) (pieces i) := by
      refine ENNReal.tsum_le_tsum ?_
      intro i
      exact
        complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_ae_chain
          I (F i) G (pieces i) (domains i) (hpieces i) (hdomains i)
          (hsubset i) (hLipschitz i) (hFmeas i) (hDensityMeas i)
          q (hq i) (hchain i)
    _ = ∫⁻ x, q x ∂riemannianAtlasAreaMeasure I F pieces := by
      symm
      exact lintegral_riemannianAtlasAreaMeasure I F pieces q

/-- Intrinsic-Jacobian specialization of
`complex_volume_le_lintegral_riemannianAtlasAreaMeasure_of_ae_chain`.
It requires manifold differentiability only almost everywhere on each
measurable chart piece. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas_of_ae_mdifferentiable
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces domains : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, MeasurableSet (pieces i))
    (hdomains : ∀ i, IsOpen (domains i))
    (hsubset : ∀ i, pieces i ⊆ domains i)
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (domains i))
    (hFmeas : ∀ i, AEMeasurable (F i) (volume.restrict (pieces i)))
    (hDensityMeas : ∀ i, AEMeasurable
      (riemannianChartDensity I (F i)) (volume.restrict (pieces i)))
    (hJacobianMeas : ∀ i, AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I G x))
      (riemannianChartAreaMeasure I (F i) (pieces i)))
    (hDiff : ∀ i, ∀ᵐ z ∂volume.restrict (pieces i),
      MDifferentiableAt 𝓘(ℝ, ℂ) I (F i) z ∧
        MDifferentiableAt I 𝓘(ℝ, ℂ) G (F i z))
    (hcoverage : omega ⊆ ⋃ i, G '' (F i '' pieces i)) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianAtlasAreaMeasure I F pieces := by
  apply
    complex_volume_le_lintegral_riemannianAtlasAreaMeasure_of_ae_chain
      I F pieces domains G omega hpieces hdomains hsubset hLipschitz
      hFmeas hDensityMeas _ hJacobianMeas ?_ hcoverage
  intro i
  filter_upwards [hDiff i] with z hz
  exact ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
    I (F i) G z hz.1 hz.2

/-- Countable-atlas globalization of the local Riemannian area inequality
under the natural local almost-everywhere measurability assumptions. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas_of_aemeasurable
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (pieces i))
    (hFdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt 𝓘(ℝ, ℂ) I (F i) z)
    (hGdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F i z))
    (hFmeas : ∀ i, AEMeasurable (F i) (volume.restrict (pieces i)))
    (hDensityMeas : ∀ i, AEMeasurable
      (riemannianChartDensity I (F i)) (volume.restrict (pieces i)))
    (hJacobianMeas : Measurable (fun x ↦
      ENNReal.ofReal (riemannianTwoJacobian I G x)))
    (hcoverage : omega ⊆ ⋃ i, G '' (F i '' pieces i)) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianAtlasAreaMeasure I F pieces := by
  calc
    volume omega ≤ volume (⋃ i, G '' (F i '' pieces i)) :=
      measure_mono hcoverage
    _ ≤ ∑' i, volume (G '' (F i '' pieces i)) :=
      measure_iUnion_le (fun i ↦ G '' (F i '' pieces i))
    _ ≤ ∑' i,
        ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
          ∂riemannianChartAreaMeasure I (F i) (pieces i) := by
      refine ENNReal.tsum_le_tsum ?_
      intro i
      exact
        complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure_of_aemeasurable
          I (F i) G (pieces i) (hpieces i) (hLipschitz i)
          (hFdiff i) (hGdiff i) (hFmeas i) (hDensityMeas i)
          hJacobianMeas
    _ = ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
          ∂riemannianAtlasAreaMeasure I F pieces := by
      symm
      exact lintegral_riemannianAtlasAreaMeasure I F pieces _

/-- Measurable-data specialization of
`complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas_of_aemeasurable`.
If a planar set is covered by the images of the chart pieces under `G`, its
area is bounded by the intrinsic two-Jacobian of `G` integrated against the
sum of the chart contributions. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (pieces i))
    (hFdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt 𝓘(ℝ, ℂ) I (F i) z)
    (hGdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F i z))
    (hFmeas : ∀ i, Measurable (F i))
    (hDensityMeas : ∀ i, Measurable (riemannianChartDensity I (F i)))
    (hJacobianMeas : Measurable (fun x ↦
      ENNReal.ofReal (riemannianTwoJacobian I G x)))
    (hcoverage : omega ⊆ ⋃ i, G '' (F i '' pieces i)) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianAtlasAreaMeasure I F pieces := by
  calc
    volume omega ≤ volume (⋃ i, G '' (F i '' pieces i)) :=
      measure_mono hcoverage
    _ ≤ ∑' i, volume (G '' (F i '' pieces i)) :=
      measure_iUnion_le (fun i ↦ G '' (F i '' pieces i))
    _ ≤ ∑' i,
        ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
          ∂riemannianChartAreaMeasure I (F i) (pieces i) := by
      refine ENNReal.tsum_le_tsum ?_
      intro i
      exact
        complex_volume_image_image_le_lintegral_riemannianChartAreaMeasure
          I (F i) G (pieces i) (hpieces i) (hLipschitz i)
          (hFdiff i) (hGdiff i) (hFmeas i) (hDensityMeas i)
          hJacobianMeas
    _ = ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
          ∂riemannianAtlasAreaMeasure I F pieces := by
      symm
      exact lintegral_riemannianAtlasAreaMeasure I F pieces _

/-- Local-AE version of the atlas inequality stated from source coverage and
target-range coverage. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_subset_range_of_atlas_cover_of_aemeasurable
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (pieces i))
    (hFdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt 𝓘(ℝ, ℂ) I (F i) z)
    (hGdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F i z))
    (hFmeas : ∀ i, AEMeasurable (F i) (volume.restrict (pieces i)))
    (hDensityMeas : ∀ i, AEMeasurable
      (riemannianChartDensity I (F i)) (volume.restrict (pieces i)))
    (hJacobianMeas : Measurable (fun x ↦
      ENNReal.ofReal (riemannianTwoJacobian I G x)))
    (hatlas : (Set.univ : Set M) ⊆ ⋃ i, F i '' pieces i)
    (hcoverage : omega ⊆ Set.range G) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianAtlasAreaMeasure I F pieces := by
  apply
    complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas_of_aemeasurable
      I F pieces G omega hpieces hLipschitz hFdiff hGdiff hFmeas
      hDensityMeas hJacobianMeas
  rintro y hy
  rcases hcoverage hy with ⟨x, rfl⟩
  rcases Set.mem_iUnion.mp (hatlas (Set.mem_univ x)) with ⟨i, hi⟩
  rcases hi with ⟨z, hz, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, ⟨F i z, ⟨z, hz, rfl⟩, rfl⟩⟩

/-- The same atlas inequality stated from the two geometric coverage facts
that arise in Lemma 5.4: the chart pieces cover the source manifold and the
target set lies in the range of `G`. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_subset_range_of_atlas_cover
    {ι E H M : Type*} [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) (G : M → ℂ)
    (omega : Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    {K : ι → ℝ≥0}
    (hLipschitz : ∀ i, LipschitzOnWith (K i) (G ∘ F i) (pieces i))
    (hFdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt 𝓘(ℝ, ℂ) I (F i) z)
    (hGdiff : ∀ i z, z ∈ pieces i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (F i z))
    (hFmeas : ∀ i, Measurable (F i))
    (hDensityMeas : ∀ i, Measurable (riemannianChartDensity I (F i)))
    (hJacobianMeas : Measurable (fun x ↦
      ENNReal.ofReal (riemannianTwoJacobian I G x)))
    (hatlas : (Set.univ : Set M) ⊆ ⋃ i, F i '' pieces i)
    (hcoverage : omega ⊆ Set.range G) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂riemannianAtlasAreaMeasure I F pieces := by
  apply complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas
    I F pieces G omega hpieces hLipschitz hFdiff hGdiff hFmeas
      hDensityMeas hJacobianMeas
  rintro y hy
  rcases hcoverage hy with ⟨x, rfl⟩
  rcases Set.mem_iUnion.mp (hatlas (Set.mem_univ x)) with ⟨i, hi⟩
  rcases hi with ⟨z, hz, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, ⟨F i z, ⟨z, hz, rfl⟩, rfl⟩⟩

end

end GromovFilling
