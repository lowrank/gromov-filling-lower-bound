import GromovFilling.RiemannianChartDisjointification
import GromovFilling.RiemannianInteriorChart

/-!
# A finite controlled atlas for the Riemannian interior

This file assembles the local ingredients used in the area half of Lemma 5.4.
Compactness supplies finitely many controlled complex inverse charts.  They
are padded by empty domains to a countable family and then disjointified, so
their images cover the manifold interior without counting any point twice.

The resulting atlas measure is deliberately attached to the chosen
controlled atlas.  Independence of that choice, and hence identification
with canonical Riemannian area, is a separate theorem rather than an implicit
assumption here.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Function Manifold NNReal

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactInteriorAtlasArea :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- A countable family of controlled complex parametrizations whose images
cover the manifold interior.  The family has finite support, but a natural
number index lets it feed the existing countable-atlas area theorem directly.
-/
structure ControlledInteriorAtlas
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] where
  parametrization : ℕ → ℂ → M
  domain : ℕ → Set ℂ
  lipschitzConstant : ℕ → ℝ≥0
  isOpen_domain : ∀ i, IsOpen (domain i)
  continuousOn_parametrization :
    ∀ i, ContinuousOn (parametrization i) (domain i)
  contMDiffOn_parametrization :
    ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) I 1 (parametrization i) (domain i)
  isOpen_image : ∀ i, IsOpen (parametrization i '' domain i)
  lipschitzOnWith_parametrization :
    ∀ i, LipschitzOnWith (lipschitzConstant i)
      (parametrization i) (domain i)
  interior_subset_iUnion_image :
    I.interior M ⊆ ⋃ i, parametrization i '' domain i
  eventually_domain_eq_empty :
    ∃ N, ∀ i, N ≤ i → domain i = ∅

/-- Pad a finite family of controlled inverse charts by a constant map after
the final index.  Its accompanying domains are empty there. -/
def finControlledInteriorParametrization
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) {n : ℕ} (centers : Fin n → M)
    (fallback : M) (i : ℕ) : ℂ → M :=
  if hi : i < n then
    interiorComplexExtChart I e (centers ⟨i, hi⟩)
  else
    fun _ ↦ fallback

/-- Pad the controlled domains of a finite inverse-chart family by empty
sets. -/
def finControlledInteriorDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) {n : ℕ} (centers : Fin n → M)
    (i : ℕ) : Set ℂ :=
  if hi : i < n then
    chosenControlledInteriorComplexChartDomain I e (centers ⟨i, hi⟩)
  else
    ∅

/-- The inverse-chart Lipschitz constant of the padded finite family. -/
def finControlledInteriorLipschitzConstant
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {n : ℕ} (centers : Fin n → M) (i : ℕ) : ℝ≥0 :=
  if hi : i < n then
    (chosenInteriorChartControl I (centers ⟨i, hi⟩)).C
  else
    0

/-- Turn a finite controlled interior-chart cover into a countable controlled
atlas with finite support. -/
def controlledInteriorAtlasOfFinCover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (e : ℂ ≃ₗᵢ[ℝ] E) {n : ℕ} (centers : Fin n → M)
    (fallback : M)
    (hcover : I.interior M ⊆ ⋃ i,
      interiorComplexExtChart I e (centers i) ''
        chosenControlledInteriorComplexChartDomain I e (centers i)) :
    ControlledInteriorAtlas I M := by
  let F : ℕ → ℂ → M :=
    finControlledInteriorParametrization I e centers fallback
  let domains : ℕ → Set ℂ :=
    finControlledInteriorDomain I e centers
  let K : ℕ → ℝ≥0 :=
    finControlledInteriorLipschitzConstant I centers
  refine
    { parametrization := F
      domain := domains
      lipschitzConstant := K
      isOpen_domain := ?_
      continuousOn_parametrization := ?_
      contMDiffOn_parametrization := ?_
      isOpen_image := ?_
      lipschitzOnWith_parametrization := ?_
      interior_subset_iUnion_image := ?_
      eventually_domain_eq_empty := ?_ }
  · intro i
    by_cases hi : i < n
    · simpa [domains, finControlledInteriorDomain, hi] using
        isOpen_controlledInteriorComplexChartDomain I e
          (chosenInteriorChartControl I (centers ⟨i, hi⟩))
    · simp [domains, finControlledInteriorDomain, hi]
  · intro i
    by_cases hi : i < n
    · have hsubset :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩))
      simpa [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi] using
        (continuousOn_interiorComplexExtChart I e (centers ⟨i, hi⟩)).mono
          hsubset
    · simp [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi]
  · intro i
    by_cases hi : i < n
    · have hsubset :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩))
      simpa [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi] using
        (contMDiffOn_interiorComplexExtChart I e (centers ⟨i, hi⟩)).mono
          hsubset
    · simp [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi]
  · intro i
    by_cases hi : i < n
    · rw [show F i = interiorComplexExtChart I e (centers ⟨i, hi⟩) by
        simp [F, finControlledInteriorParametrization, hi]]
      rw [show domains i =
          chosenControlledInteriorComplexChartDomain I e (centers ⟨i, hi⟩) by
        simp [domains, finControlledInteriorDomain, hi]]
      rw [chosenControlledInteriorComplexChartDomain,
        image_controlledInteriorComplexChartDomain I e]
      exact (isOpen_controlledInteriorChartNeighborhood I
        (chosenInteriorChartControl I (centers ⟨i, hi⟩))).inter
          (I.isOpen_interior one_ne_zero)
    · simp [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi]
  · intro i
    by_cases hi : i < n
    · simpa [F, domains, K, finControlledInteriorParametrization,
        finControlledInteriorDomain, finControlledInteriorLipschitzConstant,
        hi] using
        lipschitzOnWith_controlledInteriorComplexChart I e
          (chosenInteriorChartControl I (centers ⟨i, hi⟩))
    · simp [F, domains, K, finControlledInteriorParametrization,
        finControlledInteriorDomain, finControlledInteriorLipschitzConstant,
        hi]
  · intro y hy
    rcases Set.mem_iUnion.mp (hcover hy) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i.val, by
      simpa [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, i.isLt] using hi⟩
  · refine ⟨n, ?_⟩
    intro i hi
    simp [domains, finControlledInteriorDomain, not_lt_of_ge hi]

/-- Every compact two-dimensional Riemannian manifold admits a controlled
complex atlas of its interior with finite support. -/
theorem nonempty_controlledInteriorAtlas
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompactSpace M] [Nonempty M]
    (e : ℂ ≃ₗᵢ[ℝ] E) :
    Nonempty (ControlledInteriorAtlas I M) := by
  obtain ⟨n, centers, hcover⟩ :=
    exists_fin_controlledInteriorComplexExtChart_cover (M := M) I e
  exact ⟨controlledInteriorAtlasOfFinCover (M := M) I e centers
    (Classical.choice inferInstance) hcover⟩

namespace ControlledInteriorAtlas

/-- Pull the first-occurrence assignment on chart images back to each
coordinate domain. -/
def piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (i : ℕ) : Set ℂ :=
  disjointChartPiece A.parametrization A.domain i

/-- Every disjointified coordinate piece stays in its original open
controlled domain. -/
theorem piece_subset_domain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (i : ℕ) :
    A.piece I i ⊆ A.domain i :=
  disjointChartPiece_subset A.parametrization A.domain i

/-- The disjointified coordinate pieces are measurable. -/
theorem measurableSet_piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (i : ℕ) :
    MeasurableSet (A.piece I i) := by
  letI : Nonempty M := ⟨A.parametrization 0 0⟩
  exact measurableSet_disjointChartPiece_of_isOpen
    A.parametrization A.domain A.isOpen_domain
      A.continuousOn_parametrization A.isOpen_image i

/-- Distinct atlas pieces have disjoint images in the manifold. -/
theorem pairwise_disjoint_image_piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) :
    Pairwise (Disjoint on fun i ↦
      A.parametrization i '' A.piece I i) :=
  pairwise_disjoint_image_disjointChartPiece
    A.parametrization A.domain

/-- Disjointification preserves the union of controlled chart images. -/
theorem iUnion_image_piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) :
    (⋃ i, A.parametrization i '' A.piece I i) =
      ⋃ i, A.parametrization i '' A.domain i :=
  iUnion_image_disjointChartPiece A.parametrization A.domain

/-- The disjointified images still cover every manifold-interior point. -/
theorem interior_subset_iUnion_image_piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) :
    I.interior M ⊆ ⋃ i, A.parametrization i '' A.piece I i := by
  rw [A.iUnion_image_piece I]
  exact A.interior_subset_iUnion_image

/-- The Riemannian area measure contributed by a disjoint controlled
interior atlas. -/
def areaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) : Measure M :=
  riemannianAtlasAreaMeasure I A.parametrization (A.piece I)

end ControlledInteriorAtlas

/-- The analytic area conclusion for a globally Lipschitz surface map and a
controlled disjoint atlas.  The two remaining regularity inputs are stated
exactly where Rademacher must supply them: manifold differentiability and
measurability of the intrinsic Jacobian on each chart contribution. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_controlledInteriorAtlas
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) (G : M → ℂ) (omega : Set ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G)
    (hJacobianMeas : ∀ i, AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I G x))
      (riemannianChartAreaMeasure I (A.parametrization i) (A.piece I i)))
    (hGdiff : ∀ i, ∀ᵐ z ∂volume.restrict (A.piece I i),
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (A.parametrization i z))
    (hcoverage : omega ⊆ G '' I.interior M) :
    volume omega ≤
      ∫⁻ x, ENNReal.ofReal (riemannianTwoJacobian I G x)
        ∂A.areaMeasure I := by
  apply
    complex_volume_le_lintegral_riemannianTwoJacobian_of_atlas_of_ae_mdifferentiable
      I A.parametrization (A.piece I) A.domain G omega
  · exact A.measurableSet_piece I
  · exact A.isOpen_domain
  · exact A.piece_subset_domain I
  · intro i
    exact hG.comp_lipschitzOnWith (A.lipschitzOnWith_parametrization i)
  · intro i
    exact ((A.continuousOn_parametrization i).mono
      (A.piece_subset_domain I i)).aemeasurable
        (A.measurableSet_piece I i)
  · intro i
    exact AEMeasurable.mono_set (A.piece_subset_domain I i)
      (aemeasurable_riemannianChartDensity_of_contMDiffOn I
        (A.parametrization i) (A.domain i) (A.isOpen_domain i)
          (A.contMDiffOn_parametrization i))
  · exact hJacobianMeas
  · intro i
    filter_upwards [ae_restrict_mem (A.measurableSet_piece I i),
      hGdiff i] with z hzPiece hzG
    have hzDomain : z ∈ A.domain i := A.piece_subset_domain I i hzPiece
    exact ⟨((A.contMDiffOn_parametrization i z hzDomain).contMDiffAt
      ((A.isOpen_domain i).mem_nhds hzDomain)).mdifferentiableAt
        one_ne_zero, hzG⟩
  · rintro y hy
    rcases hcoverage hy with ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp
      (A.interior_subset_iUnion_image_piece I hx) with ⟨i, z, hz, rfl⟩
    exact Set.mem_iUnion.mpr
      ⟨i, ⟨A.parametrization i z, ⟨z, hz, rfl⟩, rfl⟩⟩

end

end GromovFilling
