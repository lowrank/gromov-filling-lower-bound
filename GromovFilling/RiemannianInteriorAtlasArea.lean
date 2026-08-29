import GromovFilling.RiemannianChartDisjointification
import GromovFilling.RiemannianChartTransition
import GromovFilling.RiemannianInteriorChart
import Mathlib.MeasureTheory.Constructions.Polish.Basic

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
open scoped Bundle ENNReal Function Manifold NNReal Topology

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
  coordinate : ℕ → M → ℂ
  domain : ℕ → Set ℂ
  lipschitzConstant : ℕ → ℝ≥0
  isOpen_domain : ∀ i, IsOpen (domain i)
  continuousOn_parametrization :
    ∀ i, ContinuousOn (parametrization i) (domain i)
  contMDiffOn_parametrization :
    ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) I 1 (parametrization i) (domain i)
  injOn_parametrization :
    ∀ i, Set.InjOn (parametrization i) (domain i)
  coordinate_parametrization :
    ∀ i z, z ∈ domain i → coordinate i (parametrization i z) = z
  mdifferentiableAt_coordinate :
    ∀ i y, y ∈ parametrization i '' domain i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) (coordinate i) y
  mdifferentiableAt_of_differentiableAt_comp :
    ∀ i (G : M → ℂ) z, z ∈ domain i →
      DifferentiableAt ℝ (G ∘ parametrization i) z →
        MDifferentiableAt I 𝓘(ℝ, ℂ) G (parametrization i z)
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

/-- Pad the forward coordinate maps of a finite interior-chart family by
the constant zero map after the final index. -/
def finControlledInteriorCoordinate
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) {n : ℕ} (centers : Fin n → M)
    (i : ℕ) : M → ℂ :=
  if hi : i < n then
    e.symm ∘ extChartAt I (centers ⟨i, hi⟩)
  else
    fun _ ↦ 0

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
  let coord : ℕ → M → ℂ :=
    finControlledInteriorCoordinate I e centers
  let domains : ℕ → Set ℂ :=
    finControlledInteriorDomain I e centers
  let K : ℕ → ℝ≥0 :=
    finControlledInteriorLipschitzConstant I centers
  refine
    { parametrization := F
      coordinate := coord
      domain := domains
      lipschitzConstant := K
      isOpen_domain := ?_
      continuousOn_parametrization := ?_
      contMDiffOn_parametrization := ?_
      injOn_parametrization := ?_
      coordinate_parametrization := ?_
      mdifferentiableAt_coordinate := ?_
      mdifferentiableAt_of_differentiableAt_comp := ?_
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
    · have hsubset :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩))
      simpa [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi] using
        (injOn_interiorComplexExtChart I e (centers ⟨i, hi⟩)).mono
          hsubset
    · simp [domains, finControlledInteriorDomain, hi]
  · intro i z hz
    by_cases hi : i < n
    · have hzControlled : z ∈
          chosenControlledInteriorComplexChartDomain I e (centers ⟨i, hi⟩) := by
        simpa [domains, finControlledInteriorDomain, hi] using hz
      have hzFull : z ∈
          interiorComplexExtChartDomain I e (centers ⟨i, hi⟩) :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩)) hzControlled
      have htarget : e z ∈
          (extChartAt I (centers ⟨i, hi⟩)).target :=
        interior_subset hzFull
      rw [show coord i =
          e.symm ∘ extChartAt I (centers ⟨i, hi⟩) by
        simp [coord, finControlledInteriorCoordinate, hi]]
      rw [show F i = interiorComplexExtChart I e (centers ⟨i, hi⟩) by
        simp [F, finControlledInteriorParametrization, hi]]
      change e.symm
        (extChartAt I (centers ⟨i, hi⟩)
          ((extChartAt I (centers ⟨i, hi⟩)).symm (e z))) = z
      rw [(extChartAt I (centers ⟨i, hi⟩)).right_inv htarget,
        e.symm_apply_apply]
    · simp [domains, finControlledInteriorDomain, hi] at hz
  · intro i y hy
    by_cases hi : i < n
    · rcases hy with ⟨z, hz, rfl⟩
      have hzControlled : z ∈
          chosenControlledInteriorComplexChartDomain I e (centers ⟨i, hi⟩) := by
        simpa [domains, finControlledInteriorDomain, hi] using hz
      have hzFull : z ∈
          interiorComplexExtChartDomain I e (centers ⟨i, hi⟩) :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩)) hzControlled
      have htarget : e z ∈
          (extChartAt I (centers ⟨i, hi⟩)).target :=
        interior_subset hzFull
      have hsourceExt :
          (extChartAt I (centers ⟨i, hi⟩)).symm (e z) ∈
            (extChartAt I (centers ⟨i, hi⟩)).source :=
        (extChartAt I (centers ⟨i, hi⟩)).map_target htarget
      have hsource :
          (extChartAt I (centers ⟨i, hi⟩)).symm (e z) ∈
            (chartAt H (centers ⟨i, hi⟩)).source := by
        simpa only [extChartAt_source] using hsourceExt
      have hcoord : MDifferentiableAt I 𝓘(ℝ, ℂ)
          (e.symm ∘ extChartAt I (centers ⟨i, hi⟩))
          ((extChartAt I (centers ⟨i, hi⟩)).symm (e z)) :=
        e.symm.toContinuousLinearEquiv.differentiableAt.comp_mdifferentiableAt
          (mdifferentiableAt_extChartAt hsource)
      simpa [coord, F, finControlledInteriorCoordinate,
        finControlledInteriorParametrization, interiorComplexExtChart, hi]
        using hcoord
    · simp [F, domains, finControlledInteriorParametrization,
        finControlledInteriorDomain, hi] at hy
  · intro i G z hz hdiff
    by_cases hi : i < n
    · have hzControlled : z ∈
          chosenControlledInteriorComplexChartDomain I e (centers ⟨i, hi⟩) := by
        simpa [domains, finControlledInteriorDomain, hi] using hz
      have hzFull : z ∈
          interiorComplexExtChartDomain I e (centers ⟨i, hi⟩) :=
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
          I e (chosenInteriorChartControl I (centers ⟨i, hi⟩)) hzControlled
      have hdiff' : DifferentiableAt ℝ
          (G ∘ interiorComplexExtChart I e (centers ⟨i, hi⟩)) z := by
        simpa [F, finControlledInteriorParametrization, hi] using hdiff
      simpa [F, finControlledInteriorParametrization, hi] using
        mdifferentiableAt_of_differentiableAt_comp_interiorComplexExtChart
          I e (centers ⟨i, hi⟩) G hzFull hdiff'
    · simp [domains, finControlledInteriorDomain, hi] at hz
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

/-- The part of one controlled coordinate domain whose image lies in a
second controlled chart image. -/
def overlapDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) : Set ℂ :=
  A.domain i ∩ A.parametrization i ⁻¹'
    (B.parametrization j '' B.domain j)

/-- The change of coordinates from one controlled chart to another. -/
def coordinateTransition
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) : ℂ → ℂ :=
  B.coordinate j ∘ A.parametrization i

/-- Controlled overlap domains are open in the complex coordinate plane. -/
theorem isOpen_overlapDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) :
    IsOpen (A.overlapDomain I B i j) :=
  (A.continuousOn_parametrization i).isOpen_inter_preimage
    (A.isOpen_domain i) (B.isOpen_image j)

/-- The first coordinate of an overlap lies in its original chart domain. -/
theorem overlapDomain_subset_domain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) :
    A.overlapDomain I B i j ⊆ A.domain i :=
  inter_subset_left

/-- A chart coordinate followed by its parametrization is the identity on
the chart image. -/
theorem parametrization_coordinate
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (i : ℕ) {y : M}
    (hy : y ∈ A.parametrization i '' A.domain i) :
    A.parametrization i (A.coordinate i y) = y := by
  rcases hy with ⟨z, hz, rfl⟩
  rw [A.coordinate_parametrization i z hz]

/-- A coordinate transition sends its overlap domain into the target chart
domain. -/
theorem coordinateTransition_mem_domain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) {z : ℂ}
    (hz : z ∈ A.overlapDomain I B i j) :
    A.coordinateTransition I B i j z ∈ B.domain j := by
  rcases hz.2 with ⟨w, hw, hzw⟩
  change B.coordinate j (A.parametrization i z) ∈ B.domain j
  rw [← hzw, B.coordinate_parametrization j w hw]
  exact hw

/-- On an overlap, changing coordinates and using the target
parametrization recovers the original point. -/
theorem parametrization_coordinateTransition
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) {z : ℂ}
    (hz : z ∈ A.overlapDomain I B i j) :
    B.parametrization j (A.coordinateTransition I B i j z) =
      A.parametrization i z := by
  exact B.parametrization_coordinate I j hz.2

/-- Coordinate transitions are differentiable at every point of their open
overlap domain. -/
theorem differentiableAt_coordinateTransition
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) {z : ℂ}
    (hz : z ∈ A.overlapDomain I B i j) :
    DifferentiableAt ℝ (A.coordinateTransition I B i j) z := by
  have hA : MDifferentiableAt 𝓘(ℝ, ℂ) I
      (A.parametrization i) z :=
    ((A.contMDiffOn_parametrization i z hz.1).contMDiffAt
      ((A.isOpen_domain i).mem_nhds hz.1)).mdifferentiableAt
        one_ne_zero
  have hB : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (B.coordinate j) (A.parametrization i z) :=
    B.mdifferentiableAt_coordinate j (A.parametrization i z) hz.2
  exact (hB.comp z hA).differentiableAt

/-- A coordinate transition is injective on its overlap domain. -/
theorem injOn_coordinateTransition
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) :
    Set.InjOn (A.coordinateTransition I B i j)
      (A.overlapDomain I B i j) := by
  intro z hz w hw hzw
  apply A.injOn_parametrization i hz.1 hw.1
  rw [← A.parametrization_coordinateTransition I B i j hz,
    ← A.parametrization_coordinateTransition I B i j hw, hzw]

/-- A coordinate transition lands in the reverse overlap domain. -/
theorem coordinateTransition_mem_overlapDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) {z : ℂ}
    (hz : z ∈ A.overlapDomain I B i j) :
    A.coordinateTransition I B i j z ∈ B.overlapDomain I A j i := by
  refine ⟨A.coordinateTransition_mem_domain I B i j hz, ?_⟩
  change B.parametrization j (A.coordinateTransition I B i j z) ∈
    A.parametrization i '' A.domain i
  rw [A.parametrization_coordinateTransition I B i j hz]
  exact ⟨z, hz.1, rfl⟩

/-- The two coordinate transitions identify their open overlap domains. -/
theorem image_coordinateTransition_overlapDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) :
    A.coordinateTransition I B i j '' A.overlapDomain I B i j =
      B.overlapDomain I A j i := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact A.coordinateTransition_mem_overlapDomain I B i j hz
  · intro w hw
    let z := B.coordinateTransition I A j i w
    have hz : z ∈ A.overlapDomain I B i j :=
      B.coordinateTransition_mem_overlapDomain I A j i hw
    refine ⟨z, hz, ?_⟩
    apply B.injOn_parametrization j
      (A.coordinateTransition_mem_domain I B i j hz) hw.1
    rw [A.parametrization_coordinateTransition I B i j hz,
      B.parametrization_coordinateTransition I A j i hw]

/-- The target parametrization composed with a coordinate transition agrees
locally with the source parametrization. -/
theorem parametrization_comp_coordinateTransition_eventuallyEq
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) {z : ℂ}
    (hz : z ∈ A.overlapDomain I B i j) :
    (B.parametrization j ∘ A.coordinateTransition I B i j) =ᶠ[𝓝 z]
      A.parametrization i := by
  filter_upwards [(A.isOpen_overlapDomain I B i j).mem_nhds hz] with w hw
  exact A.parametrization_coordinateTransition I B i j hw

/-- The Riemannian area contribution of a controlled chart agrees with that
of any second controlled chart on their common image. -/
theorem riemannianChartAreaMeasure_overlap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ) :
    riemannianChartAreaMeasure I (A.parametrization i)
        (A.overlapDomain I B i j) =
      riemannianChartAreaMeasure I (B.parametrization j)
        (B.overlapDomain I A j i) := by
  let s : Set ℂ := A.overlapDomain I B i j
  let e : ℂ → ℂ := A.coordinateTransition I B i j
  let FA : ℂ → M := A.parametrization i
  let FB : ℂ → M := B.parametrization j
  have hsOpen : IsOpen s := by
    simpa only [s] using A.isOpen_overlapDomain I B i j
  have hs : MeasurableSet s := hsOpen.measurableSet
  have hsA : s ⊆ A.domain i := by
    simpa only [s] using A.overlapDomain_subset_domain I B i j
  have himage : e '' s = B.overlapDomain I A j i := by
    simpa only [e, s] using A.image_coordinateTransition_overlapDomain I B i j
  have heDiff : ∀ z ∈ s, DifferentiableAt ℝ e z := by
    intro z hz
    exact A.differentiableAt_coordinateTransition I B i j hz
  have heInj : Set.InjOn e s := by
    simpa only [e, s] using A.injOn_coordinateTransition I B i j
  have hFBdiff : ∀ z ∈ s,
      MDifferentiableAt 𝓘(ℝ, ℂ) I FB (e z) := by
    intro z hz
    have hez : e z ∈ B.domain j :=
      A.coordinateTransition_mem_domain I B i j hz
    exact ((B.contMDiffOn_parametrization j (e z) hez).contMDiffAt
      ((B.isOpen_domain j).mem_nhds hez)).mdifferentiableAt one_ne_zero
  have hlocal : ∀ z ∈ s, (FB ∘ e) =ᶠ[𝓝 z] FA := by
    intro z hz
    simpa only [FA, FB, e, s] using
      A.parametrization_comp_coordinateTransition_eventuallyEq I B i j hz
  have hFAmeas : AEMeasurable FA (volume.restrict s) :=
    ((A.continuousOn_parametrization i).mono hsA).aemeasurable hs
  have hcompEq : (FB ∘ e) =ᵐ[volume.restrict s] FA := by
    filter_upwards [ae_restrict_mem hs] with z hz
    exact (hlocal z hz).self_of_nhds
  have hFBcompMeas : AEMeasurable (FB ∘ e) (volume.restrict s) :=
    hFAmeas.congr hcompEq.symm
  have hFBmeas : AEMeasurable FB (volume.restrict (e '' s)) := by
    rw [himage]
    exact ((B.continuousOn_parametrization j).mono
      (B.overlapDomain_subset_domain I A j i)).aemeasurable
        (B.isOpen_overlapDomain I A j i).measurableSet
  have hDensityA : AEMeasurable (riemannianChartDensity I FA)
      (volume.restrict s) := by
    exact AEMeasurable.mono_set hsA
      (aemeasurable_riemannianChartDensity_of_contMDiffOn I
        (A.parametrization i) (A.domain i) (A.isOpen_domain i)
          (A.contMDiffOn_parametrization i))
  have hDensityEq : riemannianChartDensity I (FB ∘ e)
      =ᵐ[volume.restrict s] riemannianChartDensity I FA := by
    filter_upwards [ae_restrict_mem hs] with z hz
    exact riemannianChartDensity_congr_of_eventuallyEq
      I (FB ∘ e) FA z (hlocal z hz)
  have hDensityCompMeas : AEMeasurable
      (riemannianChartDensity I (FB ∘ e)) (volume.restrict s) :=
    hDensityA.congr hDensityEq.symm
  have hDensityB : AEMeasurable (riemannianChartDensity I FB)
      (volume.restrict (e '' s)) := by
    rw [himage]
    exact AEMeasurable.mono_set
      (B.overlapDomain_subset_domain I A j i)
      (aemeasurable_riemannianChartDensity_of_contMDiffOn I
        (B.parametrization j) (B.domain j) (B.isOpen_domain j)
          (B.contMDiffOn_parametrization j))
  calc
    riemannianChartAreaMeasure I (A.parametrization i)
        (A.overlapDomain I B i j) =
        riemannianChartAreaMeasure I FA s := by rfl
    _ = riemannianChartAreaMeasure I (FB ∘ e) s :=
      riemannianChartAreaMeasure_congr_of_eventuallyEqOn
        I FA (FB ∘ e) s hs (fun z hz ↦ (hlocal z hz).symm)
    _ = riemannianChartAreaMeasure I FB (e '' s) :=
      riemannianChartAreaMeasure_comp_of_aemeasurable
        I e FB s hs heDiff heInj hFBdiff hFBcompMeas hFBmeas
          hDensityCompMeas hDensityB
    _ = riemannianChartAreaMeasure I (B.parametrization j)
        (B.overlapDomain I A j i) := by
      rw [himage]

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

/-- A globally Lipschitz surface map is manifold-differentiable almost
everywhere along every disjoint controlled chart piece.  Rademacher is
applied to the planar pullback and the local inverse-chart field transfers
the result back to the manifold. -/
theorem ae_mdifferentiableAt_of_lipschitzWith
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (G : M → ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (A.piece I i),
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (A.parametrization i z) := by
  have hLipschitz : LipschitzOnWith
      (KG * A.lipschitzConstant i) (G ∘ A.parametrization i)
      (A.domain i) :=
    hG.comp_lipschitzOnWith (A.lipschitzOnWith_parametrization i)
  have hdiffWithin := hLipschitz.ae_differentiableWithinAt (μ := volume)
    (A.isOpen_domain i).measurableSet
  have hdiffDomain : ∀ᵐ z ∂volume.restrict (A.domain i),
      MDifferentiableAt I 𝓘(ℝ, ℂ) G (A.parametrization i z) := by
    filter_upwards [ae_restrict_mem (A.isOpen_domain i).measurableSet,
      hdiffWithin] with z hz hdiff
    exact A.mdifferentiableAt_of_differentiableAt_comp i G z hz
      (hdiff.differentiableAt ((A.isOpen_domain i).mem_nhds hz))
  exact ae_mono
    (Measure.restrict_mono (A.piece_subset_domain I i) le_rfl)
      hdiffDomain

/-- The intrinsic two-Jacobian of a globally Lipschitz map is almost
everywhere measurable for every controlled chart contribution.  The proof
uses the measurable embedding of each injective chart piece, planar
measurability of `fderiv`, and the intrinsic chain rule. -/
theorem aemeasurable_riemannianTwoJacobian_of_lipschitzWith
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) (G : M → ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G) (i : ℕ) :
    AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I G x))
      (riemannianChartAreaMeasure I (A.parametrization i)
        (A.piece I i)) := by
  let F : ℂ → M := A.parametrization i
  let s : Set ℂ := A.piece I i
  let q : M → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal (riemannianTwoJacobian I G x)
  let d : ℂ → ℝ≥0∞ := riemannianChartDensity I F
  let dNN : ℂ → ℝ≥0 := fun z ↦ (d z).toNNReal
  let planarJ : ℂ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal
      (riemannianTwoJacobian 𝓘(ℝ, ℂ) (G ∘ F) z)
  have hs : MeasurableSet s := by
    simpa only [s] using A.measurableSet_piece I i
  have hsDomain : s ⊆ A.domain i := by
    simpa only [s] using A.piece_subset_domain I i
  have hFcont : ContinuousOn F s := by
    exact (A.continuousOn_parametrization i).mono hsDomain
  have hFinj : Set.InjOn F s := by
    exact (A.injOn_parametrization i).mono hsDomain
  have hFembed : MeasurableEmbedding (s.restrict F) :=
    hFcont.measurableEmbedding hs hFinj
  have hFbase : AEMeasurable F (volume.restrict s) :=
    hFcont.aemeasurable hs
  have hd : AEMeasurable d (volume.restrict s) := by
    simpa only [d, F] using
      AEMeasurable.mono_set hsDomain
        (aemeasurable_riemannianChartDensity_of_contMDiffOn I
          (A.parametrization i) (A.domain i) (A.isOpen_domain i)
            (A.contMDiffOn_parametrization i))
  have hdNN : AEMeasurable dNN (volume.restrict s) := by
    exact hd.ennreal_toNNReal
  have hplanarJ : Measurable planarJ := by
    simp only [planarJ,
      riemannianTwoJacobian_complex_eq_abs_det_fderiv]
    exact ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp
        (ContinuousLinearMap.continuous_det.measurable.comp
          (measurable_fderiv ℝ (G ∘ F))))
  have hchain : planarJ =ᵐ[volume.restrict s]
      fun z ↦ d z * q (F z) := by
    filter_upwards [ae_restrict_mem hs,
      A.ae_mdifferentiableAt_of_lipschitzWith I G hG i] with
        z hz hGdiff
    have hzDomain : z ∈ A.domain i := hsDomain hz
    have hFdiff : MDifferentiableAt 𝓘(ℝ, ℂ) I F z := by
      exact ((A.contMDiffOn_parametrization i z hzDomain).contMDiffAt
        ((A.isOpen_domain i).mem_nhds hzDomain)).mdifferentiableAt
          one_ne_zero
    simpa only [planarJ, d, q, F] using
      ofReal_riemannianTwoJacobian_comp_eq_chartDensity_mul
        I F G z hFdiff hGdiff
  have hproduct : AEMeasurable (fun z ↦ d z * q (F z))
      (volume.restrict s) :=
    hplanarJ.aemeasurable.restrict.congr hchain
  have hdNNcoe : (fun z ↦ (dNN z : ℝ≥0∞)) = d := by
    funext z
    exact ENNReal.coe_toNNReal (by
      simp [d, F, riemannianChartDensity])
  have hqFweighted : AEMeasurable (fun z ↦ q (F z))
      ((volume.restrict s).withDensity d) := by
    rw [← hdNNcoe]
    apply (aemeasurable_withDensity_ennreal_iff' hdNN).2
    have hdNNcoe_apply : ∀ z, (dNN z : ℝ≥0∞) = d z :=
      congrFun hdNNcoe
    simpa only [hdNNcoe_apply] using hproduct
  let ν : Measure ℂ := (volume.restrict s).withDensity d
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
  have hqSubtype : AEMeasurable (q ∘ s.restrict F) μs := by
    have hqRestrict : AEMeasurable (fun z ↦ q (F z)) (ν.restrict s) := by
      rw [hνrestrict]
      simpa only [ν] using hqFweighted
    have hqComap :=
      (aemeasurable_restrict_iff_comap_subtype hs).1 hqRestrict
    simpa only [μs, Function.comp_apply, Set.restrict_apply] using hqComap
  have hqMappedSubtype : AEMeasurable q (μs.map (s.restrict F)) :=
    hFembed.aemeasurable_map_iff.2 hqSubtype
  have hFafterCoe : AEMeasurable F
      (μs.map ((↑) : s → ℂ)) := by
    rw [hcoeMap]
    exact hFweighted
  have hmap : μs.map (s.restrict F) = ν.map F := by
    change μs.map (F ∘ ((↑) : s → ℂ)) = ν.map F
    rw [← hFafterCoe.map_map_of_aemeasurable
      measurable_subtype_coe.aemeasurable]
    exact congrArg (Measure.map F) hcoeMap
  simpa only [riemannianChartAreaMeasure, q, F, s, ν, hmap] using
    hqMappedSubtype

end ControlledInteriorAtlas

/-- The analytic area conclusion for a globally Lipschitz surface map and a
controlled disjoint atlas.  Planar Rademacher supplies manifold
differentiability, and chartwise measurable embeddings transfer planar
Jacobian measurability to the intrinsic two-Jacobian automatically. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_controlledInteriorAtlas
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) (G : M → ℂ) (omega : Set ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G)
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
  · intro i
    exact A.aemeasurable_riemannianTwoJacobian_of_lipschitzWith I G hG i
  · intro i
    filter_upwards [ae_restrict_mem (A.measurableSet_piece I i),
      A.ae_mdifferentiableAt_of_lipschitzWith I G hG i] with z hzPiece hzG
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
