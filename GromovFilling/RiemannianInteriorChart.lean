import GromovFilling.RiemannianChartDensity
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Complex parametrizations of manifold-interior chart pieces

For a two-dimensional manifold with boundary, the extended chart target is
not open in the ambient model vector space.  Its interior is open, however,
and an isometric identification of that vector space with `ℂ` turns the
inverse extended chart into an ordinary complex parametrization.

These interior chart pieces are open and measurable, their parametrizations
are smooth, and their images are exactly the intersections of the original
chart sources with the manifold interior.  Compactness therefore supplies a
finite family whose images cover every interior point, even though the
interior itself need not be compact.
-/

open Bundle MeasureTheory Set
open Manifold Metric
open scoped Bundle ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The complex coordinate domain obtained by pulling back the interior of
an extended chart target along a linear isometry `ℂ ≃ E`. -/
def interiorComplexExtChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) : Set ℂ :=
  e ⁻¹' interior (extChartAt I x).target

/-- The inverse extended chart, parametrized by complex coordinates on the
interior of its target. -/
def interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) : ℂ → M :=
  (extChartAt I x).symm ∘ e

/-- An interior complex chart domain is open in `ℂ`. -/
theorem isOpen_interiorComplexExtChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    IsOpen (interiorComplexExtChartDomain I e x) :=
  isOpen_interior.preimage e.continuous

/-- An interior complex inverse chart is continuous on its coordinate
domain. -/
theorem continuousOn_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    ContinuousOn (interiorComplexExtChart I e x)
      (interiorComplexExtChartDomain I e x) := by
  apply (continuousOn_extChartAt_symm x).comp e.continuous.continuousOn
  intro z hz
  exact interior_subset hz

/-- An interior complex inverse chart is `C¹` on its coordinate domain. -/
theorem contMDiffOn_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    ContMDiffOn 𝓘(ℝ, ℂ) I 1 (interiorComplexExtChart I e x)
      (interiorComplexExtChartDomain I e x) := by
  apply (contMDiffOn_extChartAt_symm x).comp
    e.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn
  intro z hz
  change e z ∈ (extChartAt I x).target
  exact interior_subset hz

/-- An interior complex inverse chart is manifold-differentiable at every
point of its open coordinate domain. -/
theorem mdifferentiableAt_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) {z : ℂ}
    (hz : z ∈ interiorComplexExtChartDomain I e x) :
    MDifferentiableAt 𝓘(ℝ, ℂ) I (interiorComplexExtChart I e x) z := by
  exact ((contMDiffOn_interiorComplexExtChart I e x z hz).contMDiffAt
    ((isOpen_interiorComplexExtChartDomain I e x).mem_nhds hz)).mdifferentiableAt
      one_ne_zero

/-- Differentiability of a map in an interior inverse-chart coordinate
system implies manifold differentiability of the original map.  This is the
local inverse step that transfers planar Rademacher differentiability back to
the surface. -/
theorem mdifferentiableAt_of_differentiableAt_comp_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) (G : M → ℂ) {z : ℂ}
    (hz : z ∈ interiorComplexExtChartDomain I e x)
    (hG : DifferentiableAt ℝ
      (G ∘ interiorComplexExtChart I e x) z) :
    MDifferentiableAt I 𝓘(ℝ, ℂ) G
      (interiorComplexExtChart I e x z) := by
  let F : ℂ → M := interiorComplexExtChart I e x
  let coord : M → ℂ := e.symm ∘ extChartAt I x
  have htarget : e z ∈ (extChartAt I x).target := interior_subset hz
  have hySourceExt : F z ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target htarget
  have hySource : F z ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using hySourceExt
  have hcoordValue : coord (F z) = z := by
    change e.symm (extChartAt I x ((extChartAt I x).symm (e z))) = z
    rw [(extChartAt I x).right_inv htarget, e.symm_apply_apply]
  have hcoord : MDifferentiableAt I 𝓘(ℝ, ℂ) coord (F z) := by
    exact e.symm.toContinuousLinearEquiv.differentiableAt.comp_mdifferentiableAt
      (mdifferentiableAt_extChartAt hySource)
  have hGcoord : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (G ∘ F) (coord (F z)) := by
    rw [hcoordValue]
    exact hG.mdifferentiableAt
  have hcomp : MDifferentiableAt I 𝓘(ℝ, ℂ)
      ((G ∘ F) ∘ coord) (F z) :=
    hGcoord.comp (F z) hcoord
  have hlocal : ((G ∘ F) ∘ coord) =ᶠ[𝓝 (F z)] G := by
    filter_upwards [(chartAt H x).open_source.mem_nhds hySource] with y hy
    change G ((extChartAt I x).symm
      (e (e.symm (extChartAt I x y)))) = G y
    rw [e.apply_symm_apply, (extChartAt I x).left_inv (by
      simpa only [extChartAt_source] using hy)]
  exact hcomp.congr_of_eventuallyEq hlocal.symm

/-- The image of an interior complex inverse chart is precisely the part of
the original chart source lying in the manifold interior. -/
theorem image_interiorComplexExtChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    interiorComplexExtChart I e x '' interiorComplexExtChartDomain I e x =
      (chartAt H x).source ∩ I.interior M := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have htarget : e z ∈ (extChartAt I x).target := interior_subset hz
    have hsourceExt : (extChartAt I x).symm (e z) ∈
        (extChartAt I x).source :=
      (extChartAt I x).map_target htarget
    have hsource : (extChartAt I x).symm (e z) ∈
        (chartAt H x).source := by
      simpa only [extChartAt_source] using hsourceExt
    refine ⟨hsource, ?_⟩
    change I.IsInteriorPoint ((extChartAt I x).symm (e z))
    rw [I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
      (chart_mem_atlas H x) hsource]
    change extChartAt I x ((extChartAt I x).symm (e z)) ∈
      interior (extChartAt I x).target
    rw [(extChartAt I x).right_inv htarget]
    exact hz
  · rintro ⟨hsource, hinterior⟩
    have hsourceExt : y ∈ (extChartAt I x).source := by
      simpa only [extChartAt_source] using hsource
    have hcoord : extChartAt I x y ∈ interior (extChartAt I x).target := by
      change I.IsInteriorPoint y at hinterior
      exact (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
        (chart_mem_atlas H x) hsource).mp hinterior
    let z : ℂ := e.symm (extChartAt I x y)
    refine ⟨z, ?_, ?_⟩
    · change e z ∈ interior (extChartAt I x).target
      simpa only [z, LinearIsometryEquiv.apply_symm_apply] using hcoord
    · change (extChartAt I x).symm (e z) = y
      rw [show e z = extChartAt I x y by
        simp only [z, LinearIsometryEquiv.apply_symm_apply]]
      exact (extChartAt I x).left_inv hsourceExt

/-- Interior complex inverse charts are injective on their coordinate
domains. -/
theorem injOn_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    Set.InjOn (interiorComplexExtChart I e x)
      (interiorComplexExtChartDomain I e x) := by
  intro z hz w hw hzw
  apply e.injective
  exact (extChartAt I x).symm.injOn (interior_subset hz)
    (interior_subset hw) hzw

/-- The image of an interior complex chart domain is open in the manifold. -/
theorem isOpen_image_interiorComplexExtChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    IsOpen (interiorComplexExtChart I e x ''
      interiorComplexExtChartDomain I e x) := by
  rw [image_interiorComplexExtChartDomain I e x]
  exact (chartAt H x).open_source.inter (I.isOpen_interior one_ne_zero)

/-- An interior complex inverse chart is almost everywhere measurable on
its coordinate domain. -/
theorem aemeasurable_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    AEMeasurable (interiorComplexExtChart I e x)
      (volume.restrict (interiorComplexExtChartDomain I e x)) :=
  (continuousOn_interiorComplexExtChart I e x).aemeasurable
    (isOpen_interiorComplexExtChartDomain I e x).measurableSet

/-- The intrinsic density of a `C¹` interior complex inverse chart is almost
everywhere measurable on its coordinate domain. -/
theorem aemeasurable_riemannianChartDensity_interiorComplexExtChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) :
    AEMeasurable
      (riemannianChartDensity I (interiorComplexExtChart I e x))
      (volume.restrict (interiorComplexExtChartDomain I e x)) :=
  aemeasurable_riemannianChartDensity_of_contMDiffOn I
    (interiorComplexExtChart I e x) (interiorComplexExtChartDomain I e x)
    (isOpen_interiorComplexExtChartDomain I e x)
    (contMDiffOn_interiorComplexExtChart I e x)

/-- A compact manifold admits finitely many interior complex inverse charts
whose images cover its entire manifold interior.  The centers are selected
from a finite subcover of the original chart sources. -/
theorem exists_fin_interiorComplexExtChart_cover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [CompactSpace M] (e : ℂ ≃ₗᵢ[ℝ] E) :
    ∃ n : ℕ, ∃ centers : Fin n → M,
      I.interior M ⊆ ⋃ i, interiorComplexExtChart I e (centers i) ''
        interiorComplexExtChartDomain I e (centers i) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset M,
      (Set.univ : Set M) ⊆ ⋃ x ∈ t, (chartAt H x).source := by
    refine isCompact_univ.elim_finite_subcover
      (fun x : M ↦ (chartAt H x).source)
      (fun x ↦ (chartAt H x).open_source) ?_
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source H x⟩
  refine ⟨t.card, fun j ↦ t.equivFin.symm j, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  rw [image_interiorComplexExtChartDomain I e]
  simpa using And.intro hyx hy

/-- A bounded derivative of an inverse extended chart on a convex set gives
a Lipschitz complex parametrization there.  The proof pulls the line segment
between two coordinate points back to the manifold and bounds its
Riemannian path length. -/
theorem lipschitzOnWith_interiorComplexExtChart_of_convex
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) (t : Set E)
    (ht : Convex ℝ t) (htarget : t ⊆ (extChartAt I x).target)
    {C : ℝ≥0}
    (hderiv : ∀ y ∈ t,
      ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ ≤ C) :
    LipschitzOnWith C (interiorComplexExtChart I e x) (e ⁻¹' t) := by
  intro z hz w hw
  change e z ∈ t at hz
  change e w ∈ t at hw
  rw [IsRiemannianManifold.out (I := I)]
  rw [← e.edist_map z w]
  let η := ContinuousAffineMap.lineMap (R := ℝ) (e z) (e w)
  set γ := (extChartAt I x).symm ∘ η
  have hη : Icc (0 : ℝ) 1 ⊆ ⇑η ⁻¹' t := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact ht.segment_subset hz hw
  have hηtarget : Icc (0 : ℝ) 1 ⊆
      ⇑η ⁻¹' (extChartAt I x).target :=
    hη.trans (preimage_mono htarget)
  have η_smooth : CMDiff[Icc (0 : ℝ) 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hpath : riemannianEDist I
      (interiorComplexExtChart I e x z)
      (interiorComplexExtChart I e x w) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hηtarget
    · simp [γ, η, interiorComplexExtChart,
        ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, interiorComplexExtChart,
        ContinuousAffineMap.coe_lineMap_eq]
  apply hpath.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,
    pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro a ha
  have hcomp : mfderiv[Icc (0 : ℝ) 1] γ a =
      (mfderiv[range I] (extChartAt I x).symm (η a)) ∘L
        (mfderiv[Icc (0 : ℝ) 1] η a) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hηtarget ha)
    · exact η_smooth.mdifferentiableOn one_ne_zero a ha
    · exact hηtarget.trans
        (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one a ha
  have happly : mfderiv[Icc (0 : ℝ) 1] γ a 1 =
      (mfderiv[range I] (extChartAt I x).symm (η a))
        (mfderiv[Icc (0 : ℝ) 1] η a 1) :=
    congr($hcomp 1)
  rw [happly]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact hderiv (η a) (hη ha)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

/-- Quantitative local data for an inverse extended chart: on a small ball
inside the model range, the inverse chart stays in its target and its
derivative has a uniform bound. -/
structure InteriorChartControl
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (x : M) where
  C : ℝ≥0
  C_pos : 0 < C
  r : ℝ
  r_pos : 0 < r
  controlled :
    ball (extChartAt I x x) r ∩ range I ⊆
      (extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C}

/-- Every point has quantitative inverse-chart control data. -/
theorem nonempty_interiorChartControl
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (x : M) : Nonempty (InteriorChartControl I x) := by
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with
    ⟨C, C_pos, hC⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆
        (extChartAt I x).target ∩
          {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    mem_nhdsWithin_iff.1
      (Filter.inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  exact ⟨⟨C, C_pos, r, r_pos, hr⟩⟩

/-- The convex interior model set on which a controlled inverse chart will
be used. -/
def controlledInteriorChartSet
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) : Set E :=
  ball (extChartAt I x x) c.r ∩ interior (range I)

/-- The controlled complex coordinate domain. -/
def controlledInteriorComplexChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) {x : M} (c : InteriorChartControl I x) : Set ℂ :=
  e ⁻¹' controlledInteriorChartSet I c

/-- The ambient manifold neighborhood whose interior part is parametrized
by the controlled complex chart. -/
def controlledInteriorChartNeighborhood
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) : Set M :=
  (extChartAt I x).source ∩
    extChartAt I x ⁻¹' ball (extChartAt I x x) c.r

/-- A controlled model set is open. -/
theorem isOpen_controlledInteriorChartSet
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) :
    IsOpen (controlledInteriorChartSet I c) :=
  isOpen_ball.inter isOpen_interior

/-- A controlled model set is convex. -/
theorem convex_controlledInteriorChartSet
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) :
    Convex ℝ (controlledInteriorChartSet I c) :=
  (convex_ball _ _).inter I.convex_range.interior

/-- A controlled model set lies in the inverse extended chart target. -/
theorem controlledInteriorChartSet_subset_target
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) :
    controlledInteriorChartSet I c ⊆ (extChartAt I x).target := by
  intro y hy
  exact (c.controlled ⟨hy.1, interior_subset hy.2⟩).1

/-- A controlled complex chart domain lies in the full interior inverse-chart
domain at the same center. -/
theorem controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) {x : M} (c : InteriorChartControl I x) :
    controlledInteriorComplexChartDomain I e c ⊆
      interiorComplexExtChartDomain I e x := by
  intro z hz
  change e z ∈ interior (extChartAt I x).target
  exact interior_maximal
    (controlledInteriorChartSet_subset_target I c)
    (isOpen_controlledInteriorChartSet I c) hz

/-- The controlled complex coordinate domain is open. -/
theorem isOpen_controlledInteriorComplexChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) {x : M} (c : InteriorChartControl I x) :
    IsOpen (controlledInteriorComplexChartDomain I e c) :=
  (isOpen_controlledInteriorChartSet I c).preimage e.continuous

/-- The ambient controlled chart neighborhood is open. -/
theorem isOpen_controlledInteriorChartNeighborhood
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) :
    IsOpen (controlledInteriorChartNeighborhood I c) := by
  exact isOpen_extChartAt_preimage' x isOpen_ball

/-- The center belongs to its ambient controlled chart neighborhood. -/
theorem mem_controlledInteriorChartNeighborhood
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {x : M} (c : InteriorChartControl I x) :
    x ∈ controlledInteriorChartNeighborhood I c :=
  ⟨mem_extChartAt_source x, mem_ball_self c.r_pos⟩

/-- A controlled inverse chart is Lipschitz on its complex coordinate
domain, with the derivative-bound constant stored in the control data. -/
theorem lipschitzOnWith_controlledInteriorComplexChart
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (e : ℂ ≃ₗᵢ[ℝ] E) {x : M} (c : InteriorChartControl I x) :
    LipschitzOnWith c.C (interiorComplexExtChart I e x)
      (controlledInteriorComplexChartDomain I e c) := by
  apply lipschitzOnWith_interiorComplexExtChart_of_convex I e x
    (controlledInteriorChartSet I c)
    (convex_controlledInteriorChartSet I c)
    (controlledInteriorChartSet_subset_target I c)
  intro y hy
  exact (c.controlled ⟨hy.1, interior_subset hy.2⟩).2.le

/-- The controlled complex chart image is exactly the interior part of its
ambient controlled neighborhood. -/
theorem image_controlledInteriorComplexChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) {x : M} (c : InteriorChartControl I x) :
    interiorComplexExtChart I e x ''
        controlledInteriorComplexChartDomain I e c =
      controlledInteriorChartNeighborhood I c ∩ I.interior M := by
  rw [interiorComplexExtChart, controlledInteriorComplexChartDomain,
    Set.image_comp, Set.image_preimage_eq _ e.surjective]
  rw [(extChartAt I x).symm_image_eq_source_inter_preimage
    (controlledInteriorChartSet_subset_target I c)]
  ext y
  simp only [controlledInteriorChartSet,
    controlledInteriorChartNeighborhood, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hsource, hball, hrange⟩
    have hchartSource : y ∈ (chartAt H x).source := by
      simpa only [extChartAt_source] using hsource
    refine ⟨⟨hsource, hball⟩, ?_⟩
    change I.IsInteriorPoint y
    apply (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
      (chart_mem_atlas H x) hchartSource).mpr
    exact interior_maximal (controlledInteriorChartSet_subset_target I c)
      (isOpen_controlledInteriorChartSet I c) ⟨hball, hrange⟩
  · rintro ⟨⟨hsource, hball⟩, hinterior⟩
    have hchartSource : y ∈ (chartAt H x).source := by
      simpa only [extChartAt_source] using hsource
    refine ⟨hsource, hball, ?_⟩
    change I.IsInteriorPoint y at hinterior
    exact interior_mono (extChartAt_target_subset_range x)
      ((I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
        (chart_mem_atlas H x) hchartSource).mp hinterior)

/-- A canonical local choice of controlled inverse-chart data at each
manifold point. -/
def chosenInteriorChartControl
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (x : M) : InteriorChartControl I x :=
  Classical.choice (nonempty_interiorChartControl I x)

/-- The chosen controlled complex coordinate domain at a point. -/
def chosenControlledInteriorComplexChartDomain
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (x : M) : Set ℂ :=
  controlledInteriorComplexChartDomain I e (chosenInteriorChartControl I x)

/-- The chosen ambient controlled chart neighborhood at a point. -/
def chosenControlledInteriorChartNeighborhood
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (x : M) : Set M :=
  controlledInteriorChartNeighborhood I (chosenInteriorChartControl I x)

/-- Compactness selects finitely many controlled inverse charts whose
images cover the manifold interior. -/
theorem exists_fin_controlledInteriorComplexExtChart_cover
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [CompactSpace M] (e : ℂ ≃ₗᵢ[ℝ] E) :
    ∃ n : ℕ, ∃ centers : Fin n → M,
      I.interior M ⊆ ⋃ i, interiorComplexExtChart I e (centers i) ''
        chosenControlledInteriorComplexChartDomain I e (centers i) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset M,
      (Set.univ : Set M) ⊆
        ⋃ x ∈ t, chosenControlledInteriorChartNeighborhood I x := by
    refine isCompact_univ.elim_finite_subcover
      (chosenControlledInteriorChartNeighborhood I)
      (fun x ↦ isOpen_controlledInteriorChartNeighborhood I
        (chosenInteriorChartControl I x)) ?_
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x,
      mem_controlledInteriorChartNeighborhood I
        (chosenInteriorChartControl I x)⟩
  refine ⟨t.card, fun j ↦ t.equivFin.symm j, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  rw [chosenControlledInteriorComplexChartDomain,
    image_controlledInteriorComplexChartDomain I e]
  have hcenter :
      ((t.equivFin.symm (t.equivFin ⟨x, hxt⟩) : t) : M) = x :=
    congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨x, hxt⟩)
  change y ∈ controlledInteriorChartNeighborhood I
      (chosenInteriorChartControl I
        ((t.equivFin.symm (t.equivFin ⟨x, hxt⟩) : t) : M)) ∩
        I.interior M
  rw [hcenter]
  exact ⟨hyx, hy⟩

end

end GromovFilling
