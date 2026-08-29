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
open scoped Bundle ENNReal Manifold NNReal

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
  rw [IsRiemannianManifold.out]
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

end

end GromovFilling
