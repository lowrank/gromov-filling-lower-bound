import GromovFilling.EuclideanAreaFormula
import GromovFilling.SurfaceCoverage
import GromovFilling.GivensDiskArea
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Lipschitz area inequality for complex-valued planar maps

The degree and coverage arguments in this project use `ℂ` as their planar
target.  This file supplies the corresponding analytic image-area inequality
directly on `ℂ`, regarded as a two-dimensional real normed space.
-/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped NNReal ENNReal Topology

namespace GromovFilling

noncomputable section

/-- On the complex plane, two-dimensional Hausdorff measure and Lebesgue
measure have the same null sets. -/
theorem complex_hausdorffMeasure_two_eq_zero_iff (s : Set ℂ) :
    μH[(2 : ℝ)] s = 0 ↔ volume s = 0 := by
  have hhausdorffHaar :
      IsAddHaarMeasure (μH[(2 : ℝ)] : Measure ℂ) := by
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using
      (inferInstance :
        IsAddHaarMeasure
          (μH[(Module.finrank ℝ ℂ : ℝ)] : Measure ℂ))
  letI := hhausdorffHaar
  constructor
  · intro hs
    exact (absolutelyContinuous_isAddHaarMeasure
      (volume : Measure ℂ) (μH[(2 : ℝ)] : Measure ℂ)) hs
  · intro hs
    exact (absolutelyContinuous_isAddHaarMeasure
      (μH[(2 : ℝ)] : Measure ℂ) (volume : Measure ℂ)) hs

/-- A globally Lipschitz complex-plane map preserves Lebesgue-null sets. -/
theorem complex_volume_image_eq_zero_of_lipschitzWith
    (f : ℂ → ℂ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {s : Set ℂ} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  rw [← complex_hausdorffMeasure_two_eq_zero_iff] at hs ⊢
  apply le_antisymm
  · exact (hf.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num) s).trans_eq
      (by rw [hs, mul_zero])
  · exact zero_le _

/-- A globally Lipschitz map of the complex plane sends every measurable set
to an image whose Lebesgue measure is bounded by the integral of the absolute
real determinant of its Fréchet derivative. -/
theorem complex_volume_image_le_lintegral_abs_det_fderiv
    (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    volume (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := by
  let differentiabilitySet : Set ℂ := {x | DifferentiableAt ℝ f x}
  have hdiffMeasurable : MeasurableSet differentiabilitySet := by
    exact measurableSet_of_differentiableAt ℝ f
  have hdiffAE : ∀ᵐ x ∂volume, x ∈ differentiabilitySet := by
    simpa only [differentiabilitySet, Set.mem_setOf_eq] using
      (hf.ae_differentiableAt (μ := volume))
  have hdiffComplZero : volume differentiabilitySetᶜ = 0 := by
    apply compl_mem_ae_iff.mp
    simpa only [compl_compl] using hdiffAE
  have himageDiffComplZero : volume (f '' differentiabilitySetᶜ) = 0 :=
    complex_volume_image_eq_zero_of_lipschitzWith f hf hdiffComplZero
  let good : Set ℂ := s ∩ differentiabilitySet
  have hgoodMeasurable : MeasurableSet good := hs.inter hdiffMeasurable
  have hgoodDerivative : ∀ x ∈ good,
      HasFDerivWithinAt f (fderiv ℝ f x) good x := by
    intro x hx
    exact (hx.2.hasFDerivAt).hasFDerivWithinAt
  have himageGood : volume (f '' good) ≤
      ∫⁻ x in good, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume :=
    addHaar_image_le_lintegral_abs_det_fderiv
      volume hgoodMeasurable hgoodDerivative
  calc
    volume (f '' s) ≤
        volume (f '' good ∪ f '' differentiabilitySetᶜ) := by
      apply measure_mono
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxdiff : x ∈ differentiabilitySet
      · exact Set.mem_union_left _ ⟨x, ⟨hx, hxdiff⟩, rfl⟩
      · exact Set.mem_union_right _ ⟨x, hxdiff, rfl⟩
    _ ≤ volume (f '' good) + volume (f '' differentiabilitySetᶜ) :=
      measure_union_le _ _
    _ = volume (f '' good) := by rw [himageDiffComplZero, add_zero]
    _ ≤ ∫⁻ x in good,
        ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := himageGood
    _ ≤ ∫⁻ x in s,
        ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := by
      exact lintegral_mono_set inter_subset_left

/-- Local form for a map which is only Lipschitz on an open subset of the
complex plane. -/
theorem complex_volume_image_le_lintegral_abs_det_fderiv_of_isOpen
    (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_finite_dimension
  have himage : f '' s = g '' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hfg hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hfg hx⟩
  have hderiv (x : ℂ) (hx : x ∈ s) :
      fderiv ℝ f x = fderiv ℝ g x := by
    have heq : f =ᶠ[𝓝 x] g := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hfg hy
    exact heq.fderiv_eq
  rw [himage]
  refine (complex_volume_image_le_lintegral_abs_det_fderiv
    g s hs.measurableSet hg).trans_eq ?_
  apply lintegral_congr_ae
  rw [Filter.EventuallyEq,
    ae_restrict_iff' (μ := volume) hs.measurableSet]
  filter_upwards with x hx
  rw [hderiv x hx]

/-- Coverage version of the local complex-plane area inequality. -/
theorem complex_volume_le_lintegral_abs_det_fderiv_of_isOpen_of_subset_range
    (f : ℂ → ℂ) (s omega : Set ℂ) (hs : IsOpen s)
    {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hcoverage : omega ⊆ f '' s) :
    volume omega ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume :=
  (measure_mono hcoverage).trans
    (complex_volume_image_le_lintegral_abs_det_fderiv_of_isOpen f s hs hf)

/-- Coverage version of the global complex-plane area inequality. -/
theorem complex_volume_le_lintegral_abs_det_fderiv_of_subset_range
    (f : ℂ → ℂ) (s omega : Set ℂ) (hs : MeasurableSet s)
    {K : ℝ≥0} (hf : LipschitzWith K f)
    (hcoverage : omega ⊆ f '' s) :
    volume omega ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume :=
  (measure_mono hcoverage).trans
    (complex_volume_image_le_lintegral_abs_det_fderiv f s hs hf)

/-- For a complex-plane domain, the topological coverage half and the
analytic area half of Lemma 5.4 compose directly: the Jordan region forced
into the image is bounded by the global Jacobian integral.  The general
surface theorem still requires the corresponding chart-globalization
statement. -/
theorem givens_jordan_region_volume_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    volume region₁ ≤
      ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  have hcoverage : region₁ ⊆ Set.range G :=
    givensBoundaryCurve_jordan_region_subset_range_of_fine_models
      j boundary hfine G hG hboundary hpartition hzero
  have hcoverage' : region₁ ⊆ G '' (Set.univ : Set ℂ) := by
    simpa only [Set.image_univ] using hcoverage
  simpa only [Measure.restrict_univ] using
    (complex_volume_le_lintegral_abs_det_fderiv_of_subset_range
      G Set.univ region₁ MeasurableSet.univ hGLipschitz hcoverage')

/-- If the boundary extends continuously across the standard closed disk, the
Jordan region forced by Lemma 5.4 is covered directly from that extension, so
the global complex Jacobian bound applies without a polygonal-model
hypothesis. -/
theorem givens_jordan_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    volume region₁ ≤
      ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  have hcoverage : region₁ ⊆ Set.range G :=
    givensBoundaryCurve_jordan_region_subset_range_of_closedUnitDisk_extension
      j F hF hboundaryExtension G hG hboundary hpartition hzero
  have hcoverage' : region₁ ⊆ G '' (Set.univ : Set ℂ) := by
    simpa only [Set.image_univ] using hcoverage
  simpa only [Measure.restrict_univ] using
    (complex_volume_le_lintegral_abs_det_fderiv_of_subset_range
      G Set.univ region₁ MeasurableSet.univ hGLipschitz hcoverage')

/-- Planar, end-to-end form of the quantitative conclusion in Lemma 5.4:
the explicit Fourier coefficient area is the actual Jordan-region volume,
that region is forced into the extension image by the mod-two obstruction,
and the area formula bounds it by the Jacobian integral. -/
theorem givens_mixedBoundaryArea_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  rw [← volume_givensBoundaryCurve_jordan_region
    j hpartition hzero]
  exact givens_jordan_region_volume_le_complex_jacobian
    j boundary hfine G hG hboundary hpartition hzero hGLipschitz

/-- If the boundary extends continuously across the standard closed disk,
Jordan separation and coverage can be discharged internally with no
polygonal-model hypothesis. -/
theorem givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  rw [← volume_givensBoundaryCurve_jordan_region j hpartition hzero]
  exact givens_jordan_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension G hG hboundary hpartition hzero hGLipschitz

/-- Jordan separation and coverage can be discharged internally: there is
a bounded open connected region containing the origin whose volume is
controlled by the Jacobian integral of the extension. -/
theorem exists_givens_bounded_region_volume_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  exact ⟨region₁, hpartition.region₁_open,
    hpartition.region₁_connected,
    givensBoundaryCurve_jordan_region_at_origin_bounded
      j hpartition hzero,
    hzero,
    givens_jordan_region_volume_le_complex_jacobian
      j boundary hfine G hG hboundary hpartition hzero hGLipschitz⟩

/-- If the boundary extends continuously across the standard closed disk,
there is a bounded open connected region containing the origin whose volume
is controlled by the Jacobian integral of the extension, with no
polygonal-model hypothesis. -/
theorem exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ G x).det| ∂volume := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  exact ⟨region₁, hpartition.region₁_open,
    hpartition.region₁_connected,
    givensBoundaryCurve_jordan_region_at_origin_bounded
      j hpartition hzero,
    hzero,
    givens_jordan_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
      j boundary F hF hboundaryExtension G hG hboundary hpartition hzero hGLipschitz⟩

end

end GromovFilling
