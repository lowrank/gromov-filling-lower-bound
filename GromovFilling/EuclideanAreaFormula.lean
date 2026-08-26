import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# The Lipschitz planar area inequality

This file derives the image-measure inequality used in Lemma 5.4 from
Rademacher's theorem and mathlib's differentiable Jacobian image bound.
-/

open Filter MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace GromovFilling

noncomputable section

/-- The Euclidean plane in the coordinate model used by mathlib's
finite-dimensional Jacobian theorem. -/
abbrev EuclideanPlane := Fin 2 → ℝ

/-- A globally Lipschitz planar map sends every measurable set to an image
whose Lebesgue measure is at most the integral of the absolute determinant
of its derivative.  At the null nondifferentiability set the derivative is
irrelevant and contributes nothing to the set integral. -/
theorem volume_image_le_lintegral_abs_det_fderiv
    (f : EuclideanPlane → EuclideanPlane) (s : Set EuclideanPlane)
    (hs : MeasurableSet s) {K : ℝ≥0} (hf : LipschitzWith K f) :
    volume (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := by
  let differentiabilitySet : Set EuclideanPlane :=
    {x | DifferentiableAt ℝ f x}
  have hdiffMeasurable : MeasurableSet differentiabilitySet := by
    exact measurableSet_of_differentiableAt ℝ f
  have hdiffAE : ∀ᵐ x ∂volume, x ∈ differentiabilitySet := by
    simpa only [differentiabilitySet, Set.mem_setOf_eq] using
      (hf.ae_differentiableAt (μ := volume))
  have hdiffComplZero : volume differentiabilitySetᶜ = 0 := by
    apply compl_mem_ae_iff.mp
    simpa only [compl_compl] using hdiffAE
  have himageDiffComplZero : volume (f '' differentiabilitySetᶜ) = 0 := by
    have hhausdorff := hf.hausdorffMeasure_image_le
      (d := (2 : ℝ)) (by norm_num) differentiabilitySetᶜ
    have hmeasureEq :
        (μH[(2 : ℝ)] : Measure EuclideanPlane) = volume := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        (hausdorffMeasure_pi_real (ι := Fin 2))
    rw [hmeasureEq] at hhausdorff
    exact le_antisymm
      (hhausdorff.trans_eq (by rw [hdiffComplZero, mul_zero]))
      (zero_le _)
  let good : Set EuclideanPlane := s ∩ differentiabilitySet
  have hgoodMeasurable : MeasurableSet good :=
    hs.inter hdiffMeasurable
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
      exact lintegral_mono_set (inter_subset_left)

/-- Local form for a map which is only Lipschitz on an open planar set.
The coordinatewise McShane extension gives a global Lipschitz map agreeing
on the open set; openness makes their Fréchet derivatives agree there. -/
theorem volume_image_le_lintegral_abs_det_fderiv_of_isOpen
    (f : EuclideanPlane → EuclideanPlane) (s : Set EuclideanPlane)
    (hs : IsOpen s) {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_pi
  have himage : f '' s = g '' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hfg hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hfg hx⟩
  have hderiv (x : EuclideanPlane) (hx : x ∈ s) :
      fderiv ℝ f x = fderiv ℝ g x := by
    have heq : f =ᶠ[𝓝 x] g := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact hfg hy
    exact heq.fderiv_eq
  rw [himage]
  refine (volume_image_le_lintegral_abs_det_fderiv
    g s hs.measurableSet hg).trans_eq ?_
  apply lintegral_congr_ae
  rw [Filter.EventuallyEq,
    ae_restrict_iff' (μ := volume) hs.measurableSet]
  filter_upwards with x hx
  rw [hderiv x hx]

/-- Coverage version of the local open-set area inequality. -/
theorem volume_le_lintegral_abs_det_fderiv_of_isOpen_of_subset_range
    (f : EuclideanPlane → EuclideanPlane)
    (s omega : Set EuclideanPlane) (hs : IsOpen s)
    {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hcoverage : omega ⊆ f '' s) :
    volume omega ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume :=
  (measure_mono hcoverage).trans
    (volume_image_le_lintegral_abs_det_fderiv_of_isOpen f s hs hf)

/-- Coverage of a measurable planar region, together with the Lipschitz
area formula, bounds its measure by the Jacobian integral. -/
theorem volume_le_lintegral_abs_det_fderiv_of_subset_range
    (f : EuclideanPlane → EuclideanPlane) (s omega : Set EuclideanPlane)
    (hs : MeasurableSet s) {K : ℝ≥0} (hf : LipschitzWith K f)
    (hcoverage : omega ⊆ f '' s) :
    volume omega ≤
      ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂volume :=
  (measure_mono hcoverage).trans
    (volume_image_le_lintegral_abs_det_fderiv f s hs hf)

end

end GromovFilling
