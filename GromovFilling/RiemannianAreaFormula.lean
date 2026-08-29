import GromovFilling.ComplexAreaFormula
import GromovFilling.RiemannianTwoJacobian

/-!
# The planar area formula in intrinsic `J₂` notation

This file connects the coordinate-free metric Jacobian to the planar area
formula already used in Lemma 5.4.  It is deliberately a bridge module: the
general Riemannian-surface change-of-variables theorem remains separate.
-/

open MeasureTheory Set
open scoped ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactArea :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The global complex-plane image inequality, expressed with the intrinsic
Riemannian two-Jacobian. -/
theorem complex_volume_image_le_lintegral_riemannianTwoJacobian
    (f : ℂ → ℂ) (s : Set ℂ) (hs : MeasurableSet s)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    volume (f '' s) ≤
      ∫⁻ x in s,
        ENNReal.ofReal (riemannianTwoJacobian 𝓘(ℝ, ℂ) f x) ∂volume := by
  simpa only [riemannianTwoJacobian_complex_eq_abs_det_fderiv] using
    complex_volume_image_le_lintegral_abs_det_fderiv f s hs hf

/-- Coverage form of the local planar area inequality in intrinsic
Riemannian two-Jacobian notation. -/
theorem complex_volume_le_lintegral_riemannianTwoJacobian_of_isOpen_of_subset_range
    (f : ℂ → ℂ) (s omega : Set ℂ) (hs : IsOpen s)
    {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hcoverage : omega ⊆ f '' s) :
    volume omega ≤
      ∫⁻ x in s,
        ENNReal.ofReal (riemannianTwoJacobian 𝓘(ℝ, ℂ) f x) ∂volume := by
  simpa only [riemannianTwoJacobian_complex_eq_abs_det_fderiv] using
    complex_volume_le_lintegral_abs_det_fderiv_of_isOpen_of_subset_range
      f s omega hs hf hcoverage

/-- The obstruction-level planar interface of Lemma 5.4, now stated with
the same intrinsic `J₂` that will occur in the general Riemannian-surface
area formula. -/
theorem givens_jordan_region_volume_le_riemannianTwoJacobian_of_odd_boundary_degree_obstruction
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : ℂ → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁)
    {K : ℝ≥0} (hGLipschitz : LipschitzWith K G) :
    volume region₁ ≤
      ∫⁻ x,
        ENNReal.ofReal (riemannianTwoJacobian 𝓘(ℝ, ℂ) G x) ∂volume := by
  simpa only [riemannianTwoJacobian_complex_eq_abs_det_fderiv] using
    givens_jordan_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
      j boundary hobstruction G hG hboundary hpartition hzero hGLipschitz

end

end GromovFilling
