import GromovFilling.JacobianBudget
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex-coordinate form of the Jacobian budget

This module identifies the determinant density used by the complex-plane
area formula with the elementary two-row Jacobian from `JacobianBudget`.
It then packages the exact pointwise-to-integrated implication needed for
the genuine metric Fourier maps.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace GromovFilling

noncomputable section

/-- The Hilbert--Schmidt square of a real-linear endomorphism of `ℂ`,
computed on the oriented orthonormal basis `(1, I)`. -/
def complexDerivativeEnergy (L : ℂ →L[ℝ] ℂ) : ℝ :=
  Complex.normSq (L 1) + Complex.normSq (L Complex.I)

@[simp] theorem complexDerivativeEnergy_neg (L : ℂ →L[ℝ] ℂ) :
    complexDerivativeEnergy (-L) = complexDerivativeEnergy L := by
  simp [complexDerivativeEnergy]

/-- Orthogonal row mixing of a finite family of real-linear complex maps. -/
def complexLinearMapMix {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (L : ι → ℂ →L[ℝ] ℂ) (j : ι) : ℂ →L[ℝ] ℂ :=
  ∑ k, U j k • L k

private lemma complexLinearMapMix_apply_re
    {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (L : ι → ℂ →L[ℝ] ℂ) (j : ι) (z : ℂ) :
    (complexLinearMapMix U L j z).re =
      U.mulVec (fun k ↦ (L k z).re) j := by
  simp [complexLinearMapMix, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [smul_eq_mul] using Complex.smul_re (U j i) (L i z)

private lemma complexLinearMapMix_apply_im
    {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (L : ι → ℂ →L[ℝ] ℂ) (j : ι) (z : ℂ) :
    (complexLinearMapMix U L j z).im =
      U.mulVec (fun k ↦ (L k z).im) j := by
  simp [complexLinearMapMix, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [smul_eq_mul] using Complex.smul_im (U j i) (L i z)

/-- Orthogonal mixing preserves the total Hilbert--Schmidt derivative
energy, in exactly the form needed before applying the determinant bound. -/
theorem sum_complexDerivativeEnergy_complexLinearMapMix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1)
    (L : ι → ℂ →L[ℝ] ℂ) :
    (∑ j, complexDerivativeEnergy (complexLinearMapMix U L j)) =
      ∑ k, complexDerivativeEnergy (L k) := by
  simp_rw [complexDerivativeEnergy, Complex.normSq_apply,
    complexLinearMapMix_apply_re, complexLinearMapMix_apply_im]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← pow_two]
  rw [orthogonal_mulVec_energy U horth (fun k ↦ (L k 1).re),
    orthogonal_mulVec_energy U horth (fun k ↦ (L k 1).im),
    orthogonal_mulVec_energy U horth (fun k ↦ (L k Complex.I).re),
    orthogonal_mulVec_energy U horth (fun k ↦ (L k Complex.I).im)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Pointwise orthogonal mixing of complex-valued functions. -/
def complexFunctionMix {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (F : ι → ℂ → ℂ) (j : ι) (x : ℂ) : ℂ :=
  ∑ k, U j k • F k x

theorem hasFDerivAt_complexFunctionMix
    {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (F : ι → ℂ → ℂ)
    (L : ι → ℂ →L[ℝ] ℂ) (j : ι) (x : ℂ)
    (hF : ∀ k, HasFDerivAt (F k) (L k) x) :
    HasFDerivAt (complexFunctionMix U F j)
      (complexLinearMapMix U L j) x := by
  unfold complexFunctionMix complexLinearMapMix
  apply HasFDerivAt.fun_sum
  intro k _
  exact (hF k).const_smul (U j k)

theorem fderiv_complexFunctionMix
    {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℝ) (F : ι → ℂ → ℂ)
    (j : ι) (x : ℂ)
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) :
    fderiv ℝ (complexFunctionMix U F j) x =
      complexLinearMapMix U (fun k ↦ fderiv ℝ (F k) x) j := by
  exact (hasFDerivAt_complexFunctionMix U F
    (fun k ↦ fderiv ℝ (F k) x) j x
    (fun k ↦ (hF k).hasFDerivAt)).fderiv

/-- At a common differentiability point, orthogonal function mixing
preserves the total derivative energy. -/
theorem sum_complexDerivativeEnergy_fderiv_complexFunctionMix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1)
    (F : ι → ℂ → ℂ) (x : ℂ)
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) :
    (∑ j, complexDerivativeEnergy
      (fderiv ℝ (complexFunctionMix U F j) x)) =
      ∑ k, complexDerivativeEnergy (fderiv ℝ (F k) x) := by
  simp_rw [fderiv_complexFunctionMix U F _ x hF]
  exact sum_complexDerivativeEnergy_complexLinearMapMix U horth
    (fun k ↦ fderiv ℝ (F k) x)

/-- The absolute real determinant is the elementary planar Jacobian of the
two images of the standard oriented basis. -/
theorem abs_det_eq_planarJacobian (L : ℂ →L[ℝ] ℂ) :
    |L.det| = planarJacobian
      ((L 1).re, (L 1).im) ((L Complex.I).re, (L Complex.I).im) := by
  change |LinearMap.det L.toLinearMap| = _
  rw [show LinearMap.det L.toLinearMap =
      (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        L.toLinearMap).det from
    (LinearMap.det_toMatrix Complex.basisOneI L.toLinearMap).symm]
  unfold planarJacobian
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr]
  congr 1
  change (L 1).re * (L Complex.I).im -
      (L Complex.I).re * (L 1).im =
    (L 1).re * (L Complex.I).im -
      (L 1).im * (L Complex.I).re
  rw [mul_comm (L Complex.I).re (L 1).im]

/-- The sum of absolute complex determinants is at most half the total
Hilbert--Schmidt energy. -/
theorem sum_abs_det_le_half_complexDerivativeEnergy
    {ι : Type*} [Fintype ι] (L : ι → ℂ →L[ℝ] ℂ) :
    (∑ j, |(L j).det|) ≤
      (∑ j, complexDerivativeEnergy (L j)) / 2 := by
  rw [show (∑ j, |(L j).det|) =
      ∑ j, planarJacobian
        (((L j) 1).re, ((L j) 1).im)
        (((L j) Complex.I).re, ((L j) Complex.I).im) by
    apply Finset.sum_congr rfl
    intro j _
    exact abs_det_eq_planarJacobian (L j)]
  refine (sum_planarJacobian_le_half_energy
    (fun j ↦ (((L j) 1).re, ((L j) 1).im))
    (fun j ↦ (((L j) Complex.I).re, ((L j) Complex.I).im))).trans_eq ?_
  unfold planarNormSq complexDerivativeEnergy
  simp only [Complex.normSq_apply, Finset.sum_add_distrib]
  ring

/-- A total derivative energy bound of `2` gives the unit pointwise
Jacobian budget in complex coordinates. -/
theorem sum_abs_det_le_one_of_complexDerivativeEnergy
    {ι : Type*} [Fintype ι] (L : ι → ℂ →L[ℝ] ℂ)
    (henergy : (∑ j, complexDerivativeEnergy (L j)) ≤ 2) :
    (∑ j, |(L j).det|) ≤ 1 := by
  have hdet := sum_abs_det_le_half_complexDerivativeEnergy L
  linarith

/-- Keeping an explicit nonnegative defect in the Hilbert--Schmidt energy
budget yields the sharp pointwise determinant defect inequality. -/
theorem sum_abs_det_add_le_one_of_complexDerivativeEnergy_defect
    {ι : Type*} [Fintype ι] (L : ι → ℂ →L[ℝ] ℂ) (defect : ℝ)
    (henergy : (∑ j, complexDerivativeEnergy (L j)) + 2 * defect ≤ 2) :
    (∑ j, |(L j).det|) + defect ≤ 1 := by
  have hdet := sum_abs_det_le_half_complexDerivativeEnergy L
  linarith

/-- The integrated complex Jacobian budget follows from the pointwise
Hilbert--Schmidt energy bound, for any measure on the domain. -/
theorem sum_lintegral_abs_det_fderiv_le_measure
    {ι : Type*} [Fintype ι] (μ : Measure ℂ) (G : ι → ℂ → ℂ)
    (henergy : ∀ᵐ x ∂μ,
      (∑ j, complexDerivativeEnergy (fderiv ℝ (G j) x)) ≤ 2) :
    (∑ j, ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂μ) ≤
      μ Set.univ := by
  let p : ι → ℂ → ℝ × ℝ := fun j x ↦
    (((fderiv ℝ (G j) x) 1).re, ((fderiv ℝ (G j) x) 1).im)
  let q : ι → ℂ → ℝ × ℝ := fun j x ↦
    (((fderiv ℝ (G j) x) Complex.I).re,
      ((fderiv ℝ (G j) x) Complex.I).im)
  have hmeasurable : ∀ j,
      Measurable (fun x ↦
        ENNReal.ofReal (planarJacobian (p j x) (q j x))) := by
    intro j
    unfold p q planarJacobian
    fun_prop
  have hpointwise : ∀ᵐ x ∂μ,
      (∑ j, planarJacobian (p j x) (q j x)) ≤ 1 := by
    filter_upwards [henergy] with x hx
    rw [show (∑ j, planarJacobian (p j x) (q j x)) =
          ∑ j, |(fderiv ℝ (G j) x).det| by
        apply Finset.sum_congr rfl
        intro j _
        exact (abs_det_eq_planarJacobian (fderiv ℝ (G j) x)).symm]
    exact sum_abs_det_le_one_of_complexDerivativeEnergy
      (fun j ↦ fderiv ℝ (G j) x) hx
  simpa only [p, q, ← abs_det_eq_planarJacobian] using
    (sum_lintegral_planarJacobian_le_measure_univ_ae
      μ p q hmeasurable hpointwise)

/-- Restricting the preceding budget to a measurable planar domain gives
the domain's ordinary Euclidean area on the right. -/
theorem sum_lintegral_abs_det_fderiv_restrict_le_volume
    {ι : Type*} [Fintype ι] (G : ι → ℂ → ℂ)
    (s : Set ℂ) (_hs : MeasurableSet s)
    (henergy : ∀ᵐ x ∂volume.restrict s,
      (∑ j, complexDerivativeEnergy (fderiv ℝ (G j) x)) ≤ 2) :
    (∑ j, ∫⁻ x in s,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ volume s := by
  simpa only [Measure.restrict_apply_univ] using
    (sum_lintegral_abs_det_fderiv_le_measure
      (volume.restrict s) G henergy)

/-- Integrated additive complex Jacobian budget with an explicit real-valued defect. -/
theorem sum_lintegral_abs_det_fderiv_add_lintegral_ofReal_defect_le_measure
    {ι : Type*} [Fintype ι] (μ : Measure ℂ) (G : ι → ℂ → ℂ)
    (defect : ℂ → ℝ)
    (hdefect : Measurable (fun x ↦ ENNReal.ofReal (defect x)))
    (hdefect_nonneg : ∀ x, 0 ≤ defect x)
    (hbudget : ∀ᵐ x ∂μ,
      (∑ j, |(fderiv ℝ (G j) x).det|) + defect x ≤ 1) :
    (∑ j, ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂μ) +
        ∫⁻ x, ENNReal.ofReal (defect x) ∂μ ≤ μ Set.univ := by
  let p : ι → ℂ → ℝ × ℝ := fun j x ↦
    (((fderiv ℝ (G j) x) 1).re, ((fderiv ℝ (G j) x) 1).im)
  let q : ι → ℂ → ℝ × ℝ := fun j x ↦
    (((fderiv ℝ (G j) x) Complex.I).re,
      ((fderiv ℝ (G j) x) Complex.I).im)
  have hmeasurable : ∀ j,
      Measurable (fun x ↦
        ENNReal.ofReal (planarJacobian (p j x) (q j x))) := by
    intro j
    unfold p q planarJacobian
    fun_prop
  have hpointwise : ∀ᵐ x ∂μ,
      (∑ j, ENNReal.ofReal (planarJacobian (p j x) (q j x))) +
        ENNReal.ofReal (defect x) ≤ 1 := by
    filter_upwards [hbudget] with x hx
    have hsum_nonneg : 0 ≤ ∑ j, planarJacobian (p j x) (q j x) :=
      Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    have hsum : (∑ j, ENNReal.ofReal (planarJacobian (p j x) (q j x))) =
        ENNReal.ofReal (∑ j, planarJacobian (p j x) (q j x)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact abs_nonneg _
    have hsumabs_eq : (∑ j, |(fderiv ℝ (G j) x).det|) =
        ∑ j, planarJacobian (p j x) (q j x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [p, q, abs_det_eq_planarJacobian]
    have hx' : ENNReal.ofReal ((∑ j, |(fderiv ℝ (G j) x).det|) + defect x) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal hx
    rw [hsumabs_eq, ENNReal.ofReal_add hsum_nonneg (hdefect_nonneg x)] at hx'
    simpa [hsum] using hx'
  simpa only [p, q, ← abs_det_eq_planarJacobian] using
    (sum_lintegral_planarJacobian_add_lintegral_defect_le_measure_univ_ae
      μ p q (fun x ↦ ENNReal.ofReal (defect x)) hmeasurable hdefect hpointwise)

/-- Restricting the additive complex Jacobian budget to a measurable planar domain. -/
theorem sum_lintegral_abs_det_fderiv_add_lintegral_ofReal_defect_restrict_le_volume
    {ι : Type*} [Fintype ι] (G : ι → ℂ → ℂ)
    (s : Set ℂ) (_hs : MeasurableSet s)
    (defect : ℂ → ℝ)
    (hdefect : Measurable (fun x ↦ ENNReal.ofReal (defect x)))
    (hdefect_nonneg : ∀ x, 0 ≤ defect x)
    (hbudget : ∀ᵐ x ∂volume.restrict s,
      (∑ j, |(fderiv ℝ (G j) x).det|) + defect x ≤ 1) :
    (∑ j, ∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) +
        ∫⁻ x in s, ENNReal.ofReal (defect x) ∂volume ≤ volume s := by
  simpa only [Measure.restrict_apply_univ] using
    (sum_lintegral_abs_det_fderiv_add_lintegral_ofReal_defect_le_measure
      (volume.restrict s) G defect hdefect hdefect_nonneg hbudget)

end

end GromovFilling
