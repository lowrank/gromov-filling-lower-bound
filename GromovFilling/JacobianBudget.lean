import GromovFilling.Universal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# The pointwise orthogonal Jacobian budget

This file contains the finite-dimensional inequality at the heart of
Proposition 3.2.  Analytic Bessel estimates supply bounds for the two square
energies; the result below converts those bounds into a sum of absolute
two-dimensional Jacobians.
-/

open scoped BigOperators ENNReal InnerProductSpace
open MeasureTheory

namespace GromovFilling

noncomputable section

/-- The absolute determinant of the two row vectors of a planar
differential. -/
def planarJacobian (p q : ℝ × ℝ) : ℝ :=
  |p.1 * q.2 - p.2 * q.1|

/-- Squared Euclidean norm on a pair of real coordinates. -/
def planarNormSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- `|det(p,q)|` is bounded by half the sum of the squared row norms. -/
lemma planarJacobian_le_half_energy (p q : ℝ × ℝ) :
    planarJacobian p q ≤ (planarNormSq p + planarNormSq q) / 2 := by
  have hp₁ := sq_abs p.1
  have hp₂ := sq_abs p.2
  have hq₁ := sq_abs q.1
  have hq₂ := sq_abs q.2
  have h₁ : 2 * |p.1| * |q.2| ≤ p.1 ^ 2 + q.2 ^ 2 := by
    nlinarith [sq_nonneg (|p.1| - |q.2|)]
  have h₂ : 2 * |p.2| * |q.1| ≤ p.2 ^ 2 + q.1 ^ 2 := by
    nlinarith [sq_nonneg (|p.2| - |q.1|)]
  calc
    planarJacobian p q ≤ |p.1 * q.2| + |p.2 * q.1| := by
      exact abs_sub _ _
    _ = |p.1| * |q.2| + |p.2| * |q.1| := by rw [abs_mul, abs_mul]
    _ ≤ (planarNormSq p + planarNormSq q) / 2 := by
      unfold planarNormSq
      linarith

/-- Summing the elementary determinant estimate over any finite family. -/
theorem sum_planarJacobian_le_half_energy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ × ℝ) :
    (∑ j, planarJacobian (p j) (q j)) ≤
      ((∑ j, planarNormSq (p j)) + ∑ j, planarNormSq (q j)) / 2 := by
  calc
    (∑ j, planarJacobian (p j) (q j)) ≤
        ∑ j, (planarNormSq (p j) + planarNormSq (q j)) / 2 :=
      Finset.sum_le_sum fun j _ ↦ planarJacobian_le_half_energy (p j) (q j)
    _ = ((∑ j, planarNormSq (p j)) + ∑ j, planarNormSq (q j)) / 2 := by
      simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul]

/-- Bessel energy bounds imply a common Jacobian budget. -/
theorem orthogonal_jacobian_budget {ι : Type*} [Fintype ι]
    (p q : ι → ℝ × ℝ) (P Q budget : ℝ)
    (hp : (∑ j, planarNormSq (p j)) ≤ P)
    (hq : (∑ j, planarNormSq (q j)) ≤ Q)
    (hbudget : P + Q ≤ 2 * budget) :
    (∑ j, planarJacobian (p j) (q j)) ≤ budget := by
  have hdet := sum_planarJacobian_le_half_energy p q
  linarith

/-- Integrating a pointwise finite Jacobian budget commutes with the finite
sum.  This is the measure-theoretic passage used after the pointwise
orthogonal estimate in Proposition 3.2. -/
theorem sum_lintegral_planarJacobian_le_lintegral_budget
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) (p q : ι → X → ℝ × ℝ) (budget : X → ℝ)
    (hmeasurable : ∀ j,
      Measurable (fun x ↦
        ENNReal.ofReal (planarJacobian (p j x) (q j x))))
    (hbudget : ∀ x,
      (∑ j, planarJacobian (p j x) (q j x)) ≤ budget x) :
    (∑ j, ∫⁻ x, ENNReal.ofReal
      (planarJacobian (p j x) (q j x)) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (budget x) ∂μ := by
  rw [← lintegral_finset_sum Finset.univ (fun j _ ↦ hmeasurable j)]
  apply lintegral_mono
  intro x
  change (∑ j, ENNReal.ofReal
      (planarJacobian (p j x) (q j x))) ≤
    ENNReal.ofReal (budget x)
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal (hbudget x)
  · intro j _
    exact abs_nonneg _

/-- In particular, a pointwise unit budget bounds the total integrated
Jacobian by the measure of the domain. -/
theorem sum_lintegral_planarJacobian_le_measure_univ
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) (p q : ι → X → ℝ × ℝ)
    (hmeasurable : ∀ j,
      Measurable (fun x ↦
        ENNReal.ofReal (planarJacobian (p j x) (q j x))))
    (hbudget : ∀ x,
      (∑ j, planarJacobian (p j x) (q j x)) ≤ 1) :
    (∑ j, ∫⁻ x, ENNReal.ofReal
      (planarJacobian (p j x) (q j x)) ∂μ) ≤ μ Set.univ := by
  simpa using
    (sum_lintegral_planarJacobian_le_lintegral_budget
      μ p q (fun _ ↦ 1) hmeasurable hbudget)

/-- Almost-everywhere form of the unit integrated Jacobian budget.  This is
the natural interface after Rademacher differentiability. -/
theorem sum_lintegral_planarJacobian_le_measure_univ_ae
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) (p q : ι → X → ℝ × ℝ)
    (hmeasurable : ∀ j,
      Measurable (fun x ↦
        ENNReal.ofReal (planarJacobian (p j x) (q j x))))
    (hbudget : ∀ᵐ x ∂μ,
      (∑ j, planarJacobian (p j x) (q j x)) ≤ 1) :
    (∑ j, ∫⁻ x, ENNReal.ofReal
      (planarJacobian (p j x) (q j x)) ∂μ) ≤ μ Set.univ := by
  rw [← lintegral_finset_sum Finset.univ (fun j _ ↦ hmeasurable j)]
  have hpointwise : ∀ᵐ x ∂μ,
      (∑ j, ENNReal.ofReal (planarJacobian (p j x) (q j x))) ≤
        ENNReal.ofReal 1 := by
    filter_upwards [hbudget] with x hx
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · exact ENNReal.ofReal_le_ofReal hx
    · intro j _
      exact abs_nonneg _
  calc
    (∫⁻ x, ∑ j, ENNReal.ofReal
        (planarJacobian (p j x) (q j x)) ∂μ) ≤
        ∫⁻ _x, ENNReal.ofReal 1 ∂μ := lintegral_mono_ae hpointwise
    _ = μ Set.univ := by simp

/-- A matrix with `UᵀU = I` preserves the sum of coordinate squares. -/
theorem orthogonal_mulVec_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1) (x : ι → ℝ) :
    (∑ j, (U.mulVec x j) ^ 2) = ∑ k, x k ^ 2 := by
  calc
    (∑ j, (U.mulVec x j) ^ 2) =
        dotProduct (U.mulVec x) (U.mulVec x) := by
          simp [dotProduct, pow_two]
    _ = dotProduct (Matrix.vecMul (U.mulVec x) U) x :=
      Matrix.dotProduct_mulVec _ _ _
    _ = dotProduct (U.transpose.mulVec (U.mulVec x)) x := by
      rw [Matrix.mulVec_transpose]
    _ = dotProduct ((U.transpose * U).mulVec x) x := by
      rw [Matrix.mulVec_mulVec]
    _ = dotProduct x x := by rw [horth, Matrix.one_mulVec]
    _ = ∑ k, x k ^ 2 := by simp [dotProduct, pow_two]

/-- In particular, every column of a real orthogonal matrix has squared norm
one, in the exact form used by `finite_universal_certificate`. -/
theorem orthogonal_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1) (k : ι) :
    (∑ j, U j k ^ 2) = 1 := by
  have hk := congr_fun (congr_fun horth k) k
  simpa [Matrix.mul_apply, pow_two] using hk

/-- Bessel's inequality grouped into the cosine/sine pair belonging to each
mode.  This is the Hilbert-space form of the two estimates used in
Proposition 3.2. -/
theorem paired_bessel_inequality
    {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : ι × Fin 2 → E) (hv : Orthonormal ℝ v) (f : E) :
    (∑ k : ι, (
      ⟪v (k, (0 : Fin 2)), f⟫_ℝ ^ 2 +
        ⟪v (k, (1 : Fin 2)), f⟫_ℝ ^ 2)) ≤ ‖f‖ ^ 2 := by
  have hb := hv.sum_inner_products_le f (s := Finset.univ)
  simp only [Finset.mem_univ, Real.norm_eq_abs, sq_abs, Finset.sum_const_zero,
    Fintype.sum_prod_type, Fin.sum_univ_two] at hb
  exact hb

/-- Applying paired Bessel estimates in two tangent directions supplies the
energy hypotheses of the orthogonal Jacobian budget. -/
theorem bessel_jacobian_budget
    {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (v : ι × Fin 2 → E) (hv : Orthonormal ℝ v) (f g : E)
    (p q : ι → ℝ × ℝ)
    (hp : ∀ k, p k =
      (⟪v (k, (0 : Fin 2)), f⟫_ℝ, ⟪v (k, (1 : Fin 2)), f⟫_ℝ))
    (hq : ∀ k, q k =
      (⟪v (k, (0 : Fin 2)), g⟫_ℝ, ⟪v (k, (1 : Fin 2)), g⟫_ℝ))
    (budget : ℝ) (hbudget : ‖f‖ ^ 2 + ‖g‖ ^ 2 ≤ 2 * budget) :
    (∑ k, planarJacobian (p k) (q k)) ≤ budget := by
  apply orthogonal_jacobian_budget p q (‖f‖ ^ 2) (‖g‖ ^ 2) budget
  · simpa only [planarNormSq, hp] using paired_bessel_inequality v hv f
  · simpa only [planarNormSq, hq] using paired_bessel_inequality v hv g
  · exact hbudget

end

end GromovFilling
