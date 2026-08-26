import GromovFilling.Universal

/-!
# The pointwise orthogonal Jacobian budget

This file contains the finite-dimensional inequality at the heart of
Proposition 3.2.  Analytic Bessel estimates supply bounds for the two square
energies; the result below converts those bounds into a sum of absolute
two-dimensional Jacobians.
-/

open scoped BigOperators

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

/-- A matrix with `UᵀU = I` preserves the sum of coordinate squares. -/
theorem orthogonal_mulVec_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1) (x : ι → ℝ) :
    (∑ j, (U.mulVec x j) ^ 2) = ∑ k, x k ^ 2 := by
  calc
    (∑ j, (U.mulVec x j) ^ 2) =
        Matrix.dotProduct (U.mulVec x) (U.mulVec x) := by
          simp [Matrix.dotProduct, pow_two]
    _ = Matrix.dotProduct (Matrix.vecMul (U.mulVec x) U) x :=
      Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.dotProduct (U.transpose.mulVec (U.mulVec x)) x := by
      rw [Matrix.mulVec_transpose]
    _ = Matrix.dotProduct ((U.transpose * U).mulVec x) x := by
      rw [Matrix.mulVec_mulVec]
    _ = Matrix.dotProduct x x := by rw [horth, Matrix.one_mulVec]
    _ = ∑ k, x k ^ 2 := by simp [Matrix.dotProduct, pow_two]

/-- In particular, every column of a real orthogonal matrix has squared norm
one, in the exact form used by `finite_universal_certificate`. -/
theorem orthogonal_column_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1) (k : ι) :
    (∑ j, U j k ^ 2) = 1 := by
  have hk := congr_fun (congr_fun horth k) k
  simpa [Matrix.mul_apply, pow_two] using hk

end

end GromovFilling
