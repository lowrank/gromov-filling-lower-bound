import GromovFilling.Givens
import GromovFilling.DominantHarmonic

/-!
# Mixed boundary curves

This file connects the explicit Givens matrix to the dominant-harmonic
embedding criterion.  It is the formal bridge from Lemma 5.2 to the Jordan
curve assertion in Lemma 5.3 of the note.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

lemma boundaryRadius_oddMode_pos (k : ℕ) : 0 < boundaryRadius (oddMode k) := by
  unfold boundaryRadius
  have : (0 : ℝ) < oddMode k := by
    unfold oddMode
    push_cast
    positivity
  positivity

/-- After differentiation, the radius of odd mode `2k+1` is the first-mode
radius times its reciprocal frequency. -/
lemma oddMode_mul_boundaryRadius (k : ℕ) :
    (oddMode k : ℝ) * boundaryRadius (oddMode k) =
      boundaryRadius (oddMode 0) * oddWeight k := by
  have hk : (oddMode k : ℝ) ≠ 0 := by
    unfold oddMode
    push_cast
    positivity
  unfold boundaryRadius oddWeight oddMode
  push_cast
  field_simp [Real.pi_ne_zero, hk]
  ring

/-- Turn a higher-mode index into its index in the full `N`-mode vector. -/
def higherFinIndex {N : ℕ} (k : Fin (N - 1)) : Fin N :=
  ⟨k + 1, by omega⟩

/-- The mixed boundary Fourier curve belonging to one Givens row.  The
overall sign in the note is omitted, since it has no effect on injectivity
or enclosed area. -/
def givensBoundaryCurve {N : ℕ} (j : Fin N) : ComplexUnitCircle → ℂ :=
  dominantHarmonicCurve
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))

private lemma higher_index_sum {N : ℕ} (j : Fin N) :
    (∑ k : Fin (N - 1),
        oddWeight (k + 1) *
          |givensMatrix N j (higherFinIndex k)|) =
      ∑ k ∈ Finset.Ico 1 N,
        oddWeight k * |givensMix N (natBasis k) j| := by
  change (∑ k : Fin (N - 1),
      oddWeight ((k : ℕ) + 1) *
        |givensMix N (natBasis ((k : ℕ) + 1)) j|) = _
  calc
    _ = ∑ k ∈ Finset.range (N - 1),
        oddWeight (k + 1) * |givensMix N (natBasis (k + 1)) j| :=
      Fin.sum_univ_eq_sum_range
        (fun k ↦ oddWeight (k + 1) * |givensMix N (natBasis (k + 1)) j|)
        (N - 1)
    _ = _ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_comm]

/-- Every mixed boundary curve in the finite universal certificate is a
Jordan parametrization (injective on the unit circle). -/
theorem givensBoundaryCurve_injective {N : ℕ} (j : Fin N) :
    Function.Injective (givensBoundaryCurve j) := by
  apply dominantHarmonicCurve_injective
  have hrho : 0 < boundaryRadius (oddMode 0) := boundaryRadius_oddMode_pos _
  have hrow := givensMix_row_dominance N j j.isLt
  have hscaled := mul_lt_mul_of_pos_left hrow hrho
  calc
    (∑ k : Fin (N - 1),
        (oddMode (k + 1) : ℝ) *
          ‖((boundaryRadius (oddMode (k + 1)) *
            givensMatrix N j (higherFinIndex k) : ℝ) : ℂ)‖) =
        boundaryRadius (oddMode 0) *
          ∑ k : Fin (N - 1),
            oddWeight (k + 1) *
              |givensMatrix N j (higherFinIndex k)| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (boundaryRadius_oddMode_pos (k + 1)),
            ← mul_assoc, oddMode_mul_boundaryRadius]
          ring
    _ = boundaryRadius (oddMode 0) *
          ∑ k ∈ Finset.Ico 1 N,
            oddWeight k * |givensMix N (natBasis k) j| := by
          rw [higher_index_sum]
    _ < boundaryRadius (oddMode 0) *
          |givensMix N (natBasis 0) j| := hscaled
    _ = ‖((boundaryRadius (oddMode 0) *
          givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hrho]
          rfl

end

end GromovFilling
