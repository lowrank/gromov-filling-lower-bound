import GromovFilling.InfiniteResonantComass

/-!
# The profile tail starting at frequency five

The weighted Fourier energy already used for the original nonlinear bound
also bounds the shorter tail needed after cancellation of its first term.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

theorem oddProfileFourierMap_first_add_twenty_five_tail_energy_le_two
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) (N : ℕ) :
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
      25 * finiteComplexEnergy (fun n : Fin N ↦
        oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x) ≤ 2 := by
  have hweighted := sum_oddProfileFourierMap_weighted_sq_le_two hboundary x (N + 2)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hweighted
  have htail :
      25 * finiteComplexEnergy (fun n : Fin N ↦
        oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x) ≤
      ∑ n : Fin N, (oddMode ((n : ℕ) + 2) : ℝ) ^ 2 *
        ‖oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x‖ ^ 2 := by
    unfold finiteComplexEnergy
    simp_rw [← Complex.sq_norm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hmodeNat : 5 ≤ oddMode ((n : ℕ) + 2) := by dsimp only [oddMode]; omega
    have hmode : (5 : ℝ) ≤ oddMode ((n : ℕ) + 2) := by exact_mod_cast hmodeNat
    have hmodeSq : (25 : ℝ) ≤ (oddMode ((n : ℕ) + 2) : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hmodeSq (sq_nonneg _)
  have hweighted' :
      ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
        9 * ‖oddProfileFourierMap boundary (oddMode 1) x‖ ^ 2 +
        ∑ n : Fin N, (oddMode ((n : ℕ) + 2) : ℝ) ^ 2 *
          ‖oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x‖ ^ 2 ≤ 2 := by
    simpa [Fin.val_succ, Nat.succ_eq_add_one, oddMode, add_assoc] using hweighted
  nlinarith [sq_nonneg ‖oddProfileFourierMap boundary (oddMode 1) x‖]

/-- The exact weight-25 tail inequality in the revised Section 4. -/
theorem oddProfileFourierMap_first_add_twenty_five_infiniteTailEnergy_le_two
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
      25 * infiniteComplexEnergy (fun n ↦
        oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x) ≤ 2 := by
  let a : ℂ := oddProfileFourierMap boundary (oddMode 0) x
  let tail : ℕ → ℂ := fun n ↦ oddProfileFourierMap boundary (oddMode ((n : ℕ) + 2)) x
  have hsum : infiniteComplexEnergy tail ≤ (2 - ‖a‖ ^ 2) / 25 := by
    unfold infiniteComplexEnergy
    apply Real.tsum_le_of_sum_range_le (fun n ↦ Complex.normSq_nonneg (tail n))
    intro N
    have hfinite := oddProfileFourierMap_first_add_twenty_five_tail_energy_le_two
      hboundary x N
    change ‖a‖ ^ 2 + 25 * finiteComplexEnergy (fun n : Fin N ↦ tail n) ≤ 2 at hfinite
    unfold finiteComplexEnergy at hfinite
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ Complex.normSq (tail n)) N] at hfinite
    nlinarith
  change ‖a‖ ^ 2 + 25 * infiniteComplexEnergy tail ≤ 2
  nlinarith

end

end GromovFilling

#print axioms GromovFilling.oddProfileFourierMap_first_add_twenty_five_infiniteTailEnergy_le_two
