import GromovFilling.InfiniteResonantVariation
import GromovFilling.SharpenedOriented

/-!
# Cancellation in the infinite mixed correlation

The term at index zero cancels identically. Cauchy--Schwarz on the two
remaining coefficient tails improves the old factor two to one and removes
the frequency-three profile coordinate from the bound.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace GromovFilling

noncomputable section

lemma infiniteComplexEnergy_zero_add_tail (c : ℕ → ℂ)
    (hc : Summable (fun k ↦ Complex.normSq (c k))) :
    infiniteComplexEnergy c = ‖c 0‖ ^ 2 +
      infiniteComplexEnergy (fun k ↦ c (k + 1)) := by
  simpa only [infiniteComplexEnergy, Complex.sq_norm] using hc.tsum_eq_zero_add

/-- The lowest mixed-correlation term is zero, so both sums start at the
next index. -/
lemma infiniteOddMixedCorrelation_eq_tail
    (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    infiniteOddMixedCorrelation y c =
      -(∑' k, y (k + 1) * star (c (-(oddMode (k + 1) : ℤ)))) * c 1 +
        star (c (-1)) * (∑' k, y (k + 1) * c (oddMode (k + 1) : ℤ)) := by
  have hnegStar : Summable
      (fun k ↦ Complex.normSq (star (c (-(oddMode k : ℤ))))) := by
    simpa only [Complex.star_def, Complex.normSq_conj] using hneg
  have hfirst := summable_mul_of_summable_normSq y
    (fun k ↦ star (c (-(oddMode k : ℤ)))) hy hnegStar
  have hsecond := summable_mul_of_summable_normSq y
    (fun k ↦ c (oddMode k : ℤ)) hy hpos
  rw [infiniteOddMixedCorrelation_decomposition y c hy hpos hneg,
    hfirst.tsum_eq_zero_add, hsecond.tsum_eq_zero_add]
  simp only [oddMode, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
    mul_zero, zero_add]
  ring

/-- The two tail contributions fit a single Cauchy--Schwarz estimate. -/
lemma two_tail_cauchy (a b P N : ℝ)
    (hP : 0 ≤ P) (_hN : 0 ≤ N)
    (ha : a ^ 2 ≤ P) (hb : b ^ 2 ≤ N) :
    b * Real.sqrt (P - a ^ 2) + a * Real.sqrt (N - b ^ 2) ≤
      Real.sqrt P * Real.sqrt N := by
  have hp := Real.sq_sqrt (sub_nonneg.mpr ha)
  have hn := Real.sq_sqrt (sub_nonneg.mpr hb)
  have hcs := sq_nonneg
    (a * b - Real.sqrt (P - a ^ 2) * Real.sqrt (N - b ^ 2))
  have hidentity :
      (b * Real.sqrt (P - a ^ 2) + a * Real.sqrt (N - b ^ 2)) ^ 2 +
        (a * b - Real.sqrt (P - a ^ 2) * Real.sqrt (N - b ^ 2)) ^ 2 = P * N := by
    calc
      _ = (a ^ 2 + (Real.sqrt (P - a ^ 2)) ^ 2) *
          (b ^ 2 + (Real.sqrt (N - b ^ 2)) ^ 2) := by ring
      _ = P * N := by rw [hp, hn]; ring
  rw [← Real.sqrt_mul hP]
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hcs, hidentity]

/-- The mixed correlation uses the profile tail after its first component,
with coefficient one. -/
theorem norm_infiniteOddMixedCorrelation_le_cancelled
    (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1) :
    ‖infiniteOddMixedCorrelation y c‖ ≤
      Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
        Real.sqrt (infiniteNegativeOddEnergy c) := by
  let cp : ℕ → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cn : ℕ → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  let Y : ℝ := Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1)))
  let P : ℝ := infinitePositiveOddEnergy c
  let N : ℝ := infiniteNegativeOddEnergy c
  have hyt : Summable (fun k ↦ Complex.normSq (y (k + 1))) := by
    simpa only [Function.comp_def] using hy.comp_injective Nat.succ_injective
  have hpt : Summable (fun k ↦ Complex.normSq (cp (k + 1))) := by
    simpa only [Function.comp_def, cp] using hpos.comp_injective Nat.succ_injective
  have hnt : Summable (fun k ↦ Complex.normSq (star (cn (k + 1)))) := by
    simpa only [Function.comp_def, cn, Complex.star_def, Complex.normSq_conj]
      using hneg.comp_injective Nat.succ_injective
  have hP0 : 0 ≤ P := infiniteComplexEnergy_nonneg _
  have hN0 : 0 ≤ N := infiniteComplexEnergy_nonneg _
  have hp : P = ‖c 1‖ ^ 2 + infiniteComplexEnergy (fun k ↦ cp (k + 1)) := by
    simpa [P, infinitePositiveOddEnergy, cp, oddMode] using
      infiniteComplexEnergy_zero_add_tail cp hpos
  have hn : N = ‖c (-1)‖ ^ 2 + infiniteComplexEnergy (fun k ↦ cn (k + 1)) := by
    simpa [N, infiniteNegativeOddEnergy, cn, oddMode] using
      infiniteComplexEnergy_zero_add_tail cn hneg
  have hpTail : infiniteComplexEnergy (fun k ↦ cp (k + 1)) = P - ‖c 1‖ ^ 2 := by
    linarith
  have hnTail : infiniteComplexEnergy (fun k ↦ cn (k + 1)) = N - ‖c (-1)‖ ^ 2 := by
    linarith
  have hfirst : ‖∑' k, y (k + 1) * star (cn (k + 1))‖ ≤
      Y * Real.sqrt (N - ‖c (-1)‖ ^ 2) := by
    have h := norm_tsum_mul_le_sqrt_infiniteComplexEnergy
      (fun k ↦ y (k + 1)) (fun k ↦ star (cn (k + 1))) hyt hnt
    have hstar : infiniteComplexEnergy (fun k ↦ star (cn (k + 1))) =
        infiniteComplexEnergy (fun k ↦ cn (k + 1)) := by
      simp only [infiniteComplexEnergy, Complex.star_def, Complex.normSq_conj]
    rw [hstar, hnTail] at h
    exact h
  have hsecond : ‖∑' k, y (k + 1) * cp (k + 1)‖ ≤
      Y * Real.sqrt (P - ‖c 1‖ ^ 2) := by
    have h := norm_tsum_mul_le_sqrt_infiniteComplexEnergy
      (fun k ↦ y (k + 1)) (fun k ↦ cp (k + 1)) hyt hpt
    simpa only [hpTail, Y] using h
  have ha : ‖c 1‖ ^ 2 ≤ P := by
    linarith [infiniteComplexEnergy_nonneg (fun k ↦ cp (k + 1))]
  have hb : ‖c (-1)‖ ^ 2 ≤ N := by
    linarith [infiniteComplexEnergy_nonneg (fun k ↦ cn (k + 1))]
  have hcs := two_tail_cauchy ‖c 1‖ ‖c (-1)‖ P N hP0 hN0 ha hb
  have hPsqrt : Real.sqrt P ≤ 1 := by
    change P ≤ 1 at hPos
    nlinarith [Real.sq_sqrt hP0, Real.sqrt_nonneg P]
  rw [infiniteOddMixedCorrelation_eq_tail y c hy hpos hneg]
  change ‖-(∑' k, y (k + 1) * star (cn (k + 1))) * c 1 +
      star (c (-1)) * (∑' k, y (k + 1) * cp (k + 1))‖ ≤ Y * Real.sqrt N
  calc
    _ ≤ ‖-(∑' k, y (k + 1) * star (cn (k + 1))) * c 1‖ +
        ‖star (c (-1)) * (∑' k, y (k + 1) * cp (k + 1))‖ := norm_add_le _ _
    _ = ‖∑' k, y (k + 1) * star (cn (k + 1))‖ * ‖c 1‖ +
        ‖c (-1)‖ * ‖∑' k, y (k + 1) * cp (k + 1)‖ := by
      simp only [norm_mul, norm_neg, norm_star]
    _ ≤ (Y * Real.sqrt (N - ‖c (-1)‖ ^ 2)) * ‖c 1‖ +
        ‖c (-1)‖ * (Y * Real.sqrt (P - ‖c 1‖ ^ 2)) := by gcongr
    _ = Y * (‖c (-1)‖ * Real.sqrt (P - ‖c 1‖ ^ 2) +
        ‖c 1‖ * Real.sqrt (N - ‖c (-1)‖ ^ 2)) := by ring
    _ ≤ Y * (Real.sqrt P * Real.sqrt N) := by
      exact mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
    _ ≤ Y * (1 * Real.sqrt N) := by dsimp [Y]; gcongr
    _ = Y * Real.sqrt N := by ring

end

end GromovFilling

#print axioms GromovFilling.infiniteOddMixedCorrelation_eq_tail
#print axioms GromovFilling.norm_infiniteOddMixedCorrelation_le_cancelled
