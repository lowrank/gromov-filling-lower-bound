import GromovFilling.Universal

/-!
# Curves with a dominant first harmonic

This is the metric core of Lemma 5.3 in the note.  We work directly on the
unit circle in `ℂ`; the proof is independent of winding-number machinery.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Chords do not expand by more than a factor `n` under the `n`th power map
on the closed complex unit disk. -/
lemma norm_pow_sub_pow_le (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ n * ‖z - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      have hzn : ‖z ^ n‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      calc
        ‖z ^ (n + 1) - w ^ (n + 1)‖ =
            ‖z ^ n * (z - w) + (z ^ n - w ^ n) * w‖ := by
              congr 1
              ring
        _ ≤ ‖z ^ n * (z - w)‖ + ‖(z ^ n - w ^ n) * w‖ := norm_add_le _ _
        _ = ‖z ^ n‖ * ‖z - w‖ + ‖z ^ n - w ^ n‖ * ‖w‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ 1 * ‖z - w‖ + (n * ‖z - w‖) * 1 := by gcongr
        _ = ((n : ℝ) + 1) * ‖z - w‖ := by ring

/-- The unit circle, represented without choosing angular coordinates. -/
abbrev ComplexUnitCircle := {z : ℂ // ‖z‖ = 1}

/-- A finite complex Fourier polynomial with its first harmonic separated. -/
def dominantHarmonicCurve {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ComplexUnitCircle) : ℂ :=
  a₁ * z + ∑ k, a k * (z : ℂ) ^ m k

/-- Strict derivative-weighted dominance of the first harmonic makes the
Fourier polynomial injective on the circle. -/
theorem dominantHarmonicCurve_injective {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    Function.Injective (dominantHarmonicCurve a₁ m a) := by
  intro z w hcurve
  apply Subtype.ext
  by_contra hne
  have hzw : 0 < ‖(z : ℂ) - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hz : ‖(z : ℂ)‖ ≤ 1 := z.property.le
  have hw : ‖(w : ℂ)‖ ≤ 1 := w.property.le
  have heq :
      a₁ * ((z : ℂ) - w) =
        -(∑ k, (a k * (z : ℂ) ^ m k - a k * (w : ℂ) ^ m k)) := by
    unfold dominantHarmonicCurve at hcurve
    rw [Finset.sum_sub_distrib]
    linear_combination hcurve
  have hterm (k : ι) :
      ‖a k * (z : ℂ) ^ m k - a k * (w : ℂ) ^ m k‖ ≤
        ((m k : ℝ) * ‖a k‖) * ‖(z : ℂ) - w‖ := by
    rw [← mul_sub, norm_mul]
    calc
      ‖a k‖ * ‖(z : ℂ) ^ m k - (w : ℂ) ^ m k‖ ≤
          ‖a k‖ * ((m k : ℝ) * ‖(z : ℂ) - w‖) := by
            gcongr
            exact norm_pow_sub_pow_le z w hz hw (m k)
      _ = ((m k : ℝ) * ‖a k‖) * ‖(z : ℂ) - w‖ := by ring
  have hupper :
      ‖a₁‖ * ‖(z : ℂ) - w‖ ≤
        (∑ k, (m k : ℝ) * ‖a k‖) * ‖(z : ℂ) - w‖ := by
    calc
      ‖a₁‖ * ‖(z : ℂ) - w‖ = ‖a₁ * ((z : ℂ) - w)‖ := (norm_mul _ _).symm
      _ = ‖∑ k, (a k * (z : ℂ) ^ m k - a k * (w : ℂ) ^ m k)‖ := by
            rw [heq, norm_neg]
      _ ≤ ∑ k, ‖a k * (z : ℂ) ^ m k - a k * (w : ℂ) ^ m k‖ :=
            norm_sum_le _ _
      _ ≤ ∑ k, (((m k : ℝ) * ‖a k‖) * ‖(z : ℂ) - w‖) := by
            exact Finset.sum_le_sum fun k _ ↦ hterm k
      _ = (∑ k, (m k : ℝ) * ‖a k‖) * ‖(z : ℂ) - w‖ := by
            rw [Finset.sum_mul]
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hdom hzw)) hupper

end

end GromovFilling
