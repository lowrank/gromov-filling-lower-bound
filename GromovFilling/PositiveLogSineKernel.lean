import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Positivity of the logarithmic sine kernel

This module verifies the elementary off-diagonal kernel inequality used in
Proposition 8.1 of `fourier_resonant_filling_area_v3.tex`.

The displayed logarithmic expression is mathematically meaningful only away
from the diagonal.  Lean's real division and logarithm are total functions, so
all positivity theorems below state the necessary hypothesis `t ≠ s`
explicitly.  This module does not yet identify the expression with the
corresponding infinite Fourier series.
-/

namespace GromovFilling

noncomputable section

/-- The logarithmic form of the sine kernel from Proposition 8.1.

Its intended analytic domain is `0 < t, s < π` with `t ≠ s`; the definition
is total only because Lean's real division and logarithm are total. -/
def logarithmicSineKernel (t s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
    (Real.sin ((t + s) / 2) / Real.sin (|t - s| / 2))

/-- The trigonometric identity that drives positivity of the kernel. -/
theorem sin_sq_half_add_sub_sin_sq_half_abs_sub (t s : ℝ) :
    Real.sin ((t + s) / 2) ^ 2 - Real.sin (|t - s| / 2) ^ 2 =
      Real.sin t * Real.sin s := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have hsum : 2 * ((t + s) / 2) = t + s := by ring
  have hdiff : 2 * (|t - s| / 2) = |t - s| := by ring
  rw [hsum, hdiff, Real.cos_abs, Real.cos_add, Real.cos_sub]
  ring

/-- The numerator sine is positive in the open square `(0, π) × (0, π)`. -/
theorem logarithmicSineKernel_numerator_pos
    {t s : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi)
    (hs0 : 0 < s) (hspi : s < Real.pi) :
    0 < Real.sin ((t + s) / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith

/-- The denominator sine is positive in the open square away from the
diagonal. -/
theorem logarithmicSineKernel_denominator_pos
    {t s : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi)
    (hs0 : 0 < s) (hspi : s < Real.pi) (hts : t ≠ s) :
    0 < Real.sin (|t - s| / 2) := by
  have habs_pos : 0 < |t - s| :=
    abs_pos.mpr (sub_ne_zero.mpr hts)
  have habs_lt : |t - s| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · nlinarith [Real.pi_pos]

/-- In the open square away from the diagonal, the denominator sine is
strictly smaller than the numerator sine. -/
theorem logarithmicSineKernel_denominator_lt_numerator
    {t s : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi)
    (hs0 : 0 < s) (hspi : s < Real.pi) (hts : t ≠ s) :
    Real.sin (|t - s| / 2) < Real.sin ((t + s) / 2) := by
  have hnum := logarithmicSineKernel_numerator_pos ht0 htpi hs0 hspi
  have hden := logarithmicSineKernel_denominator_pos ht0 htpi hs0 hspi hts
  have ht_sin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hs_sin : 0 < Real.sin s :=
    Real.sin_pos_of_pos_of_lt_pi hs0 hspi
  have hfactor :
      0 < (Real.sin ((t + s) / 2) - Real.sin (|t - s| / 2)) *
        (Real.sin ((t + s) / 2) + Real.sin (|t - s| / 2)) := by
    calc
      _ = Real.sin ((t + s) / 2) ^ 2 -
          Real.sin (|t - s| / 2) ^ 2 := by ring
      _ = Real.sin t * Real.sin s :=
        sin_sq_half_add_sub_sin_sq_half_abs_sub t s
      _ > 0 := mul_pos ht_sin hs_sin
  rcases (mul_pos_iff.mp hfactor) with hpos | hneg
  · linarith [hpos.1]
  · linarith [hneg.2, add_pos hnum hden]

/-- The quotient inside the logarithm is strictly larger than one. -/
theorem logarithmicSineKernel_ratio_gt_one
    {t s : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi)
    (hs0 : 0 < s) (hspi : s < Real.pi) (hts : t ≠ s) :
    1 < Real.sin ((t + s) / 2) / Real.sin (|t - s| / 2) := by
  apply (one_lt_div
    (logarithmicSineKernel_denominator_pos ht0 htpi hs0 hspi hts)).2
  exact logarithmicSineKernel_denominator_lt_numerator ht0 htpi hs0 hspi hts

/-- The logarithmic sine kernel is strictly positive at every interior
off-diagonal point. -/
theorem logarithmicSineKernel_pos
    {t s : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi)
    (hs0 : 0 < s) (hspi : s < Real.pi) (hts : t ≠ s) :
    0 < logarithmicSineKernel t s := by
  unfold logarithmicSineKernel
  exact mul_pos (by norm_num) <| Real.log_pos <|
    logarithmicSineKernel_ratio_gt_one ht0 htpi hs0 hspi hts

/-- The logarithmic sine kernel is symmetric. -/
theorem logarithmicSineKernel_comm (t s : ℝ) :
    logarithmicSineKernel t s = logarithmicSineKernel s t := by
  simp [logarithmicSineKernel, add_comm, abs_sub_comm]

end

end GromovFilling
