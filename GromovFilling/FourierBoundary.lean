import GromovFilling.Constants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact Fourier coefficients of the boundary distance profile

This file formalizes the elementary integration-by-parts computation in
Lemma 4.1 of the note.
-/

namespace GromovFilling

noncomputable section

open MeasureTheory Real

private lemma integral_mul_cos_nat (n : ℕ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, x * Real.cos ((n : ℝ) * x)) =
      (((-1 : ℝ) ^ n) - 1) / (n : ℝ) ^ 2 := by
  let F : ℝ → ℝ := fun x ↦
    x * Real.sin ((n : ℝ) * x) / (n : ℝ) +
      Real.cos ((n : ℝ) * x) / (n : ℝ) ^ 2
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hderiv (x : ℝ) : HasDerivAt F (x * Real.cos ((n : ℝ) * x)) x := by
    have hlin : HasDerivAt (fun y : ℝ ↦ (n : ℝ) * y) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin ((n : ℝ) * y))
        (Real.cos ((n : ℝ) * x) * (n : ℝ)) x := by
      simpa only [Function.comp_apply] using (Real.hasDerivAt_sin _).comp x hlin
    have hcos : HasDerivAt (fun y : ℝ ↦ Real.cos ((n : ℝ) * y))
        (-Real.sin ((n : ℝ) * x) * (n : ℝ)) x := by
      simpa only [Function.comp_apply] using (Real.hasDerivAt_cos _).comp x hlin
    have h := (((hasDerivAt_id x).mul hsin).div_const (n : ℝ)).add
      (hcos.div_const ((n : ℝ) ^ 2))
    convert h using 1
    all_goals simp only [F, id_eq]
    field_simp [hnR]
    ring
  have hint : IntervalIntegrable (fun x : ℝ ↦ x * Real.cos ((n : ℝ) * x))
      volume 0 Real.pi := by
    exact (continuous_id.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x) hint
  have hsinpi : Real.sin ((n : ℝ) * Real.pi) = 0 := by
    exact Real.sin_nat_mul_pi n
  have hcospi : Real.cos ((n : ℝ) * Real.pi) = (-1 : ℝ) ^ n := by
    simpa using Real.cos_add_nat_mul_pi 0 n
  rw [hfund]
  dsimp [F]
  rw [hsinpi, hcospi]
  field_simp [hnR]
  norm_num

/-- Exact cosine coefficient of the triangle wave `|x|` on `[-π,π]`. -/
theorem triangleWave_cos_coefficient (n : ℕ) (hn : n ≠ 0) :
    (1 / Real.pi) *
        (∫ x in (-Real.pi)..Real.pi, |x| * Real.cos ((n : ℝ) * x)) =
      (2 / (Real.pi * (n : ℝ) ^ 2)) * (((-1 : ℝ) ^ n) - 1) := by
  let f : ℝ → ℝ := fun x ↦ |x| * Real.cos ((n : ℝ) * x)
  have hf : Continuous f := by
    change Continuous (fun x : ℝ ↦ |x| * Real.cos ((n : ℝ) * x))
    fun_prop
  have hneg : (∫ x in (-Real.pi)..(0 : ℝ), f x) =
      ∫ x in (0 : ℝ)..Real.pi, f x := by
    calc
      (∫ x in (-Real.pi)..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..Real.pi, f (-x) := by
        convert (intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f).symm using 1
        norm_num
      _ = ∫ x in (0 : ℝ)..Real.pi, f x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp [f, mul_neg, Real.cos_neg]
  have hsplit :
      (∫ x in (-Real.pi)..Real.pi, f x) =
        2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-Real.pi) 0) (hf.intervalIntegrable 0 Real.pi), hneg]
    ring
  have hpos :
      (∫ x in (0 : ℝ)..Real.pi, f x) =
        ∫ x in (0 : ℝ)..Real.pi, x * Real.cos ((n : ℝ) * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [Set.uIcc_of_le Real.pi_pos.le] at hx
      exact hx.1
    simp [f, abs_of_nonneg hx0]
  rw [show (∫ x in (-Real.pi)..Real.pi, |x| * Real.cos ((n : ℝ) * x)) =
      ∫ x in (-Real.pi)..Real.pi, f x by rfl, hsplit, hpos, integral_mul_cos_nat n hn]
  field_simp [Real.pi_ne_zero]

/-- Odd modes have coefficient `-4/(π n²)`. -/
theorem triangleWave_cos_coefficient_of_odd (n : ℕ) (hn : Odd n) :
    (1 / Real.pi) *
        (∫ x in (-Real.pi)..Real.pi, |x| * Real.cos ((n : ℝ) * x)) =
      -4 / (Real.pi * (n : ℝ) ^ 2) := by
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, rfl⟩
    omega
  rw [triangleWave_cos_coefficient n hn0, Odd.neg_one_pow hn]
  ring

/-- Even positive modes have zero coefficient. -/
theorem triangleWave_cos_coefficient_of_even (n : ℕ) (hn : Even n) (hn0 : n ≠ 0) :
    (1 / Real.pi) *
        (∫ x in (-Real.pi)..Real.pi, |x| * Real.cos ((n : ℝ) * x)) = 0 := by
  rw [triangleWave_cos_coefficient n hn0, Even.neg_one_pow hn]
  ring

end

end GromovFilling
