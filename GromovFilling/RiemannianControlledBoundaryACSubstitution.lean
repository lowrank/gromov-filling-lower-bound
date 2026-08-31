import GromovFilling.RiemannianControlledBoundaryParameterLipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Absolutely continuous substitution for boundary phases

A controlled boundary parameter is naturally Lipschitz rather than `C¹`.
This module proves the corresponding one-dimensional substitution theorem at
the correct regularity: a Lipschitz phase is absolutely continuous, hence
differentiable almost everywhere, and the fundamental theorem of calculus
applies to the composition with an integral primitive.
-/

open Function MeasureTheory Set
open scoped NNReal

namespace GromovFilling

noncomputable section

/-- A Lipschitz real function on a compact interval has its ordinary
derivative almost everywhere on that interval. -/
theorem ae_hasDerivAt_deriv_of_lipschitzOnWith_uIcc
    {a b : ℝ} {phase : ℝ → ℝ} {K : ℝ≥0}
    (hphase : LipschitzOnWith K phase (Set.uIcc a b)) :
    ∀ᵐ y : ℝ, y ∈ Set.uIcc a b →
      HasDerivAt phase (deriv phase y) y := by
  filter_upwards
      [hphase.absolutelyContinuousOnInterval.ae_differentiableAt]
      with y hy hyInterval
  exact (hy hyInterval).hasDerivAt

/-- Change of variables for a Lipschitz real phase and a continuous bounded
integrand.  No everywhere derivative or continuous derivative is assumed:
the proof applies the absolutely-continuous fundamental theorem to the
composition of the phase with an integral primitive of `f`. -/
theorem intervalIntegral_comp_mul_deriv_of_lipschitzOnWith
    {a b : ℝ} {phase f : ℝ → ℝ} {K C : ℝ≥0}
    (hphase : LipschitzOnWith K phase (Set.uIcc a b))
    (hf : Continuous f) (hfBound : ∀ x, ‖f x‖₊ ≤ C) :
    (∫ y in a..b, f (phase y) * deriv phase y) =
      ∫ t in phase a..phase b, f t := by
  let F : ℝ → ℝ := fun u ↦ ∫ t in 0..u, f t
  have hFderiv (u : ℝ) : HasDerivAt F (f u) u := by
    simpa only [F] using
      (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hFdiff : Differentiable ℝ F :=
    fun u ↦ (hFderiv u).differentiableAt
  have hFLipschitz : LipschitzWith C F := by
    apply lipschitzWith_of_nnnorm_deriv_le hFdiff
    intro u
    rw [(hFderiv u).deriv]
    exact hfBound u
  have hcompLipschitz : LipschitzOnWith (C * K) (F ∘ phase)
      (Set.uIcc a b) :=
    hFLipschitz.comp_lipschitzOnWith hphase
  have hcompAbsolutelyContinuous :
      AbsolutelyContinuousOnInterval (F ∘ phase) a b :=
    hcompLipschitz.absolutelyContinuousOnInterval
  have hchain : ∀ᵐ y : ℝ, y ∈ Set.uIcc a b →
      deriv (F ∘ phase) y = f (phase y) * deriv phase y := by
    filter_upwards
        [hphase.absolutelyContinuousOnInterval.ae_differentiableAt]
        with y hy hyInterval
    exact ((hFderiv (phase y)).comp y
      (hy hyInterval).hasDerivAt).deriv
  calc
    (∫ y in a..b, f (phase y) * deriv phase y) =
        ∫ y in a..b, deriv (F ∘ phase) y := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hchain] with y hy hyInterval
      exact (hy (Set.uIoc_subset_uIcc hyInterval)).symm
    _ = (F ∘ phase) b - (F ∘ phase) a :=
      hcompAbsolutelyContinuous.integral_deriv_eq_sub
    _ = ∫ t in phase a..phase b, f t := by
      simp only [Function.comp_apply, F]
      exact intervalIntegral.integral_interval_sub_left
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- If a periodic continuous function vanishes on the unused part of one
period, integrating over the remaining local arc gives the full-period
integral.  This is the support argument needed for a boundary partition
subordinate to one controlled chart. -/
theorem intervalIntegral_eq_periodic_of_eq_zero_on_complement
    {f : ℝ → ℝ} {a b T s : ℝ}
    (hf : Continuous f) (hperiodic : Function.Periodic f T)
    (hab : a ≤ b) (hbT : b ≤ a + T)
    (hzero : ∀ t ∈ Set.Ioo b (a + T), f t = 0) :
    (∫ t in a..b, f t) = ∫ t in s..s + T, f t := by
  have habIntegrable : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable _ _
  have hbTIntegrable : IntervalIntegrable f volume b (a + T) :=
    hf.intervalIntegrable _ _
  have hzeroIntegral : (∫ t in b..a + T, f t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [Measure.ae_ne volume (a + T)] with t hne ht
    rw [Set.uIoc_of_le hbT] at ht
    exact hzero t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
  calc
    (∫ t in a..b, f t) = ∫ t in a..a + T, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        habIntegrable hbTIntegrable, hzeroIntegral, add_zero]
    _ = ∫ t in s..s + T, f t :=
      hperiodic.intervalIntegral_add_eq a s

#print axioms ae_hasDerivAt_deriv_of_lipschitzOnWith_uIcc
#print axioms intervalIntegral_comp_mul_deriv_of_lipschitzOnWith
#print axioms intervalIntegral_eq_periodic_of_eq_zero_on_complement

end

end GromovFilling
