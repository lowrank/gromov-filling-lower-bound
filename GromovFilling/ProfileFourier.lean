import GromovFilling.DistanceProfile
import GromovFilling.FourierBoundary
import GromovFilling.Givens
import GromovFilling.BoundaryCertificate
import GromovFilling.BoundaryDegreeComponents
import GromovFilling.ComplexJacobianBudget
import GromovFilling.FourierBessel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Fourier coefficients of the metric boundary profile

This file connects the abstract distance profile to the exact triangle-wave
calculation.  Angles in radians are sent to the unit additive circle by
division by `2π`.
-/

open MeasureTheory Real Filter
open scoped Topology

namespace GromovFilling

noncomputable section

/-- The point of `ℝ / ℤ` represented by an angle measured in radians. -/
def angleToUnitAddCircle (t : ℝ) : UnitAddCircle :=
  ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- On the standard representative interval, the quotient-circle distance
from zero is the usual absolute angular distance divided by `2π`. -/
lemma unitAddCircle_dist_zero_angleToUnitAddCircle
    {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    2 * Real.pi * dist (0 : UnitAddCircle) (angleToUnitAddCircle t) = |t| := by
  have htwoPi : 0 < (2 * Real.pi : ℝ) := mul_pos (by norm_num) Real.pi_pos
  have habst : |t| ≤ Real.pi := by
    rw [abs_le]
    exact ht
  have hquot : |t / (2 * Real.pi)| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_div, abs_of_pos htwoPi, abs_one]
    calc
      |t| / (2 * Real.pi) ≤ Real.pi / (2 * Real.pi) :=
        div_le_div_of_nonneg_right habst htwoPi.le
      _ = 1 / 2 := by field_simp [Real.pi_ne_zero]
  have hnorm :
      ‖((t / (2 * Real.pi) : ℝ) : UnitAddCircle)‖ =
        |t / (2 * Real.pi)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 hquot
  rw [dist_eq_norm, zero_sub, norm_neg]
  change 2 * Real.pi * ‖((t / (2 * Real.pi) : ℝ) : UnitAddCircle)‖ = |t|
  rw [hnorm, abs_div, abs_of_pos htwoPi]
  field_simp [Real.pi_ne_zero]

/-- At the boundary base point, the metric odd profile is literally the
centered triangle wave on `[-π,π]`. -/
theorem oddDistanceProfile_at_boundary_base
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    oddDistanceProfile boundary (angleToUnitAddCircle t)
        (boundary (0 : UnitAddCircle)) = |t| - Real.pi / 2 := by
  rw [oddDistanceProfile_on_boundary hboundary]
  rw [unitAddCircle_dist_zero_angleToUnitAddCircle ht]

/-- Cosine coefficient of the metric odd profile at the boundary base
point, using the symmetric period `[-π,π]`. -/
def oddProfileCosineCoefficientAtBase
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (0 : UnitAddCircle)) * Real.cos ((n : ℝ) * t)

private lemma integral_cos_nat_symmetric (n : ℕ) (hn : n ≠ 0) :
    (∫ t in (-Real.pi)..Real.pi, Real.cos ((n : ℝ) * t)) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [intervalIntegral.integral_comp_mul_left Real.cos hnR]
  simp only [integral_cos]
  have hsin : Real.sin ((n : ℝ) * Real.pi) = 0 :=
    Real.sin_nat_mul_pi n
  rw [hsin]
  have hneg : (n : ℝ) * -Real.pi = -((n : ℝ) * Real.pi) := by ring
  rw [hneg, Real.sin_neg, hsin]
  simp

/-- The Fourier cosine coefficient extracted from an isometric boundary is
the exact odd-mode radius (with the sign dictated by the centered distance
wave). -/
theorem oddProfileCosineCoefficientAtBase_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) :
    oddProfileCosineCoefficientAtBase boundary n =
      -boundaryRadius n := by
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, rfl⟩
    omega
  have hprofile :
      (∫ t in (-Real.pi)..Real.pi,
        oddDistanceProfile boundary (angleToUnitAddCircle t)
            (boundary (0 : UnitAddCircle)) * Real.cos ((n : ℝ) * t)) =
        ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [oddDistanceProfile_at_boundary_base hboundary]
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  have habsInt : IntervalIntegrable
      (fun t : ℝ ↦ |t| * Real.cos ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosInt : IntervalIntegrable
      (fun t : ℝ ↦ Real.pi / 2 * Real.cos ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplit :
      (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) =
        (∫ t in (-Real.pi)..Real.pi,
          |t| * Real.cos ((n : ℝ) * t)) -
        Real.pi / 2 *
          ∫ t in (-Real.pi)..Real.pi, Real.cos ((n : ℝ) * t) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_sub habsInt hcosInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  unfold oddProfileCosineCoefficientAtBase boundaryRadius
  rw [hprofile, hsplit, integral_cos_nat_symmetric n hn0]
  simp only [mul_zero, sub_zero]
  rw [triangleWave_cos_coefficient_of_odd n hn]
  ring

/-- Sine coefficient of the metric odd profile at the boundary base point. -/
def oddProfileSineCoefficientAtBase
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (0 : UnitAddCircle)) * Real.sin ((n : ℝ) * t)

/-- The centered triangle wave is even, so every sine coefficient at the
boundary base point vanishes. -/
theorem oddProfileSineCoefficientAtBase_eq_zero
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    oddProfileSineCoefficientAtBase boundary n = 0 := by
  have hprofile :
      (∫ t in (-Real.pi)..Real.pi,
        oddDistanceProfile boundary (angleToUnitAddCircle t)
            (boundary (0 : UnitAddCircle)) * Real.sin ((n : ℝ) * t)) =
        ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [oddDistanceProfile_at_boundary_base hboundary]
    rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  let f : ℝ → ℝ := fun t ↦
    (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hneg :
      (∫ t in (-Real.pi)..(0 : ℝ), f t) =
        -(∫ t in (0 : ℝ)..Real.pi, f t) := by
    calc
      (∫ t in (-Real.pi)..(0 : ℝ), f t) =
          ∫ t in (0 : ℝ)..Real.pi, f (-t) := by
        convert (intervalIntegral.integral_comp_neg
          (a := 0) (b := Real.pi) f).symm using 1 <;> norm_num
      _ = ∫ t in (0 : ℝ)..Real.pi, -f t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [f]
        rw [show (n : ℝ) * -t = -((n : ℝ) * t) by ring,
          Real.sin_neg, abs_neg]
        ring
      _ = -(∫ t in (0 : ℝ)..Real.pi, f t) := by
        rw [intervalIntegral.integral_neg]
  have hzero : (∫ t in (-Real.pi)..Real.pi, f t) = 0 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (-Real.pi) 0)
      (hf.intervalIntegrable 0 Real.pi), hneg]
    ring
  unfold oddProfileSineCoefficientAtBase
  rw [hprofile, show
    (∫ t in (-Real.pi)..Real.pi,
      (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) =
        ∫ t in (-Real.pi)..Real.pi, f t by rfl, hzero]
  ring

/-- The complete complex boundary coefficient at the base point. -/
def oddProfileComplexCoefficientAtBase
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) : ℂ :=
  (oddProfileCosineCoefficientAtBase boundary n : ℂ) +
    Complex.I * oddProfileSineCoefficientAtBase boundary n

theorem oddProfileComplexCoefficientAtBase_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) :
    oddProfileComplexCoefficientAtBase boundary n =
      -(boundaryRadius n : ℂ) := by
  rw [oddProfileComplexCoefficientAtBase,
    oddProfileCosineCoefficientAtBase_of_odd hboundary n hn,
    oddProfileSineCoefficientAtBase_eq_zero hboundary n]
  simp

lemma angleToUnitAddCircle_add (s t : ℝ) :
    angleToUnitAddCircle (s + t) =
      angleToUnitAddCircle s + angleToUnitAddCircle t := by
  unfold angleToUnitAddCircle
  rw [← AddCircle.coe_add]
  congr 1
  ring

/-- Under the chosen circle equivalence, a radian angle is sent to the
usual complex exponential. -/
lemma unitAddCircleEquivComplexUnitCircle_angle (s : ℝ) :
    (unitAddCircleEquivComplexUnitCircle (angleToUnitAddCircle s) : ℂ) =
      Complex.exp ((s : ℂ) * Complex.I) := by
  change ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
      (angleToUnitAddCircle s) : Circle) : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply]
  unfold angleToUnitAddCircle
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

lemma unitAddCircle_dist_angle_add (s t : ℝ) :
    dist (angleToUnitAddCircle s) (angleToUnitAddCircle (s + t)) =
      dist (0 : UnitAddCircle) (angleToUnitAddCircle t) := by
  rw [dist_eq_norm, dist_eq_norm, angleToUnitAddCircle_add]
  congr 1
  abel

/-- The triangle-wave boundary identity centered at an arbitrary boundary
angle. -/
theorem oddDistanceProfile_at_boundary_angle
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (s : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) :
    oddDistanceProfile boundary (angleToUnitAddCircle (s + t))
        (boundary (angleToUnitAddCircle s)) = |t| - Real.pi / 2 := by
  rw [oddDistanceProfile_on_boundary hboundary,
    unitAddCircle_dist_angle_add,
    unitAddCircle_dist_zero_angleToUnitAddCircle ht]

/-- Cosine coordinate computed over the full period centered at the
boundary angle `s`. -/
def oddProfileCosineCoefficientOnCenteredPeriod
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (s : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in (s - Real.pi)..(s + Real.pi),
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (angleToUnitAddCircle s)) * Real.cos ((n : ℝ) * t)

/-- Sine coordinate computed over the full period centered at the
boundary angle `s`. -/
def oddProfileSineCoefficientOnCenteredPeriod
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (s : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in (s - Real.pi)..(s + Real.pi),
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (angleToUnitAddCircle s)) * Real.sin ((n : ℝ) * t)

private lemma centered_profile_cos_integral_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) :
    (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
      (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t) =
        -boundaryRadius n := by
  have h := oddProfileCosineCoefficientAtBase_of_odd hboundary n hn
  unfold oddProfileCosineCoefficientAtBase at h
  rw [show
    (∫ t in (-Real.pi)..Real.pi,
      oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (0 : UnitAddCircle)) * Real.cos ((n : ℝ) * t)) =
      ∫ t in (-Real.pi)..Real.pi,
        (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t) by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [oddDistanceProfile_at_boundary_base hboundary]
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht] at h
  exact h

private lemma centered_profile_sin_integral
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
      (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t) = 0 := by
  have h := oddProfileSineCoefficientAtBase_eq_zero hboundary n
  unfold oddProfileSineCoefficientAtBase at h
  rw [show
    (∫ t in (-Real.pi)..Real.pi,
      oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (0 : UnitAddCircle)) * Real.sin ((n : ℝ) * t)) =
      ∫ t in (-Real.pi)..Real.pi,
        (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t) by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [oddDistanceProfile_at_boundary_base hboundary]
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht] at h
  exact h

/-- Exact cosine boundary coordinate at every boundary angle. -/
theorem oddProfileCosineCoefficientOnCenteredPeriod_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileCosineCoefficientOnCenteredPeriod boundary n s =
      -boundaryRadius n * Real.cos ((n : ℝ) * s) := by
  let F : ℝ → ℝ := fun t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (angleToUnitAddCircle s)) * Real.cos ((n : ℝ) * t)
  have hshift :
      (∫ t in (s - Real.pi)..(s + Real.pi), F t) =
        ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * (t + s)) := by
    calc
      (∫ t in (s - Real.pi)..(s + Real.pi), F t) =
          ∫ t in (-Real.pi)..Real.pi, F (t + s) := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 1 <;> ring
      _ = ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * (t + s)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only [F]
        rw [show t + s = s + t by ring,
          oddDistanceProfile_at_boundary_angle hboundary s]
        rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  have hcos := centered_profile_cos_integral_of_odd hboundary n hn
  have hsin := centered_profile_sin_integral hboundary n
  have hrewrite :
      (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * (t + s))) =
        (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
            Real.cos ((n : ℝ) * s) -
        (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
            Real.sin ((n : ℝ) * s) := by
    have h₁ : IntervalIntegrable (fun t : ℝ ↦
        (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t) *
          Real.cos ((n : ℝ) * s)) volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h₂ : IntervalIntegrable (fun t : ℝ ↦
        (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t) *
          Real.sin ((n : ℝ) * s)) volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_sub h₁ h₂]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show (n : ℝ) * (t + s) = (n : ℝ) * t + (n : ℝ) * s by ring,
      Real.cos_add]
    ring
  unfold oddProfileCosineCoefficientOnCenteredPeriod
  change (1 / Real.pi) * ∫ t in (s - Real.pi)..(s + Real.pi), F t = _
  rw [hshift, hrewrite]
  calc
    (1 / Real.pi) *
        ((∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
              Real.cos ((n : ℝ) * s) -
          (∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
              Real.sin ((n : ℝ) * s)) =
        ((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
              Real.cos ((n : ℝ) * s) -
          ((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
              Real.sin ((n : ℝ) * s) := by ring
    _ = -boundaryRadius n * Real.cos ((n : ℝ) * s) := by rw [hcos, hsin]; ring

/-- Exact sine boundary coordinate at every boundary angle. -/
theorem oddProfileSineCoefficientOnCenteredPeriod_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileSineCoefficientOnCenteredPeriod boundary n s =
      -boundaryRadius n * Real.sin ((n : ℝ) * s) := by
  let F : ℝ → ℝ := fun t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t)
      (boundary (angleToUnitAddCircle s)) * Real.sin ((n : ℝ) * t)
  have hshift :
      (∫ t in (s - Real.pi)..(s + Real.pi), F t) =
        ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * (t + s)) := by
    calc
      (∫ t in (s - Real.pi)..(s + Real.pi), F t) =
          ∫ t in (-Real.pi)..Real.pi, F (t + s) := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 1 <;> ring
      _ = ∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * (t + s)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only [F]
        rw [show t + s = s + t by ring,
          oddDistanceProfile_at_boundary_angle hboundary s]
        rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
  have hcos := centered_profile_cos_integral_of_odd hboundary n hn
  have hsin := centered_profile_sin_integral hboundary n
  have hrewrite :
      (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * (t + s))) =
        (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
            Real.cos ((n : ℝ) * s) +
        (∫ t in (-Real.pi)..Real.pi,
          (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
            Real.sin ((n : ℝ) * s) := by
    have h₁ : IntervalIntegrable (fun t : ℝ ↦
        (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t) *
          Real.cos ((n : ℝ) * s)) volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h₂ : IntervalIntegrable (fun t : ℝ ↦
        (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t) *
          Real.sin ((n : ℝ) * s)) volume (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_add h₁ h₂]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [show (n : ℝ) * (t + s) = (n : ℝ) * t + (n : ℝ) * s by ring,
      Real.sin_add]
    ring
  unfold oddProfileSineCoefficientOnCenteredPeriod
  change (1 / Real.pi) * ∫ t in (s - Real.pi)..(s + Real.pi), F t = _
  rw [hshift, hrewrite]
  calc
    (1 / Real.pi) *
        ((∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
              Real.cos ((n : ℝ) * s) +
          (∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
              Real.sin ((n : ℝ) * s)) =
        ((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.sin ((n : ℝ) * t)) *
              Real.cos ((n : ℝ) * s) +
          ((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
            (|t| - Real.pi / 2) * Real.cos ((n : ℝ) * t)) *
              Real.sin ((n : ℝ) * s) := by ring
    _ = -boundaryRadius n * Real.sin ((n : ℝ) * s) := by rw [hcos, hsin]; ring

/-- The two centered-period coordinates assembled into the complex Fourier
coordinate used in the note. -/
def oddProfileComplexCoefficientOnCenteredPeriod
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (s : ℝ) : ℂ :=
  (oddProfileCosineCoefficientOnCenteredPeriod boundary n s : ℂ) +
    (oddProfileSineCoefficientOnCenteredPeriod boundary n s : ℂ) * Complex.I

/-- Exact boundary formula `zₙ(γ(s)) = -ρₙ exp(i n s)` derived directly
from the metric distance profile. -/
theorem oddProfileComplexCoefficientOnCenteredPeriod_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileComplexCoefficientOnCenteredPeriod boundary n s =
      -(boundaryRadius n : ℂ) *
        Complex.exp (((((n : ℝ) * s : ℝ) : ℂ) * Complex.I)) := by
  unfold oddProfileComplexCoefficientOnCenteredPeriod
  rw [oddProfileCosineCoefficientOnCenteredPeriod_of_odd
      hboundary n hn s,
    oddProfileSineCoefficientOnCenteredPeriod_of_odd
      hboundary n hn s,
    Complex.exp_mul_I]
  push_cast
  ring

lemma angleToUnitAddCircle_add_two_pi (t : ℝ) :
    angleToUnitAddCircle (t + 2 * Real.pi) = angleToUnitAddCircle t := by
  rw [angleToUnitAddCircle_add]
  have hperiod : angleToUnitAddCircle (2 * Real.pi) = 0 := by
    unfold angleToUnitAddCircle
    rw [show (2 * Real.pi : ℝ) / (2 * Real.pi) = 1 by
      field_simp [Real.pi_ne_zero]]
    norm_num
  rw [hperiod, add_zero]

private lemma odd_profile_cos_integrand_periodic
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (x : X) :
    Function.Periodic (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x *
        Real.cos ((n : ℝ) * t)) (2 * Real.pi) := by
  intro t
  dsimp only
  rw [angleToUnitAddCircle_add_two_pi]
  congr 1
  convert Real.cos_add_nat_mul_two_pi ((n : ℝ) * t) n using 1 <;> ring

private lemma odd_profile_sin_integrand_periodic
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (x : X) :
    Function.Periodic (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x *
        Real.sin ((n : ℝ) * t)) (2 * Real.pi) := by
  intro t
  dsimp only
  rw [angleToUnitAddCircle_add_two_pi]
  congr 1
  convert Real.sin_add_nat_mul_two_pi ((n : ℝ) * t) n using 1 <;> ring

/-- The fixed-period cosine Fourier coordinate of the odd distance profile. -/
def oddProfileCosineCoordinate
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (x : X) : ℝ :=
  (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
    oddDistanceProfile boundary (angleToUnitAddCircle t) x *
      Real.cos ((n : ℝ) * t)

/-- The fixed-period sine Fourier coordinate of the odd distance profile. -/
def oddProfileSineCoordinate
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (x : X) : ℝ :=
  (1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
    oddDistanceProfile boundary (angleToUnitAddCircle t) x *
      Real.sin ((n : ℝ) * t)

/-- The complex Fourier map `Fₙ=(Aₙ,Bₙ)` constructed from the metric odd
distance profile. -/
def oddProfileFourierMap
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (x : X) : ℂ :=
  (oddProfileCosineCoordinate boundary n x : ℂ) +
    (oddProfileSineCoordinate boundary n x : ℂ) * Complex.I

/-- An isometric circumference-`2π` boundary parametrization is
`2π`-Lipschitz in the normalized additive-circle metric. -/
theorem IsometricCircleBoundary.lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) :
    LipschitzWith ⟨2 * Real.pi, mul_nonneg (by norm_num) Real.pi_pos.le⟩
      boundary := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [hboundary]
  change 2 * Real.pi * dist s t ≤ 2 * Real.pi * dist s t
  exact le_rfl

theorem continuous_angleToUnitAddCircle : Continuous angleToUnitAddCircle := by
  unfold angleToUnitAddCircle
  fun_prop

theorem IsometricCircleBoundary.continuous_oddDistanceProfile_parameter
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    Continuous (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x) := by
  have hb : Continuous boundary := hboundary.lipschitzWith.continuous
  unfold oddDistanceProfile boundaryDistance
  have hangle : Continuous (fun t : ℝ ↦ angleToUnitAddCircle t) :=
    continuous_angleToUnitAddCircle
  have hfirst : Continuous (fun t : ℝ ↦
      dist x (boundary (angleToUnitAddCircle t))) :=
    continuous_const.dist (hb.comp hangle)
  have hsecond : Continuous (fun t : ℝ ↦
      dist x (boundary
        (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) :=
    continuous_const.dist (hb.comp (hangle.add continuous_const))
  exact (hfirst.sub hsecond).div_const 2

/-- Joint continuity of the distance profile in its angular parameter and
its filling variable.  This is the measurability input needed to apply
Fubini to Rademacher's theorem. -/
theorem IsometricCircleBoundary.continuous_oddDistanceProfile_uncurry
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) :
    Continuous (Function.uncurry (fun t : ℝ ↦ fun x : ℂ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x)) := by
  have hb : Continuous boundary := hboundary.lipschitzWith.continuous
  unfold Function.uncurry oddDistanceProfile boundaryDistance
  have hangle : Continuous (fun p : ℝ × ℂ ↦ angleToUnitAddCircle p.1) :=
    continuous_angleToUnitAddCircle.comp continuous_fst
  have hfirst : Continuous (fun p : ℝ × ℂ ↦
      dist p.2 (boundary (angleToUnitAddCircle p.1))) :=
    continuous_snd.dist (hb.comp hangle)
  have hsecond : Continuous (fun p : ℝ × ℂ ↦
      dist p.2 (boundary
        (angleToUnitAddCircle p.1 +
          ((1 / 2 : ℝ) : UnitAddCircle)))) :=
    continuous_snd.dist
      (hb.comp (hangle.add continuous_const))
  exact (hfirst.sub hsecond).div_const 2

theorem IsometricCircleBoundary.continuous_distanceSlack_parameter
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    Continuous (fun t : ℝ ↦
      distanceSlack boundary (angleToUnitAddCircle t) x) := by
  have hb : Continuous boundary := hboundary.lipschitzWith.continuous
  unfold distanceSlack boundaryDistance
  have hangle : Continuous (fun t : ℝ ↦ angleToUnitAddCircle t) :=
    continuous_angleToUnitAddCircle
  have hfirst : Continuous (fun t : ℝ ↦
      dist x (boundary (angleToUnitAddCircle t))) :=
    continuous_const.dist (hb.comp hangle)
  have hsecond : Continuous (fun t : ℝ ↦
      dist x (boundary
        (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) :=
    continuous_const.dist (hb.comp (hangle.add continuous_const))
  exact ((hfirst.add hsecond).sub continuous_const).div_const 2

/-- Joint continuity of the antipodal slack in its angular parameter and
its filling variable. -/
theorem IsometricCircleBoundary.continuous_distanceSlack_uncurry
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) :
    Continuous (Function.uncurry (fun t : ℝ ↦ fun x : ℂ ↦
      distanceSlack boundary (angleToUnitAddCircle t) x)) := by
  have hb : Continuous boundary := hboundary.lipschitzWith.continuous
  unfold Function.uncurry distanceSlack boundaryDistance
  have hangle : Continuous (fun p : ℝ × ℂ ↦ angleToUnitAddCircle p.1) :=
    continuous_angleToUnitAddCircle.comp continuous_fst
  have hfirst : Continuous (fun p : ℝ × ℂ ↦
      dist p.2 (boundary (angleToUnitAddCircle p.1))) :=
    continuous_snd.dist (hb.comp hangle)
  have hsecond : Continuous (fun p : ℝ × ℂ ↦
      dist p.2 (boundary
        (angleToUnitAddCircle p.1 +
          ((1 / 2 : ℝ) : UnitAddCircle)))) :=
    continuous_snd.dist
      (hb.comp (hangle.add continuous_const))
  exact ((hfirst.add hsecond).sub continuous_const).div_const 2

/-- For almost every filling point, almost every angular distance profile
is differentiable there.  This is the Fubini/Rademacher step in the weak
differentiation part of Lemma 5.4. -/
theorem ae_ae_differentiableAt_oddDistanceProfile
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) :
    ∀ᵐ x : ℂ ∂volume,
      ∀ᵐ t : ℝ ∂volume.restrict (Set.uIoc (-Real.pi) Real.pi),
        DifferentiableAt ℝ
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) x := by
  let P : ℝ → ℂ → Prop := fun t x ↦ DifferentiableAt ℝ
    (oddDistanceProfile boundary (angleToUnitAddCircle t)) x
  have hP : MeasurableSet {p : ℝ × ℂ | P p.1 p.2} :=
    measurableSet_of_differentiableAt_with_param ℝ
      hboundary.continuous_oddDistanceProfile_uncurry
  have ht : ∀ᵐ t : ℝ ∂volume, ∀ᵐ x : ℂ ∂volume, P t x := by
    apply ae_of_all
    intro t
    exact (oddDistanceProfile_lipschitzWith boundary
      (angleToUnitAddCircle t)).ae_differentiableAt
  have hx : ∀ᵐ x : ℂ ∂volume, ∀ᵐ t : ℝ ∂volume, P t x :=
    ((MeasureTheory.Measure.ae_ae_comm
      (μ := volume) (ν := volume) hP).mp ht)
  filter_upwards [hx] with x hx'
  exact ae_restrict_of_ae hx'

/-- The measurable weak derivative field of the angular distance
profiles at a fixed filling point.  At nondifferentiability points
mathlib's `fderiv` is zero, which is harmless for all almost-everywhere
statements below. -/
def oddProfileDerivativeField
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) : ℂ →L[ℝ] ℝ :=
  fderiv ℝ (oddDistanceProfile boundary (angleToUnitAddCircle t)) x

theorem measurable_oddProfileDerivativeField
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (x : ℂ) :
    Measurable (oddProfileDerivativeField boundary x) := by
  let F : ℝ → ℂ → ℝ := fun t y ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) y
  have hF : Continuous F.uncurry :=
    hboundary.continuous_oddDistanceProfile_uncurry
  have hjoint : Measurable (fun p : ℝ × ℂ ↦
      fderiv ℝ (F p.1) p.2) :=
    measurable_fderiv_with_param ℝ hF
  have hcomp := hjoint.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ ↦ x)))
  simpa only [F, oddProfileDerivativeField] using hcomp

/-- The weak derivative of every angular profile has operator norm at
most one, including at the exceptional points where `fderiv` is zero. -/
theorem norm_oddProfileDerivativeField_le_one
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) :
    ‖oddProfileDerivativeField boundary x t‖ ≤ 1 := by
  unfold oddProfileDerivativeField
  simpa only [NNReal.coe_one] using
    norm_fderiv_le_of_lipschitz ℝ
      (oddDistanceProfile_lipschitzWith boundary
        (angleToUnitAddCircle t))

/-- Exact two-dimensional consequence of the preceding operator bound:
the squared directional derivatives along `(1,I)` have total at most
one. -/
theorem oddProfileDerivativeField_basis_energy_le_one
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) :
    (oddProfileDerivativeField boundary x t 1) ^ 2 +
      (oddProfileDerivativeField boundary x t Complex.I) ^ 2 ≤ 1 :=
  realCovector_basis_energy_le_one _
    (norm_oddProfileDerivativeField_le_one boundary x t)

/-- The measurable weak derivative field of the angular slack profiles at a
fixed filling point. -/
def distanceSlackDerivativeField
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) : ℂ →L[ℝ] ℝ :=
  fderiv ℝ (distanceSlack boundary (angleToUnitAddCircle t)) x

theorem measurable_distanceSlackDerivativeField
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (x : ℂ) :
    Measurable (distanceSlackDerivativeField boundary x) := by
  let F : ℝ → ℂ → ℝ := fun t y ↦
    distanceSlack boundary (angleToUnitAddCircle t) y
  have hF : Continuous F.uncurry :=
    hboundary.continuous_distanceSlack_uncurry
  have hjoint : Measurable (fun p : ℝ × ℂ ↦
      fderiv ℝ (F p.1) p.2) :=
    measurable_fderiv_with_param ℝ hF
  have hcomp := hjoint.comp
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ ↦ x)))
  simpa only [F, distanceSlackDerivativeField] using hcomp

/-- The weak derivative of every angular slack profile has operator norm at
most one, including at the exceptional points where `fderiv` is zero. -/
theorem norm_distanceSlackDerivativeField_le_one
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) :
    ‖distanceSlackDerivativeField boundary x t‖ ≤ 1 := by
  unfold distanceSlackDerivativeField
  simpa only [NNReal.coe_one] using
    norm_fderiv_le_of_lipschitz ℝ
      (distanceSlack_lipschitzWith boundary
        (angleToUnitAddCircle t))

/-- Exact two-dimensional consequence of the preceding operator bound for
antipodal slack. -/
theorem distanceSlackDerivativeField_basis_energy_le_one
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ) :
    (distanceSlackDerivativeField boundary x t 1) ^ 2 +
      (distanceSlackDerivativeField boundary x t Complex.I) ^ 2 ≤ 1 :=
  realCovector_basis_energy_le_one _
    (norm_distanceSlackDerivativeField_le_one boundary x t)

private theorem differentiableAt_boundaryDistance_of_ne
    (boundary : UnitAddCircle → ℂ) (θ : UnitAddCircle) {x : ℂ}
    (hx : x ≠ boundary θ) :
    DifferentiableAt ℝ (boundaryDistance boundary θ) x := by
  have hsub : DifferentiableAt ℝ (fun y : ℂ ↦ y - boundary θ) x :=
    differentiableAt_id.sub_const (boundary θ)
  unfold boundaryDistance
  simpa [dist_eq_norm] using hsub.norm ℝ (sub_ne_zero.mpr hx)

private theorem norm_fderiv_boundaryDistance_eq_one_of_ne
    (boundary : UnitAddCircle → ℂ) (θ : UnitAddCircle) {x : ℂ}
    (hx : x ≠ boundary θ) :
    ‖fderiv ℝ (boundaryDistance boundary θ) x‖ = 1 := by
  have hsub : HasFDerivAt (fun y : ℂ ↦ y - boundary θ) (1 : ℂ →L[ℝ] ℂ) x := by
    simpa using (hasFDerivAt_id x).sub_const (boundary θ)
  have hnormDiff : DifferentiableAt ℝ (fun z : ℂ ↦ ‖z‖) (x - boundary θ) := by
    exact differentiableAt_id.norm ℝ (sub_ne_zero.mpr hx)
  have hnorm : HasFDerivAt (fun z : ℂ ↦ ‖z‖)
      (fderiv ℝ (fun z : ℂ ↦ ‖z‖) (x - boundary θ)) (x - boundary θ) :=
    hnormDiff.hasFDerivAt
  have hcomp : HasFDerivAt (boundaryDistance boundary θ)
      (fderiv ℝ (fun z : ℂ ↦ ‖z‖) (x - boundary θ)) x := by
    unfold boundaryDistance
    simpa [dist_eq_norm] using hnorm.comp x hsub
  rw [hcomp.fderiv]
  exact norm_fderiv_norm (E := ℂ) hnormDiff

private theorem oddProfileDerivativeField_eq_half_sub_boundaryDistance_of_ne
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ)
    (hxt : x ≠ boundary (angleToUnitAddCircle t))
    (hxhalf : x ≠ boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) :
    oddProfileDerivativeField boundary x t =
      (1 / 2 : ℝ) •
        (fderiv ℝ (boundaryDistance boundary (angleToUnitAddCircle t)) x -
          fderiv ℝ (boundaryDistance boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) x) := by
  have h1 :=
    (differentiableAt_boundaryDistance_of_ne boundary
      (angleToUnitAddCircle t) hxt).hasFDerivAt
  have h2 :=
    (differentiableAt_boundaryDistance_of_ne boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))
      hxhalf).hasFDerivAt
  have hderiv :
      HasFDerivAt
        (fun y : ℂ ↦ oddDistanceProfile boundary (angleToUnitAddCircle t) y)
        ((1 / 2 : ℝ) •
          (fderiv ℝ (boundaryDistance boundary (angleToUnitAddCircle t)) x -
            fderiv ℝ (boundaryDistance boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) x)) x := by
    simpa [oddDistanceProfile, sub_eq_add_neg, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
      ((h1.sub h2).const_mul (1 / 2 : ℝ))
  unfold oddProfileDerivativeField
  exact hderiv.fderiv

private theorem distanceSlackDerivativeField_eq_half_add_boundaryDistance_of_ne
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ)
    (hxt : x ≠ boundary (angleToUnitAddCircle t))
    (hxhalf : x ≠ boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) :
    distanceSlackDerivativeField boundary x t =
      (1 / 2 : ℝ) •
        (fderiv ℝ (boundaryDistance boundary (angleToUnitAddCircle t)) x +
          fderiv ℝ (boundaryDistance boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) x) := by
  have h1 :=
    (differentiableAt_boundaryDistance_of_ne boundary
      (angleToUnitAddCircle t) hxt).hasFDerivAt
  have h2 :=
    (differentiableAt_boundaryDistance_of_ne boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))
      hxhalf).hasFDerivAt
  have hderiv :
      HasFDerivAt
        (fun y : ℂ ↦ distanceSlack boundary (angleToUnitAddCircle t) y)
        ((1 / 2 : ℝ) •
          (fderiv ℝ (boundaryDistance boundary (angleToUnitAddCircle t)) x +
            fderiv ℝ (boundaryDistance boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) x)) x := by
    simpa [distanceSlack, sub_eq_add_neg, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (((h1.add h2).const_add (-Real.pi)).const_mul (1 / 2 : ℝ))
  unfold distanceSlackDerivativeField
  exact hderiv.fderiv

private theorem oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one_of_ne
    (boundary : UnitAddCircle → ℂ) (x : ℂ) (t : ℝ)
    (hxt : x ≠ boundary (angleToUnitAddCircle t))
    (hxhalf : x ≠ boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) :
    ((oddProfileDerivativeField boundary x t 1) ^ 2 +
        (oddProfileDerivativeField boundary x t Complex.I) ^ 2) +
      ((distanceSlackDerivativeField boundary x t 1) ^ 2 +
        (distanceSlackDerivativeField boundary x t Complex.I) ^ 2) = 1 := by
  let θ : UnitAddCircle := angleToUnitAddCircle t
  let D₁ : ℂ →L[ℝ] ℝ := fderiv ℝ (boundaryDistance boundary θ) x
  let D₂ : ℂ →L[ℝ] ℝ :=
    fderiv ℝ (boundaryDistance boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))) x
  have hodd :=
    oddProfileDerivativeField_eq_half_sub_boundaryDistance_of_ne
      boundary x t hxt hxhalf
  have hslack :=
    distanceSlackDerivativeField_eq_half_add_boundaryDistance_of_ne
      boundary x t hxt hxhalf
  have hnorm1 : ‖D₁‖ = 1 := by
    simpa [D₁, θ] using
      norm_fderiv_boundaryDistance_eq_one_of_ne boundary θ hxt
  have hnorm2 : ‖D₂‖ = 1 := by
    simpa [D₂, θ] using
      norm_fderiv_boundaryDistance_eq_one_of_ne boundary
        (θ + ((1 / 2 : ℝ) : UnitAddCircle)) hxhalf
  rw [hodd, hslack]
  have hpar :
      ((((1 / 2 : ℝ) • (D₁ - D₂)) 1) ^ 2 +
          (((1 / 2 : ℝ) • (D₁ - D₂)) Complex.I) ^ 2) +
        ((((1 / 2 : ℝ) • (D₁ + D₂)) 1) ^ 2 +
          (((1 / 2 : ℝ) • (D₁ + D₂)) Complex.I) ^ 2) =
      (((D₁ 1) ^ 2 + (D₁ Complex.I) ^ 2) +
          ((D₂ 1) ^ 2 + (D₂ Complex.I) ^ 2)) / 2 := by
    simp [ContinuousLinearMap.smul_apply, D₁, D₂]
    ring
  rw [hpar, realCovector_apply_one_sq_add_apply_I_sq,
    realCovector_apply_one_sq_add_apply_I_sq, hnorm1, hnorm2]
  ring

/-- Away from the boundary curve, the odd profile and the antipodal slack
satisfy the exact planar parallelogram identity at the derivative level. -/
theorem oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one_of_not_mem_range
    {boundary : UnitAddCircle → ℂ} {x : ℂ}
    (hx : x ∉ Set.range boundary) (t : ℝ) :
    ((oddProfileDerivativeField boundary x t 1) ^ 2 +
        (oddProfileDerivativeField boundary x t Complex.I) ^ 2) +
      ((distanceSlackDerivativeField boundary x t 1) ^ 2 +
        (distanceSlackDerivativeField boundary x t Complex.I) ^ 2) = 1 := by
  have hxt : x ≠ boundary (angleToUnitAddCircle t) := by
    intro h
    exact hx ⟨angleToUnitAddCircle t, h.symm⟩
  have hxhalf : x ≠ boundary
      (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)) := by
    intro h
    exact hx ⟨angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle), h.symm⟩
  exact oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one_of_ne
    boundary x t hxt hxhalf

/-- Every unit directional component of the profile derivative is `L²`
on the angular period. -/
theorem memLp_oddProfileDerivativeField_apply
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (x v : ℂ) (hv : ‖v‖ ≤ 1) :
    MemLp (fun t ↦
      ((oddProfileDerivativeField boundary x t v : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
  have hDmeas : Measurable (oddProfileDerivativeField boundary x) :=
    measurable_oddProfileDerivativeField hboundary x
  have hreal : Measurable (fun t ↦
      oddProfileDerivativeField boundary x t v) :=
    (ContinuousLinearMap.measurable_apply v).comp hDmeas
  apply MemLp.of_bound
    (Complex.continuous_ofReal.measurable.comp hreal).aestronglyMeasurable 1
  apply ae_of_all
  intro t
  calc
    ‖((oddProfileDerivativeField boundary x t v : ℝ) : ℂ)‖ =
        ‖oddProfileDerivativeField boundary x t v‖ := by simp
    _ ≤ ‖oddProfileDerivativeField boundary x t‖ * ‖v‖ :=
      (oddProfileDerivativeField boundary x t).le_opNorm v
    _ ≤ 1 * 1 := mul_le_mul
      (norm_oddProfileDerivativeField_le_one boundary x t) hv
      (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Every unit directional component of the slack derivative is `L²`
on the angular period. -/
theorem memLp_distanceSlackDerivativeField_apply
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (x v : ℂ) (hv : ‖v‖ ≤ 1) :
    MemLp (fun t ↦
      ((distanceSlackDerivativeField boundary x t v : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
  have hDmeas : Measurable (distanceSlackDerivativeField boundary x) :=
    measurable_distanceSlackDerivativeField hboundary x
  have hreal : Measurable (fun t ↦
      distanceSlackDerivativeField boundary x t v) :=
    (ContinuousLinearMap.measurable_apply v).comp hDmeas
  apply MemLp.of_bound
    (Complex.continuous_ofReal.measurable.comp hreal).aestronglyMeasurable 1
  apply ae_of_all
  intro t
  calc
    ‖((distanceSlackDerivativeField boundary x t v : ℝ) : ℂ)‖ =
        ‖distanceSlackDerivativeField boundary x t v‖ := by simp
    _ ≤ ‖distanceSlackDerivativeField boundary x t‖ * ‖v‖ :=
      (distanceSlackDerivativeField boundary x t).le_opNorm v
    _ ≤ 1 * 1 := mul_le_mul
      (norm_distanceSlackDerivativeField_le_one boundary x t) hv
      (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Weak differentiation through one weighted angular integral.  The
assumptions are exactly those supplied almost everywhere by the preceding
Fubini theorem; domination uses the global one-Lipschitz estimate for each
distance profile. -/
theorem hasFDerivAt_oddProfile_weightedIntegral
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (x : ℂ) (w : ℝ → ℝ) (hw : Continuous w)
    (hwabs : ∀ t, |w t| ≤ 1)
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      DifferentiableAt ℝ
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) :
    HasFDerivAt
      (fun y : ℂ ↦ ∫ t in (-Real.pi)..Real.pi,
        oddDistanceProfile boundary (angleToUnitAddCircle t) y * w t)
      (∫ t in (-Real.pi)..Real.pi,
        w t • oddProfileDerivativeField boundary x t) x := by
  let F : ℂ → ℝ → ℝ := fun y t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) y * w t
  let F' : ℝ → ℂ →L[ℝ] ℝ := fun t ↦
    w t • oddProfileDerivativeField boundary x t
  have hFmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (F y)
        (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    filter_upwards [] with y
    exact ((hboundary.continuous_oddDistanceProfile_parameter y).mul hw)
      |>.aestronglyMeasurable.restrict
  have hFint : IntervalIntegrable (F x) volume
      (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    exact (hboundary.continuous_oddDistanceProfile_parameter x).mul hw
  have hF'meas : AEStronglyMeasurable F'
      (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
    exact (hw.measurable.smul
      (measurable_oddProfileDerivativeField hboundary x))
      |>.aestronglyMeasurable.restrict
  have hlip : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      LipschitzOnWith (Real.nnabs (1 : ℝ)) (F · t) Set.univ := by
    apply ae_of_all
    intro t
    norm_num [Real.nnabs]
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [Real.dist_eq]
    change
      |oddDistanceProfile boundary (angleToUnitAddCircle t) y * w t -
        oddDistanceProfile boundary (angleToUnitAddCircle t) z * w t| ≤
        1 * dist y z
    rw [← sub_mul, abs_mul, one_mul]
    have hp := (oddDistanceProfile_lipschitzWith boundary
      (angleToUnitAddCircle t)).dist_le_mul y z
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hp
    exact (mul_le_mul hp (hwabs t) (abs_nonneg _) (dist_nonneg)).trans_eq
      (mul_one _)
  have hbound : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume
      (-Real.pi) Real.pi := by
    exact (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ)))
      |>.intervalIntegrable _ _
  have hdiff' : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      HasFDerivAt (F · t) (F' t) x := by
    filter_upwards [hdiff] with t ht
    exact ht.hasFDerivAt.mul_const (w t)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip_interval
    (x₀ := x) (s := Set.univ) (F := F) (F' := F')
    (bound := fun _ : ℝ ↦ 1) Filter.univ_mem hFmeas hFint hF'meas
    hlip hbound hdiff').2

/-- The weak derivative of the cosine coordinate at a good filling
point. -/
def oddProfileCosineDerivative
    (boundary : UnitAddCircle → ℂ) (n : ℕ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  (1 / Real.pi) • ∫ t in (-Real.pi)..Real.pi,
    Real.cos ((n : ℝ) * t) • oddProfileDerivativeField boundary x t

/-- The weak derivative of the sine coordinate at a good filling point. -/
def oddProfileSineDerivative
    (boundary : UnitAddCircle → ℂ) (n : ℕ) (x : ℂ) : ℂ →L[ℝ] ℝ :=
  (1 / Real.pi) • ∫ t in (-Real.pi)..Real.pi,
    Real.sin ((n : ℝ) * t) • oddProfileDerivativeField boundary x t

/-- The two real weak derivatives assembled as a real-linear complex
derivative. -/
def oddProfileFourierDerivative
    (boundary : UnitAddCircle → ℂ) (n : ℕ) (x : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (oddProfileCosineDerivative boundary n x) +
    Complex.I • Complex.ofRealCLM.comp
      (oddProfileSineDerivative boundary n x)

theorem hasFDerivAt_oddProfileCosineCoordinate
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x : ℂ)
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      DifferentiableAt ℝ
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) :
    HasFDerivAt (oddProfileCosineCoordinate boundary n)
      (oddProfileCosineDerivative boundary n x) x := by
  have h := hasFDerivAt_oddProfile_weightedIntegral hboundary x
    (fun t ↦ Real.cos ((n : ℝ) * t)) (by fun_prop)
    (fun t ↦ abs_cos_le_one _) hdiff
  simpa only [oddProfileCosineCoordinate, oddProfileCosineDerivative] using
    h.const_mul (1 / Real.pi)

theorem hasFDerivAt_oddProfileSineCoordinate
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x : ℂ)
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      DifferentiableAt ℝ
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) :
    HasFDerivAt (oddProfileSineCoordinate boundary n)
      (oddProfileSineDerivative boundary n x) x := by
  have h := hasFDerivAt_oddProfile_weightedIntegral hboundary x
    (fun t ↦ Real.sin ((n : ℝ) * t)) (by fun_prop)
    (fun t ↦ abs_sin_le_one _) hdiff
  simpa only [oddProfileSineCoordinate, oddProfileSineDerivative] using
    h.const_mul (1 / Real.pi)

/-- At every Fubini-good point the explicit weak derivative above is the
Fréchet derivative of the genuine complex distance-profile Fourier map. -/
theorem hasFDerivAt_oddProfileFourierMap
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x : ℂ)
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.uIoc (-Real.pi) Real.pi),
      DifferentiableAt ℝ
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) :
    HasFDerivAt (oddProfileFourierMap boundary n)
      (oddProfileFourierDerivative boundary n x) x := by
  have hcos := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hasFDerivAt_oddProfileCosineCoordinate hboundary n x hdiff))
  have hsin := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hasFDerivAt_oddProfileSineCoordinate hboundary n x hdiff))
  simpa only [oddProfileFourierMap, oddProfileFourierDerivative] using
    hcos.add (hsin.mul_const Complex.I)

private lemma neg_pi_lt_pi : -Real.pi < Real.pi := by
  linarith [Real.pi_pos]

private theorem intervalIntegrable_oddProfileDerivativeField
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (x : ℂ) :
    IntervalIntegrable (oddProfileDerivativeField boundary x)
      volume (-Real.pi) Real.pi := by
  apply IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ ↦ (1 : ℝ))
  · exact
      (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).intervalIntegrable _ _
  · exact (measurable_oddProfileDerivativeField hboundary x).aestronglyMeasurable
  · apply ae_of_all
    intro t
    exact norm_oddProfileDerivativeField_le_one boundary x t

private theorem intervalIntegrable_oddProfileDerivativeField_apply
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (x v : ℂ) (hv : ‖v‖ ≤ 1) :
    IntervalIntegrable
      (fun t ↦ oddProfileDerivativeField boundary x t v)
      volume (-Real.pi) Real.pi := by
  apply IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ ↦ (1 : ℝ))
  · exact
      (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).intervalIntegrable _ _
  · exact
      ((ContinuousLinearMap.measurable_apply v).comp
        (measurable_oddProfileDerivativeField hboundary x)).aestronglyMeasurable
  · apply ae_of_all
    intro t
    calc
      ‖oddProfileDerivativeField boundary x t v‖ ≤
          ‖oddProfileDerivativeField boundary x t‖ * ‖v‖ :=
        (oddProfileDerivativeField boundary x t).le_opNorm v
      _ ≤ 1 * 1 := mul_le_mul
        (norm_oddProfileDerivativeField_le_one boundary x t) hv
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring

private theorem oddProfileCosineDerivative_apply
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x v : ℂ) :
    oddProfileCosineDerivative boundary n x v =
      (1 / Real.pi) *
        ∫ t in (-Real.pi)..Real.pi,
          oddProfileDerivativeField boundary x t v *
            Real.cos ((n : ℝ) * t) := by
  unfold oddProfileCosineDerivative
  have hD := intervalIntegrable_oddProfileDerivativeField hboundary x
  have hcos : IntervalIntegrable
      (fun t ↦ Real.cos ((n : ℝ) * t) • oddProfileDerivativeField boundary x t)
      volume (-Real.pi) Real.pi := by
    exact hD.continuousOn_smul (by
      simpa [Set.uIcc_of_le neg_pi_lt_pi.le] using
        (show ContinuousOn (fun t : ℝ ↦ Real.cos ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply hcos v]
  apply congrArg
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [] with t
  simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem oddProfileSineDerivative_apply
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x v : ℂ) :
    oddProfileSineDerivative boundary n x v =
      (1 / Real.pi) *
        ∫ t in (-Real.pi)..Real.pi,
          oddProfileDerivativeField boundary x t v *
            Real.sin ((n : ℝ) * t) := by
  unfold oddProfileSineDerivative
  have hD := intervalIntegrable_oddProfileDerivativeField hboundary x
  have hsin : IntervalIntegrable
      (fun t ↦ Real.sin ((n : ℝ) * t) • oddProfileDerivativeField boundary x t)
      volume (-Real.pi) Real.pi := by
    exact hD.continuousOn_smul (by
      simpa [Set.uIcc_of_le neg_pi_lt_pi.le] using
        (show ContinuousOn (fun t : ℝ ↦ Real.sin ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply hsin v]
  apply congrArg
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [] with t
  simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

private theorem oddProfileFourierDerivative_apply_eq_two_mul_fourierCoeffOn
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (x v : ℂ) (hv : ‖v‖ ≤ 1) :
    oddProfileFourierDerivative boundary n x v =
      2 * fourierCoeffOn neg_pi_lt_pi
        (fun t ↦ ((oddProfileDerivativeField boundary x t v : ℝ) : ℂ))
        (-(n : ℤ)) := by
  have hInt : IntervalIntegrable
      (fun t ↦ ((oddProfileDerivativeField boundary x t v : ℝ) : ℂ))
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le]
    simpa [IntegrableOn] using
      ((memLp_oddProfileDerivativeField_apply hboundary x v hv).integrable
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) (by norm_num))
  have hcoeff := GromovFilling.two_mul_fourierCoeffOn_neg_eq_cos_add_sin neg_pi_lt_pi hInt n
  unfold oddProfileFourierDerivative
  rw [hcoeff]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.smul_apply]
  rw [oddProfileCosineDerivative_apply hboundary n x v,
    oddProfileSineDerivative_apply hboundary n x v]
  have hcosInt :
      IntervalIntegrable
        (fun t ↦ oddProfileDerivativeField boundary x t v * Real.cos ((n : ℝ) * t))
        volume (-Real.pi) Real.pi := by
    exact (intervalIntegrable_oddProfileDerivativeField_apply hboundary x v hv).mul_continuousOn (by
      simpa [Set.uIcc_of_le neg_pi_lt_pi.le] using
        (show ContinuousOn (fun t : ℝ ↦ Real.cos ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hsinInt :
      IntervalIntegrable
        (fun t ↦ oddProfileDerivativeField boundary x t v * Real.sin ((n : ℝ) * t))
        volume (-Real.pi) Real.pi := by
    exact (intervalIntegrable_oddProfileDerivativeField_apply hboundary x v hv).mul_continuousOn (by
      simpa [Set.uIcc_of_le neg_pi_lt_pi.le] using
        (show ContinuousOn (fun t : ℝ ↦ Real.sin ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hcosCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((oddProfileDerivativeField boundary x t v *
              Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            oddProfileDerivativeField boundary x t v *
              Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using
      (Complex.ofRealCLM.intervalIntegral_comp_comm
        (f := fun t ↦ oddProfileDerivativeField boundary x t v *
          Real.cos ((n : ℝ) * t)) hcosInt)
  have hsinCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((oddProfileDerivativeField boundary x t v *
              Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            oddProfileDerivativeField boundary x t v *
              Real.sin ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using
      (Complex.ofRealCLM.intervalIntegral_comp_comm
        (f := fun t ↦ oddProfileDerivativeField boundary x t v *
          Real.sin ((n : ℝ) * t)) hsinInt)
  rw [smul_eq_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ← hcosCast, ← hsinCast]
  ring

private theorem angleToUnitAddCircle_eq_iff_of_mem_Ioc {s t : ℝ}
    (hs : s ∈ Set.Ioc (-Real.pi) Real.pi)
    (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) :
    angleToUnitAddCircle s = angleToUnitAddCircle t ↔ s = t := by
  have htwoPi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hs' : s / (2 * Real.pi) ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor
    · rw [lt_div_iff₀ htwoPi]
      nlinarith [hs.1, Real.pi_pos]
    · rw [div_le_iff₀ htwoPi]
      nlinarith [hs.2, Real.pi_pos]
  have ht' : t / (2 * Real.pi) ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by
    constructor
    · rw [lt_div_iff₀ htwoPi]
      nlinarith [ht.1, Real.pi_pos]
    · rw [div_le_iff₀ htwoPi]
      nlinarith [ht.2, Real.pi_pos]
  constructor
  · intro hst
    have hsub :
        (⟨s / (2 * Real.pi), hs'⟩ : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) =
          ⟨t / (2 * Real.pi), ht'⟩ := by
      have h' :
          (AddCircle.equivIoc 1 (-(1 / 2 : ℝ))) (((s / (2 * Real.pi) : ℝ) : UnitAddCircle)) =
            (AddCircle.equivIoc 1 (-(1 / 2 : ℝ))) (((t / (2 * Real.pi) : ℝ) : UnitAddCircle)) := by
        simpa [angleToUnitAddCircle] using
          congrArg (AddCircle.equivIoc 1 (-(1 / 2 : ℝ))) hst
      rwa [AddCircle.equivIoc_coe_eq hs', AddCircle.equivIoc_coe_eq ht'] at h'
    have hdiv : s / (2 * Real.pi) = t / (2 * Real.pi) := congrArg Subtype.val hsub
    have hmul := congrArg (fun u : ℝ ↦ u * (2 * Real.pi)) hdiv
    field_simp [Real.pi_ne_zero] at hmul
    exact hmul
  · intro hst
    simp [hst]

private theorem exists_angleToUnitAddCircle_eq_mem_Ioc (θ : UnitAddCircle) :
    ∃ t ∈ Set.Ioc (-Real.pi) Real.pi, angleToUnitAddCircle t = θ := by
  let u : Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    AddCircle.equivIoc 1 (-(1 / 2 : ℝ)) θ
  refine ⟨2 * Real.pi * u.1, ?_, ?_⟩
  · constructor
    · nlinarith [u.2.1, Real.pi_pos]
    · nlinarith [u.2.2, Real.pi_pos]
  · have hu := (AddCircle.equivIoc 1 (-(1 / 2 : ℝ))).symm_apply_apply θ
    change (((↑u : ℝ) : UnitAddCircle) = θ) at hu
    unfold angleToUnitAddCircle
    rw [show (2 * Real.pi * u.1 : ℝ) / (2 * Real.pi) = u.1 by
      field_simp [Real.pi_ne_zero]]
    exact hu

private theorem ae_oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (x : ℂ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
      ((oddProfileDerivativeField boundary x t 1) ^ 2 +
          (oddProfileDerivativeField boundary x t Complex.I) ^ 2) +
        ((distanceSlackDerivativeField boundary x t 1) ^ 2 +
          (distanceSlackDerivativeField boundary x t Complex.I) ^ 2) = 1 := by
  have hboundary_injective : Function.Injective boundary := by
    intro s t hst
    have hdist : dist (boundary s) (boundary t) = 2 * Real.pi * dist s t :=
      hboundary s t
    rw [hst, dist_self] at hdist
    have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
    have hst' : dist s t = 0 := by
      have hst_nonneg : 0 ≤ dist s t := dist_nonneg
      nlinarith [hst_nonneg, hpi, hdist]
    exact dist_eq_zero.mp hst'
  by_cases hx : x ∈ Set.range boundary
  · rcases hx with ⟨θ, rfl⟩
    obtain ⟨t₀, ht₀mem, ht₀eq⟩ := exists_angleToUnitAddCircle_eq_mem_Ioc θ
    obtain ⟨t₁, ht₁mem, ht₁eq⟩ :=
      exists_angleToUnitAddCircle_eq_mem_Ioc
        (θ - ((1 / 2 : ℝ) : UnitAddCircle))
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      Measure.ae_ne (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) t₀,
      Measure.ae_ne (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) t₁] with t htmem htne₀ htne₁
    have hxt : boundary θ ≠ boundary (angleToUnitAddCircle t) := by
      intro h
      have hangle : angleToUnitAddCircle t = θ :=
        hboundary_injective h.symm
      have htt₀ : t = t₀ :=
        (angleToUnitAddCircle_eq_iff_of_mem_Ioc htmem ht₀mem).mp (hangle.trans ht₀eq.symm)
      exact htne₀ htt₀
    have hxhalf : boundary θ ≠ boundary
        (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)) := by
      intro h
      have hangle : angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle) = θ :=
        hboundary_injective h.symm
      have hangle' : angleToUnitAddCircle t = θ - ((1 / 2 : ℝ) : UnitAddCircle) := by
        have hshift := congrArg
          (fun z : UnitAddCircle ↦ z - ((1 / 2 : ℝ) : UnitAddCircle)) hangle
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
      have htt₁ : t = t₁ :=
        (angleToUnitAddCircle_eq_iff_of_mem_Ioc htmem ht₁mem).mp (hangle'.trans ht₁eq.symm)
      exact htne₁ htt₁
    simpa using
      oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one_of_ne
        boundary (boundary θ) t hxt hxhalf
  · exact ae_restrict_of_ae (Filter.Eventually.of_forall fun t ↦
      oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one_of_not_mem_range hx t)

private theorem oddProfileDerivativeField_energy_budget_with_slack
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (x : ℂ) :
    2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2) +
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) +
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2) +
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) = 2 := by
  have h1L2 := memLp_oddProfileDerivativeField_apply hboundary x 1 (by simp)
  have hIL2 := memLp_oddProfileDerivativeField_apply hboundary x Complex.I (by simp)
  have hs1L2 := memLp_distanceSlackDerivativeField_apply hboundary x 1 (by simp)
  have hsIL2 := memLp_distanceSlackDerivativeField_apply hboundary x Complex.I (by simp)
  have hpow1 : IntervalIntegrable
      (fun t ↦ ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow' (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) h1L2)
  have hpowI : IntervalIntegrable
      (fun t ↦ ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow' (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hIL2)
  have hspow1 : IntervalIntegrable
      (fun t ↦ ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow' (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hs1L2)
  have hspowI : IntervalIntegrable
      (fun t ↦ ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow' (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hsIL2)
  have hintEq :
      (∫ t in (-Real.pi)..Real.pi,
          (‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2 +
            ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) +
          (‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2 +
            ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2)) =
        ∫ t in (-Real.pi)..Real.pi, (1 : ℝ) := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [Set.uIoc_of_le neg_pi_lt_pi.le]
    filter_upwards [ae_oddProfileDerivativeField_add_distanceSlackDerivativeField_basis_energy_eq_one
      hboundary x] with t ht
    simpa [Complex.norm_real, sq_abs] using ht
  have haddOdd :
      (∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2 +
            ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) =
        (∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2) +
        ∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2 := by
    rw [intervalIntegral.integral_add hpow1 hpowI]
  have haddSlack :
      (∫ t in (-Real.pi)..Real.pi,
          ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2 +
            ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) =
        (∫ t in (-Real.pi)..Real.pi,
          ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2) +
        ∫ t in (-Real.pi)..Real.pi,
          ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2 := by
    rw [intervalIntegral.integral_add hspow1 hspowI]
  have hlength : ∫ t in (-Real.pi)..Real.pi, (1 : ℝ) = Real.pi - -Real.pi := by
    have hpi_nonneg : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    simp [intervalIntegral.integral_of_le neg_pi_lt_pi.le, hpi_nonneg]
  set A : ℝ := ∫ t in (-Real.pi)..Real.pi,
    ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2
  set B : ℝ := ∫ t in (-Real.pi)..Real.pi,
    ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2
  set C : ℝ := ∫ t in (-Real.pi)..Real.pi,
    ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2
  set D : ℝ := ∫ t in (-Real.pi)..Real.pi,
    ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2
  have hsumABCD : A + B + (C + D) = Real.pi - -Real.pi := by
    rw [intervalIntegral.integral_add (hpow1.add hpowI) (hspow1.add hspowI), haddOdd, haddSlack] at hintEq
    simpa [hlength, A, B, C, D, add_assoc, add_left_comm, add_comm] using hintEq
  have hlenpos : 0 < Real.pi - -Real.pi := sub_pos.mpr neg_pi_lt_pi
  have hrewrite :
      2 * ((Real.pi - -Real.pi)⁻¹ * A) +
        2 * ((Real.pi - -Real.pi)⁻¹ * B) +
        2 * ((Real.pi - -Real.pi)⁻¹ * C) +
        2 * ((Real.pi - -Real.pi)⁻¹ * D) =
      2 * ((Real.pi - -Real.pi)⁻¹ * (A + B + (C + D))) := by
    ring
  rw [hrewrite, hsumABCD]
  have hunit : (Real.pi - -Real.pi)⁻¹ * (Real.pi - -Real.pi) = 1 := by
    field_simp [ne_of_gt hlenpos]
  nlinarith [hunit]

private theorem oddProfileDerivativeField_energy_budget
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (x : ℂ) :
    2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2) +
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          ‖((oddProfileDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2) ≤ 2 := by
  have hsharp := oddProfileDerivativeField_energy_budget_with_slack hboundary x
  have hnonneg1 :
      0 ≤ ∫ t in (-Real.pi)..Real.pi,
        ‖((distanceSlackDerivativeField boundary x t 1 : ℝ) : ℂ)‖ ^ 2 := by
    exact intervalIntegral.integral_nonneg_of_forall neg_pi_lt_pi.le
      (fun t ↦ by positivity)
  have hnonnegI :
      0 ≤ ∫ t in (-Real.pi)..Real.pi,
        ‖((distanceSlackDerivativeField boundary x t Complex.I : ℝ) : ℂ)‖ ^ 2 := by
    exact intervalIntegral.integral_nonneg_of_forall neg_pi_lt_pi.le
      (fun t ↦ by positivity)
  have hlenpos : 0 < Real.pi - -Real.pi := sub_pos.mpr neg_pi_lt_pi
  have hfac : 0 ≤ (Real.pi - -Real.pi)⁻¹ := inv_nonneg.mpr hlenpos.le
  nlinarith

theorem sum_complexDerivativeEnergy_oddProfileFourierDerivative_le_two
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) (x : ℂ) :
    (∑ k : Fin N,
      complexDerivativeEnergy
        (oddProfileFourierDerivative boundary (oddMode k) x)) ≤ 2 := by
  refine sum_complexDerivativeEnergy_le_two_of_fourierCoeffOn
    neg_pi_lt_pi N
    (fun t ↦ oddProfileDerivativeField boundary x t 1)
    (fun t ↦ oddProfileDerivativeField boundary x t Complex.I)
    (memLp_oddProfileDerivativeField_apply hboundary x 1 (by simp))
    (memLp_oddProfileDerivativeField_apply hboundary x Complex.I (by simp))
    (fun k ↦ oddProfileFourierDerivative boundary (oddMode k) x)
    ?_ ?_ (oddProfileDerivativeField_energy_budget hboundary x)
  · intro k
    simpa using oddProfileFourierDerivative_apply_eq_two_mul_fourierCoeffOn
      hboundary (oddMode k) x 1 (by simp)
  · intro k
    simpa using oddProfileFourierDerivative_apply_eq_two_mul_fourierCoeffOn
      hboundary (oddMode k) x Complex.I (by simp)

theorem ae_sum_complexDerivativeEnergy_fderiv_oddProfileFourierMap_le_two
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    ∀ᵐ x ∂volume,
      (∑ k : Fin N, complexDerivativeEnergy
        (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 := by
  filter_upwards [ae_ae_differentiableAt_oddDistanceProfile hboundary] with x hdiff
  have hderiv : ∀ k : Fin N,
      fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x =
        oddProfileFourierDerivative boundary (oddMode k) x := by
    intro k
    exact (hasFDerivAt_oddProfileFourierMap hboundary (oddMode k) x hdiff).fderiv
  calc
    (∑ k : Fin N, complexDerivativeEnergy
        (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) =
      ∑ k : Fin N,
        complexDerivativeEnergy
          (oddProfileFourierDerivative boundary (oddMode k) x) := by
        simp [hderiv]
    _ ≤ 2 := sum_complexDerivativeEnergy_oddProfileFourierDerivative_le_two
      hboundary N x

private lemma odd_profile_cos_intervalIntegrable
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) (x : X) :
    IntervalIntegrable (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x *
        Real.cos ((n : ℝ) * t)) volume (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  exact (hboundary.continuous_oddDistanceProfile_parameter x).mul (by fun_prop)

private lemma odd_profile_sin_intervalIntegrable
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) (x : X) :
    IntervalIntegrable (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x *
        Real.sin ((n : ℝ) * t)) volume (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  exact (hboundary.continuous_oddDistanceProfile_parameter x).mul (by fun_prop)

/-- Every cosine Fourier coordinate is `2`-Lipschitz on the filling. -/
theorem oddProfileCosineCoordinate_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    LipschitzWith 2 (oddProfileCosineCoordinate boundary n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  unfold oddProfileCosineCoordinate
  rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  rw [← intervalIntegral.integral_sub
    (odd_profile_cos_intervalIntegrable hboundary n x)
    (odd_profile_cos_intervalIntegrable hboundary n y)]
  have hnorm :
      ‖∫ t in (-Real.pi)..Real.pi,
        (oddDistanceProfile boundary (angleToUnitAddCircle t) x *
          Real.cos ((n : ℝ) * t) -
         oddDistanceProfile boundary (angleToUnitAddCircle t) y *
          Real.cos ((n : ℝ) * t))‖ ≤
        dist x y * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    have hprofile :
        |oddDistanceProfile boundary (angleToUnitAddCircle t) x -
          oddDistanceProfile boundary (angleToUnitAddCircle t) y| ≤ dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (oddDistanceProfile_lipschitzWith boundary
          (angleToUnitAddCircle t)).dist_le_mul x y
    calc
      |oddDistanceProfile boundary (angleToUnitAddCircle t) x -
          oddDistanceProfile boundary (angleToUnitAddCircle t) y| *
          |Real.cos ((n : ℝ) * t)| ≤ dist x y * 1 := by
            gcongr
            exact abs_cos_le_one _
      _ = dist x y := by ring
  rw [Real.norm_eq_abs] at hnorm
  have hpi : |Real.pi - -Real.pi| = 2 * Real.pi := by
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [hpi] at hnorm
  calc
    1 / Real.pi *
        |∫ t in (-Real.pi)..Real.pi,
          (oddDistanceProfile boundary (angleToUnitAddCircle t) x *
            Real.cos ((n : ℝ) * t) -
           oddDistanceProfile boundary (angleToUnitAddCircle t) y *
            Real.cos ((n : ℝ) * t))| ≤
        1 / Real.pi * (dist x y * (2 * Real.pi)) := by gcongr
    _ = 2 * dist x y := by field_simp [Real.pi_ne_zero]

/-- Every sine Fourier coordinate is `2`-Lipschitz on the filling. -/
theorem oddProfileSineCoordinate_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    LipschitzWith 2 (oddProfileSineCoordinate boundary n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  unfold oddProfileSineCoordinate
  rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr Real.pi_pos)]
  rw [← intervalIntegral.integral_sub
    (odd_profile_sin_intervalIntegrable hboundary n x)
    (odd_profile_sin_intervalIntegrable hboundary n y)]
  have hnorm :
      ‖∫ t in (-Real.pi)..Real.pi,
        (oddDistanceProfile boundary (angleToUnitAddCircle t) x *
          Real.sin ((n : ℝ) * t) -
         oddDistanceProfile boundary (angleToUnitAddCircle t) y *
          Real.sin ((n : ℝ) * t))‖ ≤
        dist x y * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    rw [← sub_mul, Real.norm_eq_abs, abs_mul]
    have hprofile :
        |oddDistanceProfile boundary (angleToUnitAddCircle t) x -
          oddDistanceProfile boundary (angleToUnitAddCircle t) y| ≤ dist x y := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        (oddDistanceProfile_lipschitzWith boundary
          (angleToUnitAddCircle t)).dist_le_mul x y
    calc
      |oddDistanceProfile boundary (angleToUnitAddCircle t) x -
          oddDistanceProfile boundary (angleToUnitAddCircle t) y| *
          |Real.sin ((n : ℝ) * t)| ≤ dist x y * 1 := by
            gcongr
            exact abs_sin_le_one _
      _ = dist x y := by ring
  rw [Real.norm_eq_abs] at hnorm
  have hpi : |Real.pi - -Real.pi| = 2 * Real.pi := by
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [hpi] at hnorm
  calc
    1 / Real.pi *
        |∫ t in (-Real.pi)..Real.pi,
          (oddDistanceProfile boundary (angleToUnitAddCircle t) x *
            Real.sin ((n : ℝ) * t) -
           oddDistanceProfile boundary (angleToUnitAddCircle t) y *
            Real.sin ((n : ℝ) * t))| ≤
        1 / Real.pi * (dist x y * (2 * Real.pi)) := by gcongr
    _ = 2 * dist x y := by field_simp [Real.pi_ne_zero]

/-- The complex Fourier map is globally `4`-Lipschitz.  This elementary
bound is enough to apply the planar Lipschitz area formula; the sharper
common estimate enters through its Jacobian budget. -/
theorem oddProfileFourierMap_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    LipschitzWith 4 (oddProfileFourierMap boundary n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold oddProfileFourierMap
  rw [show
    ((oddProfileCosineCoordinate boundary n x : ℂ) +
          (oddProfileSineCoordinate boundary n x : ℂ) * Complex.I) -
        ((oddProfileCosineCoordinate boundary n y : ℂ) +
          (oddProfileSineCoordinate boundary n y : ℂ) * Complex.I) =
      ((oddProfileCosineCoordinate boundary n x -
        oddProfileCosineCoordinate boundary n y : ℝ) : ℂ) +
      ((oddProfileSineCoordinate boundary n x -
        oddProfileSineCoordinate boundary n y : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
  calc
    ‖((oddProfileCosineCoordinate boundary n x -
          oddProfileCosineCoordinate boundary n y : ℝ) : ℂ) +
        ((oddProfileSineCoordinate boundary n x -
          oddProfileSineCoordinate boundary n y : ℝ) : ℂ) * Complex.I‖ ≤
      ‖((oddProfileCosineCoordinate boundary n x -
          oddProfileCosineCoordinate boundary n y : ℝ) : ℂ)‖ +
        ‖((oddProfileSineCoordinate boundary n x -
          oddProfileSineCoordinate boundary n y : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |oddProfileCosineCoordinate boundary n x -
          oddProfileCosineCoordinate boundary n y| +
        |oddProfileSineCoordinate boundary n x -
          oddProfileSineCoordinate boundary n y| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real,
            Complex.norm_I, mul_one]
          simp only [Real.norm_eq_abs]
    _ ≤ 2 * dist x y + 2 * dist x y := by
      gcongr
      · simpa only [Real.dist_eq, NNReal.coe_ofNat] using
          (oddProfileCosineCoordinate_lipschitzWith hboundary n).dist_le_mul x y
      · simpa only [Real.dist_eq, NNReal.coe_ofNat] using
          (oddProfileSineCoordinate_lipschitzWith hboundary n).dist_le_mul x y
    _ = 4 * dist x y := by ring

/-- In particular, every complex Fourier map is continuous. -/
theorem continuous_oddProfileFourierMap
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (n : ℕ) :
    Continuous (oddProfileFourierMap boundary n) := by
  unfold oddProfileFourierMap
  have hcos : Continuous (oddProfileCosineCoordinate boundary n) :=
    (oddProfileCosineCoordinate_lipschitzWith hboundary n).continuous
  have hsin : Continuous (oddProfileSineCoordinate boundary n) :=
    (oddProfileSineCoordinate_lipschitzWith hboundary n).continuous
  fun_prop

private lemma fixed_cosine_integral_eq_centered
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (s : ℝ) :
    (∫ t in (-Real.pi)..Real.pi,
      oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (angleToUnitAddCircle s)) * Real.cos ((n : ℝ) * t)) =
      ∫ t in (s - Real.pi)..(s + Real.pi),
        oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (angleToUnitAddCircle s)) * Real.cos ((n : ℝ) * t) := by
  have h := (odd_profile_cos_integrand_periodic boundary n
    (boundary (angleToUnitAddCircle s))).intervalIntegral_add_eq
      (-Real.pi) (s - Real.pi)
  convert h using 1 <;> ring

private lemma fixed_sine_integral_eq_centered
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (n : ℕ) (s : ℝ) :
    (∫ t in (-Real.pi)..Real.pi,
      oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (angleToUnitAddCircle s)) * Real.sin ((n : ℝ) * t)) =
      ∫ t in (s - Real.pi)..(s + Real.pi),
        oddDistanceProfile boundary (angleToUnitAddCircle t)
          (boundary (angleToUnitAddCircle s)) * Real.sin ((n : ℝ) * t) := by
  have h := (odd_profile_sin_integrand_periodic boundary n
    (boundary (angleToUnitAddCircle s))).intervalIntegral_add_eq
      (-Real.pi) (s - Real.pi)
  convert h using 1 <;> ring

/-- Exact cosine boundary value of the fixed Fourier map. -/
theorem oddProfileCosineCoordinate_on_boundary_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileCosineCoordinate boundary n (boundary (angleToUnitAddCircle s)) =
      -boundaryRadius n * Real.cos ((n : ℝ) * s) := by
  unfold oddProfileCosineCoordinate
  rw [fixed_cosine_integral_eq_centered]
  exact oddProfileCosineCoefficientOnCenteredPeriod_of_odd
    hboundary n hn s

/-- Exact sine boundary value of the fixed Fourier map. -/
theorem oddProfileSineCoordinate_on_boundary_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileSineCoordinate boundary n (boundary (angleToUnitAddCircle s)) =
      -boundaryRadius n * Real.sin ((n : ℝ) * s) := by
  unfold oddProfileSineCoordinate
  rw [fixed_sine_integral_eq_centered]
  exact oddProfileSineCoefficientOnCenteredPeriod_of_odd
    hboundary n hn s

/-- Equation (4.3) of the note, now for the actual fixed Fourier map:
`zₙ(γ(s)) = -ρₙ exp(i n s)` for every positive odd mode. -/
theorem oddProfileFourierMap_on_boundary_of_odd
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (n : ℕ) (hn : Odd n) (s : ℝ) :
    oddProfileFourierMap boundary n (boundary (angleToUnitAddCircle s)) =
      -(boundaryRadius n : ℂ) *
        Complex.exp (((((n : ℝ) * s : ℝ) : ℂ) * Complex.I)) := by
  unfold oddProfileFourierMap
  rw [oddProfileCosineCoordinate_on_boundary_of_odd hboundary n hn s,
    oddProfileSineCoordinate_on_boundary_of_odd hboundary n hn s,
    Complex.exp_mul_I]
  push_cast
  ring

lemma odd_oddMode (k : ℕ) : Odd (oddMode k) := by
  exact ⟨k, rfl⟩

private lemma complex_exp_pow_eq_mode (s : ℝ) (m : ℕ) :
    Complex.exp ((s : ℂ) * Complex.I) ^ m =
      Complex.exp (((((m : ℝ) * s : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The explicit finite Fourier sum is the previously studied mixed
dominant-harmonic Jordan curve in radian coordinates. -/
theorem givensBoundaryCurveAddCircle_angle_eq_sum
    {N : ℕ} (j : Fin N) (s : ℝ) :
    givensBoundaryCurveAddCircle j (angleToUnitAddCircle s) =
      ∑ k : Fin N,
        ((boundaryRadius (oddMode k) * givensMatrix N j k : ℝ) : ℂ) *
          Complex.exp (((((oddMode k : ℝ) * s : ℝ) : ℂ) * Complex.I)) := by
  cases N with
  | zero => exact Fin.elim0 j
  | succ N =>
      unfold givensBoundaryCurveAddCircle givensBoundaryCurve
        dominantHarmonicCurve
      rw [unitAddCircleEquivComplexUnitCircle_angle]
      rw [Fin.sum_univ_succ]
      congr 1
      · simp [oddMode]
      · apply Finset.sum_congr rfl
        intro k _
        rw [complex_exp_pow_eq_mode]
        rfl

/-- The `j`th Givens mixture of the genuine metric Fourier maps. -/
def mixedOddProfileFourierMap
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (N : ℕ) (j : Fin N) (x : X) : ℂ :=
  ∑ k : Fin N,
    (givensMatrix N j k : ℂ) * oddProfileFourierMap boundary (oddMode k) x

theorem continuous_mixedOddProfileFourierMap
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (j : Fin N) :
    Continuous (mixedOddProfileFourierMap boundary N j) := by
  unfold mixedOddProfileFourierMap
  apply continuous_finset_sum
  intro k _
  exact continuous_const.mul
    (continuous_oddProfileFourierMap hboundary (oddMode k))

/-- A convenient global Lipschitz constant for a Givens-mixed Fourier
coordinate.  The `ℓ¹` row norm is sufficient for the area arguments below. -/
def mixedOddProfileFourierLipschitzConstant
    (N : ℕ) (j : Fin N) : NNReal :=
  (4 : NNReal) * ∑ k : Fin N, ‖((givensMatrix N j k : ℝ) : ℂ)‖₊

theorem mixedOddProfileFourierMap_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (j : Fin N) :
    LipschitzWith (mixedOddProfileFourierLipschitzConstant N j)
      (mixedOddProfileFourierMap boundary N j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold mixedOddProfileFourierMap
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ k : Fin N,
        (((givensMatrix N j k : ℝ) : ℂ) * oddProfileFourierMap boundary (oddMode k) x -
          ((givensMatrix N j k : ℝ) : ℂ) * oddProfileFourierMap boundary (oddMode k) y)‖
        ≤ ∑ k : Fin N,
            ‖(((givensMatrix N j k : ℝ) : ℂ) * oddProfileFourierMap boundary (oddMode k) x -
              ((givensMatrix N j k : ℝ) : ℂ) * oddProfileFourierMap boundary (oddMode k) y)‖ :=
      norm_sum_le _ _
    _ = ∑ k : Fin N, ‖((givensMatrix N j k : ℝ) : ℂ)‖ *
          ‖oddProfileFourierMap boundary (oddMode k) x -
            oddProfileFourierMap boundary (oddMode k) y‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← mul_sub, norm_mul]
    _ ≤ ∑ k : Fin N, ‖((givensMatrix N j k : ℝ) : ℂ)‖ * (4 * dist x y) := by
      apply Finset.sum_le_sum
      intro k _
      gcongr
      rw [← dist_eq_norm]
      simpa only [NNReal.coe_ofNat] using
        (oddProfileFourierMap_lipschitzWith hboundary (oddMode k)).dist_le_mul x y
    _ = ↑(mixedOddProfileFourierLipschitzConstant N j) * dist x y := by
      unfold mixedOddProfileFourierLipschitzConstant
      push_cast
      rw [← Finset.sum_mul]
      ring

/-- Boundary formula for every mixed row, derived from the distance profile
and the Givens matrix rather than supplied as a coverage hypothesis. -/
theorem mixedOddProfileFourierMap_on_boundary
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (j : Fin N) (s : ℝ) :
    mixedOddProfileFourierMap boundary N j
        (boundary (angleToUnitAddCircle s)) =
      -(∑ k : Fin N,
        ((boundaryRadius (oddMode k) * givensMatrix N j k : ℝ) : ℂ) *
          Complex.exp (((((oddMode k : ℝ) * s : ℝ) : ℂ) * Complex.I))) := by
  unfold mixedOddProfileFourierMap
  simp_rw [oddProfileFourierMap_on_boundary_of_odd
    hboundary (oddMode _) (odd_oddMode _) s]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

theorem mixedOddProfileFourierMap_on_boundary_eq_neg_givens
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) (s : ℝ) :
    mixedOddProfileFourierMap boundary N j
        (boundary (angleToUnitAddCircle s)) =
      -givensBoundaryCurveAddCircle j (angleToUnitAddCircle s) := by
  rw [mixedOddProfileFourierMap_on_boundary hboundary,
    givensBoundaryCurveAddCircle_angle_eq_sum]

theorem angleToUnitAddCircle_surjective :
    Function.Surjective angleToUnitAddCircle := by
  intro t
  obtain ⟨r, _hr, hr⟩ := AddCircle.eq_coe_Ico t
  refine ⟨2 * Real.pi * r, ?_⟩
  unfold angleToUnitAddCircle
  rw [show (2 * Real.pi * r : ℝ) / (2 * Real.pi) = r by
    field_simp [Real.pi_ne_zero]]
  exact hr

/-- Negating the raw metric mixture matches the sign convention of the
dominant-harmonic curve used by the Jordan coverage modules. -/
def givensMetricFourierMap
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (N : ℕ) (j : Fin N) (x : X) : ℂ :=
  -mixedOddProfileFourierMap boundary N j x

theorem givensMetricFourierMap_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (j : Fin N) :
    LipschitzWith (mixedOddProfileFourierLipschitzConstant N j)
      (givensMetricFourierMap boundary N j) := by
  unfold givensMetricFourierMap
  exact (mixedOddProfileFourierMap_lipschitzWith hboundary N j).neg

/-- Orthogonal Givens mixing preserves the full derivative energy of the
genuine metric Fourier coordinates at every common differentiability
point.  This discharges the mixing portion of the unit Jacobian budget. -/
theorem sum_complexDerivativeEnergy_fderiv_givensMetricFourierMap
    {boundary : UnitAddCircle → ℂ}
    (N : ℕ) (x : ℂ)
    (hdiff : ∀ k : Fin N,
      DifferentiableAt ℝ
        (oddProfileFourierMap boundary (oddMode k)) x) :
    (∑ j : Fin N, complexDerivativeEnergy
      (fderiv ℝ (givensMetricFourierMap boundary N j) x)) =
      ∑ k : Fin N, complexDerivativeEnergy
        (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x) := by
  let F : Fin N → ℂ → ℂ := fun k ↦
    oddProfileFourierMap boundary (oddMode k)
  let L : Fin N → ℂ →L[ℝ] ℂ := fun k ↦ fderiv ℝ (F k) x
  have hderiv (j : Fin N) :
      fderiv ℝ (givensMetricFourierMap boundary N j) x =
        -complexLinearMapMix (givensMatrix N) L j := by
    apply HasFDerivAt.fderiv
    have hmix : HasFDerivAt
        (complexFunctionMix (givensMatrix N) F j)
        (complexLinearMapMix (givensMatrix N) L j) x := by
      exact hasFDerivAt_complexFunctionMix (givensMatrix N) F L j x
        (fun k ↦ (hdiff k).hasFDerivAt)
    convert hmix.neg using 1
  simp_rw [hderiv, complexDerivativeEnergy_neg]
  change (∑ j : Fin N, complexDerivativeEnergy
      (complexLinearMapMix (givensMatrix N) L j)) =
    ∑ k : Fin N, complexDerivativeEnergy (L k)
  exact sum_complexDerivativeEnergy_complexLinearMapMix
    (givensMatrix N) (givensMatrix_orthogonal N) L

/-- Every fixed finite family of genuine metric Fourier coordinates is
simultaneously differentiable almost everywhere on the complex plane. -/
theorem ae_differentiableAt_oddProfileFourierMap_fin
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    ∀ᵐ x ∂volume, ∀ k : Fin N,
      DifferentiableAt ℝ
        (oddProfileFourierMap boundary (oddMode k)) x := by
  rw [ae_all_iff]
  intro k
  exact (oddProfileFourierMap_lipschitzWith
    hboundary (oddMode k)).ae_differentiableAt

/-- Every fixed finite family of mixed Givens Fourier maps is also
simultaneously differentiable almost everywhere. -/
theorem ae_differentiableAt_givensMetricFourierMap_fin
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    ∀ᵐ x ∂volume, ∀ j : Fin N,
      DifferentiableAt ℝ (givensMetricFourierMap boundary N j) x := by
  rw [ae_all_iff]
  intro j
  exact (givensMetricFourierMap_lipschitzWith hboundary N j).ae_differentiableAt

/-- Almost everywhere, the total derivative energy of the mixed Givens rows
agrees with that of the underlying finite family of odd Fourier modes. -/
theorem ae_sum_complexDerivativeEnergy_fderiv_givensMetricFourierMap
    {boundary : UnitAddCircle → ℂ}
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    ∀ᵐ x ∂volume,
      (∑ j : Fin N, complexDerivativeEnergy
        (fderiv ℝ (givensMetricFourierMap boundary N j) x)) =
        ∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x) := by
  filter_upwards [ae_differentiableAt_oddProfileFourierMap_fin hboundary N]
    with x hdiff
  exact sum_complexDerivativeEnergy_fderiv_givensMetricFourierMap N x hdiff

theorem continuous_givensMetricFourierMap
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (j : Fin N) :
    Continuous (givensMetricFourierMap boundary N j) := by
  unfold givensMetricFourierMap
  exact (continuous_mixedOddProfileFourierMap hboundary N j).neg

/-- The metric Givens map has exactly the boundary curve required by the
Jordan and mod-two coverage theorem, for every additive-circle parameter. -/
theorem givensMetricFourierMap_on_boundary
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) (t : UnitAddCircle) :
    givensMetricFourierMap boundary N j (boundary t) =
      givensBoundaryCurveAddCircle j t := by
  obtain ⟨s, rfl⟩ := angleToUnitAddCircle_surjective t
  unfold givensMetricFourierMap
  rw [mixedOddProfileFourierMap_on_boundary_eq_neg_givens hboundary]
  simp

end

end GromovFilling
