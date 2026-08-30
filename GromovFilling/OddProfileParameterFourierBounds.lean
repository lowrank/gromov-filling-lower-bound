import GromovFilling.NonlinearCorrelationBounds
import GromovFilling.ProfileFourier
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Fourier bounds for angular odd-distance profiles

This file proves the pointwise coefficient bounds for the genuine metric
odd-distance profile.  These are the profile hypotheses used by the nonlinear
comass estimate: the angular profile is globally one-Lipschitz, its weighted
odd Fourier energy is at most two, and its first complex coefficient has the
sharp `4 / pi` bound.
-/

open MeasureTheory Metric Set
open scoped BigOperators ComplexConjugate Topology

namespace GromovFilling

noncomputable section

/-- Angles in radians map to the normalized additive circle with Lipschitz
constant `1 / (2 * pi)`. -/
theorem angleToUnitAddCircle_lipschitzWith :
    LipschitzWith
      ⟨(2 * Real.pi)⁻¹, inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)⟩
      angleToUnitAddCircle := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, show angleToUnitAddCircle s - angleToUnitAddCircle t =
      (((s - t) / (2 * Real.pi) : ℝ) : UnitAddCircle) by
    rw [show angleToUnitAddCircle s =
        ((s / (2 * Real.pi) : ℝ) : UnitAddCircle) by rfl,
      show angleToUnitAddCircle t =
        ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) by rfl,
      ← AddCircle.coe_sub]
    congr 1
    ring]
  calc
    ‖(((s - t) / (2 * Real.pi) : ℝ) : UnitAddCircle)‖ ≤
        ‖(s - t) / (2 * Real.pi)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |s - t| / (2 * Real.pi) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    _ = (2 * Real.pi)⁻¹ * dist s t := by
      rw [Real.dist_eq]
      field_simp

/-- For an isometric circumference-`2 * pi` boundary, the genuine angular
odd-distance profile is globally one-Lipschitz. -/
theorem IsometricCircleBoundary.lipschitzWith_oddDistanceProfile_parameter
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    LipschitzWith 1 (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x) := by
  apply LipschitzWith.mk_one
  intro s t
  rw [Real.dist_eq]
  unfold oddDistanceProfile boundaryDistance
  have hfirst :
      |dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary (angleToUnitAddCircle t))| ≤ |s - t| := by
    calc
      |dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary (angleToUnitAddCircle t))| ≤
          dist (boundary (angleToUnitAddCircle s))
            (boundary (angleToUnitAddCircle t)) := by
        simpa only [Real.dist_eq] using dist_dist_dist_le_right x
          (boundary (angleToUnitAddCircle s))
          (boundary (angleToUnitAddCircle t))
      _ = 2 * Real.pi * dist (angleToUnitAddCircle s)
          (angleToUnitAddCircle t) := hboundary _ _
      _ ≤ 2 * Real.pi * ((2 * Real.pi)⁻¹ * dist s t) := by
        gcongr
        exact angleToUnitAddCircle_lipschitzWith.dist_le_mul s t
      _ = |s - t| := by
        rw [Real.dist_eq]
        field_simp [Real.pi_ne_zero]
  have hsecond :
      |dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))| ≤
        |s - t| := by
    calc
      |dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))| ≤
          dist
            (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))
            (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) := by
        simpa only [Real.dist_eq] using dist_dist_dist_le_right x
          (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))
          (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))
      _ = 2 * Real.pi *
          dist
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)) :=
        hboundary _ _
      _ = 2 * Real.pi *
          dist (angleToUnitAddCircle s) (angleToUnitAddCircle t) := by
        rw [dist_add_right]
      _ ≤ 2 * Real.pi * ((2 * Real.pi)⁻¹ * dist s t) := by
        gcongr
        exact angleToUnitAddCircle_lipschitzWith.dist_le_mul s t
      _ = |s - t| := by
        rw [Real.dist_eq]
        field_simp [Real.pi_ne_zero]
  calc
    |(dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
        (dist x (boundary (angleToUnitAddCircle t)) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2| =
        |(dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary (angleToUnitAddCircle t))) -
          (dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))))| / 2 := by
      rw [show
        (dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
          (dist x (boundary (angleToUnitAddCircle t)) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 =
          ((dist x (boundary (angleToUnitAddCircle s)) -
              dist x (boundary (angleToUnitAddCircle t))) -
            (dist x (boundary
                (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
              dist x (boundary
                (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))))) / 2 by
          ring,
        abs_div]
      norm_num
    _ ≤
        (|dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary (angleToUnitAddCircle t))| +
          |dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))|) / 2 := by
      gcongr
      exact abs_sub _ _
    _ ≤ |s - t| := by linarith

private theorem lipschitzWith_nat_mul (n : ℕ) :
    LipschitzWith ⟨n, Nat.cast_nonneg n⟩ (fun t : ℝ ↦ (n : ℝ) * t) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, Real.dist_eq]
  push_cast
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]

private theorem absolutelyContinuousOnInterval_sin_nat_mul
    (n : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ ↦ Real.sin ((n : ℝ) * t)) a b := by
  exact (Real.lipschitzWith_sin.comp (lipschitzWith_nat_mul n)).lipschitzOnWith
    |>.absolutelyContinuousOnInterval

private theorem absolutelyContinuousOnInterval_cos_nat_mul
    (n : ℕ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ ↦ Real.cos ((n : ℝ) * t)) a b := by
  exact (Real.lipschitzWith_cos.comp (lipschitzWith_nat_mul n)).lipschitzOnWith
    |>.absolutelyContinuousOnInterval

private theorem deriv_sin_nat_mul (n : ℕ) (t : ℝ) :
    deriv (fun s : ℝ ↦ Real.sin ((n : ℝ) * s)) t =
      (n : ℝ) * Real.cos ((n : ℝ) * t) := by
  have hlin : HasDerivAt (fun s : ℝ ↦ (n : ℝ) * s) (n : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (n : ℝ)
  simpa only [Function.comp_apply, mul_comm] using
    ((Real.hasDerivAt_sin _).comp t hlin).deriv

private theorem deriv_cos_nat_mul (n : ℕ) (t : ℝ) :
    deriv (fun s : ℝ ↦ Real.cos ((n : ℝ) * s)) t =
      -(n : ℝ) * Real.sin ((n : ℝ) * t) := by
  have hlin : HasDerivAt (fun s : ℝ ↦ (n : ℝ) * s) (n : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (n : ℝ)
  have hder :
      deriv (fun s : ℝ ↦ Real.cos ((n : ℝ) * s)) t =
        -Real.sin ((n : ℝ) * t) * (n : ℝ) := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_cos _).comp t hlin).deriv
  rw [hder]
  ring

/-- Multiplying a genuine angular profile coefficient by its mode is a
quarter-turn of twice the corresponding Fourier coefficient of the a.e.
derivative. Absolute continuity supplies the integration-by-parts step, so
no pointwise differentiability hypothesis is needed. -/
theorem oddProfileFourierMap_mode_mul_eq_deriv_fourierCoeffOn
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) (n : ℕ) :
    (((n : ℝ) : ℂ) * oddProfileFourierMap boundary n x) =
      Complex.I *
        (2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ ((deriv (fun s : ℝ ↦
            oddDistanceProfile boundary (angleToUnitAddCircle s) x) t : ℝ) : ℂ))
          (-(n : ℤ))) := by
  let f : ℝ → ℝ := fun t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) x
  let d : ℝ → ℝ := deriv f
  have hfLip : LipschitzWith 1 f := by
    simpa only [f] using hboundary.lipschitzWith_oddDistanceProfile_parameter x
  have hfAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi :=
    hfLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdInt : IntervalIntegrable d volume (-Real.pi) Real.pi := by
    simpa only [d] using hfAC.intervalIntegrable_deriv
  have hdIntComplex : IntervalIntegrable (fun t ↦ (d t : ℂ)) volume
      (-Real.pi) Real.pi := by
    constructor
    · exact Complex.ofRealCLM.integrable_comp hdInt.1
    · exact Complex.ofRealCLM.integrable_comp hdInt.2
  have hfperiod : f Real.pi = f (-Real.pi) := by
    dsimp only [f]
    rw [← angleToUnitAddCircle_add_two_pi (-Real.pi)]
    congr 3
    ring
  have hsinpi : Real.sin ((n : ℝ) * Real.pi) = 0 :=
    Real.sin_nat_mul_pi n
  have hsinnpi : Real.sin ((n : ℝ) * -Real.pi) = 0 := by
    rw [show (n : ℝ) * -Real.pi = -((n : ℝ) * Real.pi) by ring,
      Real.sin_neg, hsinpi, neg_zero]
  have hcosEndpoints :
      Real.cos ((n : ℝ) * Real.pi) = Real.cos ((n : ℝ) * -Real.pi) := by
    rw [show (n : ℝ) * -Real.pi = -((n : ℝ) * Real.pi) by ring,
      Real.cos_neg]
  have hsinAC := absolutelyContinuousOnInterval_sin_nat_mul
    n (-Real.pi) Real.pi
  have hcosAC := absolutelyContinuousOnInterval_cos_nat_mul
    n (-Real.pi) Real.pi
  have hcosParts :
      (n : ℝ) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.cos ((n : ℝ) * t) =
        -∫ t in (-Real.pi)..Real.pi,
          d t * Real.sin ((n : ℝ) * t) := by
    calc
      (n : ℝ) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.cos ((n : ℝ) * t) =
          ∫ t in (-Real.pi)..Real.pi,
            f t * deriv (fun s : ℝ ↦ Real.sin ((n : ℝ) * s)) t := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        change (n : ℝ) * (f t * Real.cos ((n : ℝ) * t)) =
          f t * deriv (fun s : ℝ ↦ Real.sin ((n : ℝ) * s)) t
        rw [deriv_sin_nat_mul]
        ring
      _ = f Real.pi * Real.sin ((n : ℝ) * Real.pi) -
          f (-Real.pi) * Real.sin ((n : ℝ) * -Real.pi) -
          ∫ t in (-Real.pi)..Real.pi,
            d t * Real.sin ((n : ℝ) * t) := by
        simpa only [d] using hfAC.integral_mul_deriv_eq_deriv_mul hsinAC
      _ = -∫ t in (-Real.pi)..Real.pi,
          d t * Real.sin ((n : ℝ) * t) := by
        rw [hsinpi, hsinnpi]
        ring
  have hsinParts :
      (n : ℝ) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.sin ((n : ℝ) * t) =
        ∫ t in (-Real.pi)..Real.pi,
          d t * Real.cos ((n : ℝ) * t) := by
    have hparts := hfAC.integral_mul_deriv_eq_deriv_mul hcosAC
    have hraw :
        ∫ t in (-Real.pi)..Real.pi,
            f t * (-(n : ℝ) * Real.sin ((n : ℝ) * t)) =
          f Real.pi * Real.cos ((n : ℝ) * Real.pi) -
            f (-Real.pi) * Real.cos ((n : ℝ) * -Real.pi) -
            ∫ t in (-Real.pi)..Real.pi,
              d t * Real.cos ((n : ℝ) * t) := by
      simpa only [d, deriv_cos_nat_mul] using hparts
    have hboundaryZero :
        f Real.pi * Real.cos ((n : ℝ) * Real.pi) -
          f (-Real.pi) * Real.cos ((n : ℝ) * -Real.pi) = 0 := by
      rw [hfperiod, hcosEndpoints]
      ring
    calc
      (n : ℝ) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.sin ((n : ℝ) * t) =
          -(∫ t in (-Real.pi)..Real.pi,
            f t * (-(n : ℝ) * Real.sin ((n : ℝ) * t))) := by
        rw [← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = ∫ t in (-Real.pi)..Real.pi,
          d t * Real.cos ((n : ℝ) * t) := by
        rw [hraw, hboundaryZero]
        ring
  have hcoeff := two_mul_fourierCoeffOn_neg_eq_cos_add_sin
    (by linarith [Real.pi_pos] : -Real.pi < Real.pi) hdIntComplex n
  have hdcosInt : IntervalIntegrable
      (fun t ↦ d t * Real.cos ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    exact hdInt.mul_continuousOn (by
      simpa [Set.uIcc_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using
        (show ContinuousOn (fun t : ℝ ↦ Real.cos ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hdsinInt : IntervalIntegrable
      (fun t ↦ d t * Real.sin ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    exact hdInt.mul_continuousOn (by
      simpa [Set.uIcc_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using
        (show ContinuousOn (fun t : ℝ ↦ Real.sin ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hdcosCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.intervalIntegral_comp_comm hdcosInt)
  have hdsinCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.intervalIntegral_comp_comm hdsinInt)
  rw [show (deriv (fun s : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle s) x)) = d by rfl,
    hcoeff, hdcosCast, hdsinCast]
  unfold oddProfileFourierMap oddProfileCosineCoordinate
    oddProfileSineCoordinate
  change (((n : ℝ) : ℂ) *
      ((((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) +
        (((1 / Real.pi) * ∫ t in (-Real.pi)..Real.pi,
          f t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I)) = _
  have hcosPartsComplex :
      (((n : ℝ) : ℂ) *
          ((∫ t in (-Real.pi)..Real.pi,
            f t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) =
        -((∫ t in (-Real.pi)..Real.pi,
          d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) := by
    exact_mod_cast hcosParts
  have hsinPartsComplex :
      (((n : ℝ) : ℂ) *
          ((∫ t in (-Real.pi)..Real.pi,
            f t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
          d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
    exact_mod_cast hsinParts
  have hcosPartsComplexNat :
      ((n : ℂ) *
          ((∫ t in (-Real.pi)..Real.pi,
            f t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) =
        -((∫ t in (-Real.pi)..Real.pi,
          d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hcosPartsComplex
  have hsinPartsComplexNat :
      ((n : ℂ) *
          ((∫ t in (-Real.pi)..Real.pi,
            f t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
          d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using hsinPartsComplex
  push_cast
  calc
    ((n : ℂ) *
        (1 / (Real.pi : ℂ) *
            ((∫ t in (-Real.pi)..Real.pi,
              f t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) +
          1 / (Real.pi : ℂ) *
            ((∫ t in (-Real.pi)..Real.pi,
              f t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I)) =
        1 / (Real.pi : ℂ) *
            ((n : ℂ) * ((∫ t in (-Real.pi)..Real.pi,
              f t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) +
          1 / (Real.pi : ℂ) *
            ((n : ℂ) * ((∫ t in (-Real.pi)..Real.pi,
              f t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) * Complex.I := by
      ring
    _ = 1 / (Real.pi : ℂ) *
          -((∫ t in (-Real.pi)..Real.pi,
            d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) +
        1 / (Real.pi : ℂ) *
          ((∫ t in (-Real.pi)..Real.pi,
            d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
      rw [hcosPartsComplexNat, hsinPartsComplexNat]
    _ = Complex.I *
        (1 / (Real.pi : ℂ) *
            ((∫ t in (-Real.pi)..Real.pi,
              d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) +
          1 / (Real.pi : ℂ) *
            ((∫ t in (-Real.pi)..Real.pi,
              d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
      have hI (z : ℂ) : Complex.I * (z * Complex.I) = -z := by
        calc
          Complex.I * (z * Complex.I) = z * (Complex.I * Complex.I) := by ring
          _ = -z := by rw [Complex.I_mul_I]; ring
      rw [mul_add, hI]
      ring

/-- Every finite family of genuine odd-profile coefficients satisfies the
sharp weighted energy estimate coming from the unit Lipschitz constant. -/
theorem sum_oddProfileFourierMap_weighted_sq_le_two
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) (N : ℕ) :
    (∑ k : Fin N, (oddMode k : ℝ) ^ 2 *
      ‖oddProfileFourierMap boundary (oddMode k) x‖ ^ 2) ≤ 2 := by
  let f : ℝ → ℝ := fun t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) x
  let d : ℝ → ℝ := deriv f
  have hfLip : LipschitzWith 1 f := by
    simpa only [f] using hboundary.lipschitzWith_oddDistanceProfile_parameter x
  have hfAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi :=
    hfLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdInt : IntervalIntegrable d volume (-Real.pi) Real.pi := by
    simpa only [d] using hfAC.intervalIntegrable_deriv
  have hdIntComplex : IntervalIntegrable (fun t ↦ (d t : ℂ)) volume
      (-Real.pi) Real.pi := by
    constructor
    · exact Complex.ofRealCLM.integrable_comp hdInt.1
    · exact Complex.ofRealCLM.integrable_comp hdInt.2
  have hdBound (t : ℝ) : ‖(d t : ℂ)‖ ≤ 1 := by
    simpa only [d, Complex.norm_real, Real.norm_eq_abs, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := t) hfLip)
  have hdL2 : MemLp (fun t ↦ (d t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    MemLp.of_bound hdIntComplex.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hdBound)
  have hdSqInt : IntervalIntegrable (fun t ↦ ‖(d t : ℂ)‖ ^ 2) volume
      (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hdL2)
  have hdEnergy :
      (∫ t in (-Real.pi)..Real.pi, ‖(d t : ℂ)‖ ^ 2) ≤
        2 * Real.pi := by
    calc
      (∫ t in (-Real.pi)..Real.pi, ‖(d t : ℂ)‖ ^ 2) ≤
          ∫ _t in (-Real.pi)..Real.pi, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on
          (by linarith [Real.pi_pos]) hdSqInt
          ((continuous_const : Continuous (fun _t : ℝ ↦ (1 : ℝ)))
            |>.intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
          (fun t _ ↦ by nlinarith [hdBound t, norm_nonneg (d t : ℂ)])
      _ = 2 * Real.pi := by simp; ring
  have hoddinj : Function.Injective (fun k : Fin N ↦ oddMode k) := by
    intro k l hkl
    apply Fin.val_injective
    have hval : 2 * k.val + 1 = 2 * l.val + 1 := by
      simpa only [oddMode] using hkl
    omega
  have hoddpos : ∀ k : Fin N, 0 < oddMode k := by
    intro k
    unfold oddMode
    omega
  have hbessel := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
    d hdL2 (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  simp only [smul_eq_mul] at hbessel
  have hnormalized :
      (Real.pi - -Real.pi)⁻¹ *
          (∫ t in (-Real.pi)..Real.pi, ‖(d t : ℂ)‖ ^ 2) ≤ 1 := by
    calc
      (Real.pi - -Real.pi)⁻¹ *
          (∫ t in (-Real.pi)..Real.pi, ‖(d t : ℂ)‖ ^ 2) ≤
          (Real.pi - -Real.pi)⁻¹ * (2 * Real.pi) := by
        exact mul_le_mul_of_nonneg_left hdEnergy
          (inv_nonneg.mpr (by linarith [Real.pi_pos]))
      _ = 1 := by field_simp [Real.pi_ne_zero]; ring
  have hfourier :
      4 * (∑ k : Fin N,
        ‖fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-(oddMode k : ℤ))‖ ^ 2) ≤ 2 := by
    linarith [hbessel.trans hnormalized]
  have hmodeSq (k : Fin N) :
      (oddMode k : ℝ) ^ 2 *
          ‖oddProfileFourierMap boundary (oddMode k) x‖ ^ 2 =
        4 * ‖fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-(oddMode k : ℤ))‖ ^ 2 := by
    have hmode := oddProfileFourierMap_mode_mul_eq_deriv_fourierCoeffOn
      hboundary x (oddMode k)
    rw [show (deriv (fun s : ℝ ↦
        oddDistanceProfile boundary (angleToUnitAddCircle s) x)) = d by rfl] at hmode
    have hnorm := congrArg norm hmode
    simp only [norm_mul, Complex.norm_real, Real.norm_natCast,
      Complex.norm_I, one_mul] at hnorm
    norm_num at hnorm
    nlinarith [norm_nonneg (oddProfileFourierMap boundary (oddMode k) x),
      norm_nonneg (fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
        (fun t ↦ (d t : ℂ)) (-(oddMode k : ℤ)))]
  calc
    (∑ k : Fin N, (oddMode k : ℝ) ^ 2 *
        ‖oddProfileFourierMap boundary (oddMode k) x‖ ^ 2) =
        ∑ k : Fin N, 4 * ‖fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-(oddMode k : ℤ))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      exact hmodeSq k
    _ = 4 * (∑ k : Fin N, ‖fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-(oddMode k : ℤ))‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 2 := hfourier

/-- The weighted energy estimate implies the exact finite profile inequality
used by the nonlinear comass calculation: the first mode has weight one and
all remaining positive odd modes have squared weight at least nine. -/
theorem oddProfileFourierMap_first_add_nine_tail_energy_le_two
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) (N : ℕ) :
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
        9 * finiteComplexEnergy (fun n : Fin N ↦
          oddProfileFourierMap boundary (oddMode n.succ) x) ≤ 2 := by
  have hweighted := sum_oddProfileFourierMap_weighted_sq_le_two
    hboundary x (N + 1)
  rw [Fin.sum_univ_succ] at hweighted
  have htail :
      9 * finiteComplexEnergy (fun n : Fin N ↦
          oddProfileFourierMap boundary (oddMode n.succ) x) ≤
        ∑ n : Fin N, (oddMode n.succ : ℝ) ^ 2 *
          ‖oddProfileFourierMap boundary (oddMode n.succ) x‖ ^ 2 := by
    unfold finiteComplexEnergy
    simp_rw [← Complex.sq_norm]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hmodeNat : 3 ≤ oddMode n.succ := by
      simp [oddMode]
    have hmode : (3 : ℝ) ≤ oddMode n.succ := by
      exact_mod_cast hmodeNat
    have hmodeSq : (9 : ℝ) ≤ (oddMode n.succ : ℝ) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hmodeSq
      (sq_nonneg ‖oddProfileFourierMap boundary (oddMode n.succ) x‖)
  calc
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
        9 * finiteComplexEnergy (fun n : Fin N ↦
          oddProfileFourierMap boundary (oddMode n.succ) x) ≤
        ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
          ∑ n : Fin N, (oddMode n.succ : ℝ) ^ 2 *
            ‖oddProfileFourierMap boundary (oddMode n.succ) x‖ ^ 2 :=
      add_le_add le_rfl htail
    _ = (oddMode (0 : Fin (N + 1)) : ℝ) ^ 2 *
          ‖oddProfileFourierMap boundary (oddMode (0 : Fin (N + 1))) x‖ ^ 2 +
        ∑ n : Fin N, (oddMode n.succ : ℝ) ^ 2 *
          ‖oddProfileFourierMap boundary (oddMode n.succ) x‖ ^ 2 := by
      simp [oddMode]
    _ ≤ 2 := hweighted

private theorem integral_abs_cos_standard_full_period :
    (∫ t in -(Real.pi / 2)..(Real.pi + Real.pi / 2), |Real.cos t|) = 4 := by
  have hcont : Continuous (fun t : ℝ ↦ |Real.cos t|) :=
    Real.continuous_cos.abs
  have hleft :
      (∫ t in -(Real.pi / 2)..(Real.pi / 2), |Real.cos t|) = 2 := by
    calc
      (∫ t in -(Real.pi / 2)..(Real.pi / 2), |Real.cos t|) =
          ∫ t in -(Real.pi / 2)..(Real.pi / 2), Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t ht
        change |Real.cos t| = Real.cos t
        rw [abs_of_nonneg]
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact Real.cos_nonneg_of_mem_Icc ht
      _ = Real.sin (Real.pi / 2) - Real.sin (-(Real.pi / 2)) :=
        integral_cos
      _ = 2 := by rw [Real.sin_neg, Real.sin_pi_div_two]; norm_num
  have hright :
      (∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), |Real.cos t|) = 2 := by
    calc
      (∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), |Real.cos t|) =
          ∫ t in (Real.pi / 2)..(Real.pi + Real.pi / 2), -Real.cos t := by
        apply intervalIntegral.integral_congr
        intro t ht
        change |Real.cos t| = -Real.cos t
        rw [abs_of_nonpos]
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
        exact Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 ht.2
      _ = -(Real.sin (Real.pi + Real.pi / 2) -
          Real.sin (Real.pi / 2)) := by
        rw [intervalIntegral.integral_neg, integral_cos]
      _ = 2 := by
        rw [Real.sin_add, Real.sin_pi, Real.cos_pi,
          Real.sin_pi_div_two, Real.cos_pi_div_two]
        norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-(Real.pi / 2)) (Real.pi / 2))
    (hcont.intervalIntegrable (Real.pi / 2) (Real.pi + Real.pi / 2)),
    hleft, hright]
  norm_num

/-- The `L¹` norm of every phase shift of cosine over one full angular
period is exactly four. -/
theorem integral_abs_cos_sub_full_period (theta : ℝ) :
    (∫ t in (-Real.pi)..Real.pi, |Real.cos (t - theta)|) = 4 := by
  let g : ℝ → ℝ := fun t ↦ |Real.cos (t - theta)|
  have hgperiod : Function.Periodic g (2 * Real.pi) := by
    intro t
    dsimp only [g]
    rw [show t + 2 * Real.pi - theta = (t - theta) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  have hshift := hgperiod.intervalIntegral_add_eq
    (-Real.pi) (theta - Real.pi / 2)
  have hperiodIntegral :
      (∫ t in (-Real.pi)..Real.pi, g t) =
        ∫ t in (theta - Real.pi / 2)..(theta + (Real.pi + Real.pi / 2)), g t := by
    convert hshift using 1
    all_goals ring_nf
  rw [hperiodIntegral]
  change (∫ t in (theta - Real.pi / 2)..(theta + (Real.pi + Real.pi / 2)),
    |Real.cos (t - theta)|) = 4
  calc
    (∫ t in (theta - Real.pi / 2)..(theta + (Real.pi + Real.pi / 2)),
        |Real.cos (t - theta)|) =
        ∫ u in (theta - Real.pi / 2 - theta)..
          (theta + (Real.pi + Real.pi / 2) - theta), |Real.cos u| := by
      simpa using (intervalIntegral.integral_comp_sub_right
        (f := fun u : ℝ ↦ |Real.cos u|)
        (a := theta - Real.pi / 2)
        (b := theta + (Real.pi + Real.pi / 2)) theta)
    _ = 4 := by
      convert integral_abs_cos_standard_full_period using 1
      all_goals ring_nf

/-- A real density bounded by one has first complex trigonometric moment of
norm at most four over a full period. The proof rotates by the argument of
the moment and uses the exact `L¹` norm of a shifted cosine. -/
theorem norm_first_trigonometric_moment_le_four
    (d : ℝ → ℝ)
    (hdInt : IntervalIntegrable d volume (-Real.pi) Real.pi)
    (hdBound : ∀ t, |d t| ≤ 1) :
    ‖(((∫ t in (-Real.pi)..Real.pi, d t * Real.cos t : ℝ) : ℂ) +
        ((∫ t in (-Real.pi)..Real.pi, d t * Real.sin t : ℝ) : ℂ) *
          Complex.I)‖ ≤ 4 := by
  let C : ℝ := ∫ t in (-Real.pi)..Real.pi, d t * Real.cos t
  let S : ℝ := ∫ t in (-Real.pi)..Real.pi, d t * Real.sin t
  let w : ℂ := (C : ℂ) + (S : ℂ) * Complex.I
  let theta : ℝ := Complex.arg w
  have hwre : w.re = C := by simp [w]
  have hwim : w.im = S := by simp [w]
  have hprojection :
      Real.cos theta * C + Real.sin theta * S = ‖w‖ := by
    rw [← hwre, ← hwim]
    rw [← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
    change Real.cos theta * (‖w‖ * Real.cos theta) +
      Real.sin theta * (‖w‖ * Real.sin theta) = ‖w‖
    calc
      Real.cos theta * (‖w‖ * Real.cos theta) +
          Real.sin theta * (‖w‖ * Real.sin theta) =
          ‖w‖ * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
      _ = ‖w‖ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hcosInt : IntervalIntegrable (fun t ↦ d t * Real.cos t) volume
      (-Real.pi) Real.pi := hdInt.mul_continuousOn (by fun_prop)
  have hsinInt : IntervalIntegrable (fun t ↦ d t * Real.sin t) volume
      (-Real.pi) Real.pi := hdInt.mul_continuousOn (by fun_prop)
  have hshiftInt : IntervalIntegrable
      (fun t ↦ d t * Real.cos (t - theta)) volume
      (-Real.pi) Real.pi := hdInt.mul_continuousOn (by fun_prop)
  have habsShiftInt : IntervalIntegrable
      (fun t ↦ |Real.cos (t - theta)|) volume
      (-Real.pi) Real.pi := by
    exact (Real.continuous_cos.comp
      (continuous_id.sub continuous_const)).abs.intervalIntegrable
        (-Real.pi) Real.pi
  have hcombine :
      (∫ t in (-Real.pi)..Real.pi, d t * Real.cos (t - theta)) =
        Real.cos theta * C + Real.sin theta * S := by
    calc
      (∫ t in (-Real.pi)..Real.pi, d t * Real.cos (t - theta)) =
          ∫ t in (-Real.pi)..Real.pi,
            Real.cos theta * (d t * Real.cos t) +
              Real.sin theta * (d t * Real.sin t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change d t * Real.cos (t - theta) =
          Real.cos theta * (d t * Real.cos t) +
            Real.sin theta * (d t * Real.sin t)
        rw [Real.cos_sub]
        ring
      _ = (∫ t in (-Real.pi)..Real.pi,
            Real.cos theta * (d t * Real.cos t)) +
          ∫ t in (-Real.pi)..Real.pi,
            Real.sin theta * (d t * Real.sin t) := by
        rw [intervalIntegral.integral_add
          (hcosInt.const_mul (Real.cos theta))
          (hsinInt.const_mul (Real.sin theta))]
      _ = Real.cos theta * C + Real.sin theta * S := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hnormIntegral :
      ‖w‖ = ∫ t in (-Real.pi)..Real.pi,
        d t * Real.cos (t - theta) :=
    hprojection.symm.trans hcombine.symm
  change ‖w‖ ≤ 4
  rw [hnormIntegral]
  calc
    (∫ t in (-Real.pi)..Real.pi, d t * Real.cos (t - theta)) ≤
        ∫ t in (-Real.pi)..Real.pi, |Real.cos (t - theta)| := by
      exact intervalIntegral.integral_mono_on
        (by linarith [Real.pi_pos]) hshiftInt habsShiftInt
        (fun t _ ↦ by
          calc
            d t * Real.cos (t - theta) ≤
                |d t * Real.cos (t - theta)| := le_abs_self _
            _ = |d t| * |Real.cos (t - theta)| := abs_mul _ _
            _ ≤ 1 * |Real.cos (t - theta)| := by
              gcongr
              exact hdBound t
            _ = |Real.cos (t - theta)| := one_mul _)
    _ = 4 := integral_abs_cos_sub_full_period theta

/-- The genuine first odd-profile coefficient obeys the sharp bound
`4 / pi` at every point of every pseudometric target with an isometric
circumference-`2 * pi` boundary. -/
theorem norm_oddProfileFourierMap_first_le_four_div_pi
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ≤ 4 / Real.pi := by
  change ‖oddProfileFourierMap boundary 1 x‖ ≤ 4 / Real.pi
  let f : ℝ → ℝ := fun t ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) x
  let d : ℝ → ℝ := deriv f
  let C : ℝ := ∫ t in (-Real.pi)..Real.pi, d t * Real.cos t
  let S : ℝ := ∫ t in (-Real.pi)..Real.pi, d t * Real.sin t
  let w : ℂ := (C : ℂ) + (S : ℂ) * Complex.I
  have hfLip : LipschitzWith 1 f := by
    simpa only [f] using hboundary.lipschitzWith_oddDistanceProfile_parameter x
  have hfAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi :=
    hfLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdInt : IntervalIntegrable d volume (-Real.pi) Real.pi := by
    simpa only [d] using hfAC.intervalIntegrable_deriv
  have hdIntComplex : IntervalIntegrable (fun t ↦ (d t : ℂ)) volume
      (-Real.pi) Real.pi := by
    constructor
    · exact Complex.ofRealCLM.integrable_comp hdInt.1
    · exact Complex.ofRealCLM.integrable_comp hdInt.2
  have hdBound (t : ℝ) : |d t| ≤ 1 := by
    simpa only [d, Real.norm_eq_abs, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := t) hfLip)
  have hmoment : ‖w‖ ≤ 4 := by
    simpa only [w, C, S] using
      norm_first_trigonometric_moment_le_four d hdInt hdBound
  have hmode := oddProfileFourierMap_mode_mul_eq_deriv_fourierCoeffOn
    hboundary x 1
  rw [show (deriv (fun s : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle s) x)) = d by rfl] at hmode
  norm_num at hmode
  have hprofileNorm :
      ‖oddProfileFourierMap boundary 1 x‖ =
        ‖2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-1)‖ := by
    have hnorm := congrArg norm hmode
    simpa only [norm_mul, Complex.norm_I, one_mul] using hnorm
  have hdcosInt : IntervalIntegrable (fun t ↦ d t * Real.cos t) volume
      (-Real.pi) Real.pi := hdInt.mul_continuousOn (by fun_prop)
  have hdsinInt : IntervalIntegrable (fun t ↦ d t * Real.sin t) volume
      (-Real.pi) Real.pi := hdInt.mul_continuousOn (by fun_prop)
  have hdcosCast :
      (∫ t in (-Real.pi)..Real.pi, ((d t * Real.cos t : ℝ) : ℂ)) =
        ((C : ℝ) : ℂ) := by
    simpa only [C] using
      (Complex.ofRealCLM.intervalIntegral_comp_comm hdcosInt)
  have hdsinCast :
      (∫ t in (-Real.pi)..Real.pi, ((d t * Real.sin t : ℝ) : ℂ)) =
        ((S : ℝ) : ℂ) := by
    simpa only [S] using
      (Complex.ofRealCLM.intervalIntegral_comp_comm hdsinInt)
  have hcoeff := two_mul_fourierCoeffOn_neg_eq_cos_add_sin
    (by linarith [Real.pi_pos] : -Real.pi < Real.pi) hdIntComplex 1
  simp only [Nat.cast_one, one_mul] at hcoeff
  have hcoeffFactored :
      2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-1) =
        (((1 / Real.pi : ℝ) : ℂ) * w) := by
    rw [hcoeff, hdcosCast, hdsinCast]
    simp only [w]
    push_cast
    ring
  calc
    ‖oddProfileFourierMap boundary 1 x‖ =
        ‖2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d t : ℂ)) (-1)‖ := hprofileNorm
    _ = ‖(((1 / Real.pi : ℝ) : ℂ) * w)‖ := by rw [hcoeffFactored]
    _ = (1 / Real.pi) * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr Real.pi_pos)]
    _ ≤ (1 / Real.pi) * 4 := by
      exact mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 4 / Real.pi := by ring

#print axioms oddProfileFourierMap_mode_mul_eq_deriv_fourierCoeffOn
#print axioms sum_oddProfileFourierMap_weighted_sq_le_two
#print axioms oddProfileFourierMap_first_add_nine_tail_energy_le_two
#print axioms norm_oddProfileFourierMap_first_le_four_div_pi

end

end GromovFilling
