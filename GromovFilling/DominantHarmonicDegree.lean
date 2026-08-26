import GromovFilling.CircleDegree
import GromovFilling.DominantHarmonic

/-!
# Degree of a dominant-harmonic boundary curve

This file develops the explicit winding-number part of Lemma 5.3.  It
uses the real-lift degree from `CircleDegree` and radial normalization.
-/

namespace GromovFilling

noncomputable section

/-- Radial normalization at zero respects multiplication of nonzero
complex numbers. -/
theorem radialProjection_zero_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    radialProjection 0 ⟨a * b, mul_ne_zero ha hb⟩ =
      complexUnitCircleMul (radialProjection 0 ⟨a, ha⟩)
        (radialProjection 0 ⟨b, hb⟩) := by
  apply Subtype.ext
  simp only [radialProjection, complexUnitCircleMul, sub_zero]
  rw [norm_mul]
  have hna : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr ha)
  have hnb : (‖b‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hb)
  field_simp [hna, hnb]

/-- Radial normalization fixes a point already on the unit circle. -/
theorem radialProjection_zero_unit (u : ComplexUnitCircle) :
    radialProjection 0 ⟨(u : ℂ), norm_ne_zero_iff.mp (by rw [u.property]; norm_num)⟩ =
      u := by
  apply Subtype.ext
  simp [radialProjection, u.property]

/-- The radial normalization of `a z`, for fixed nonzero `a` and the
standard unit-circle parameter `z`, has degree one. -/
theorem hasComplexCircleDegree_linear (a : ℂ) (ha : a ≠ 0) :
    HasComplexCircleDegree
      (radialMap
        (fun x : UnitAddCircle ↦
          a * (unitAddCircleEquivComplexUnitCircle x : ℂ))
        0
        (fun x ↦ mul_ne_zero ha
          (norm_ne_zero_iff.mp (by
            rw [(unitAddCircleEquivComplexUnitCircle x).property]
            norm_num))))
      1 := by
  let ua : ComplexUnitCircle := radialProjection 0 ⟨a, ha⟩
  have hdegree := (hasComplexCircleDegree_const ua).mul
    hasComplexCircleDegree_standard
  convert hdegree using 1
  funext x
  simp only [radialMap, ua]
  have hz : (unitAddCircleEquivComplexUnitCircle x : ℂ) ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [(unitAddCircleEquivComplexUnitCircle x).property]
      norm_num)
  calc
    radialProjection 0 ⟨a * (unitAddCircleEquivComplexUnitCircle x : ℂ),
        mul_ne_zero ha hz⟩ =
        complexUnitCircleMul (radialProjection 0 ⟨a, ha⟩)
          (radialProjection 0
            ⟨(unitAddCircleEquivComplexUnitCircle x : ℂ), hz⟩) :=
      radialProjection_zero_mul a
        (unitAddCircleEquivComplexUnitCircle x : ℂ) ha hz
    _ = complexUnitCircleMul (radialProjection 0 ⟨a, ha⟩)
          (unitAddCircleEquivComplexUnitCircle x) := by
      rw [radialProjection_zero_unit]

/-- A factorization into a nonzero constant, the standard circle, and a
continuous correction whose normalized image avoids `-1` has degree one.
This is the lift-theoretic form of the straight-line homotopy argument in
Lemma 5.3. -/
theorem hasComplexCircleDegree_one_of_factor
    (curve correction : UnitAddCircle → ℂ) (a : ℂ)
    (ha : a ≠ 0) (hcorrection : Continuous correction)
    (hcorrection_ne : ∀ x, correction x ≠ 0)
    (hfactor : ∀ x,
      curve x = a * (unitAddCircleEquivComplexUnitCircle x : ℂ) * correction x)
    (havoid : ∀ x,
      radialMap correction 0 hcorrection_ne x ≠
        (⟨(-1 : ℂ), by norm_num⟩ : ComplexUnitCircle)) :
    HasComplexCircleDegree (radialMap curve 0 (fun x ↦ by
      rw [hfactor x]
      exact mul_ne_zero (mul_ne_zero ha
        (norm_ne_zero_iff.mp (by
          rw [(unitAddCircleEquivComplexUnitCircle x).property]
          norm_num))) (hcorrection_ne x))) 1 := by
  have hlinear := hasComplexCircleDegree_linear a ha
  have hcorrectionDegree :
      HasComplexCircleDegree (radialMap correction 0 hcorrection_ne) 0 := by
    apply hasComplexCircleDegree_zero_of_avoids_cut
      (radialMap correction 0 hcorrection_ne)
      (continuous_radialMap correction 0 hcorrection_ne hcorrection)
      (1 / 2)
    intro x hx
    apply havoid x
    rw [unitAddCircleEquivComplexUnitCircle_half] at hx
    exact hx
  have hproduct := hlinear.mul hcorrectionDegree
  convert hproduct using 1
  funext x
  simp only [radialMap]
  have hlinear_ne :
      a * (unitAddCircleEquivComplexUnitCircle x : ℂ) ≠ 0 :=
    mul_ne_zero ha (norm_ne_zero_iff.mp (by
      rw [(unitAddCircleEquivComplexUnitCircle x).property]
      norm_num))
  calc
    radialProjection 0 ⟨curve x, by
        rw [hfactor x]
        exact mul_ne_zero hlinear_ne (hcorrection_ne x)⟩ =
        radialProjection 0
          ⟨a * (unitAddCircleEquivComplexUnitCircle x : ℂ) * correction x,
            mul_ne_zero hlinear_ne (hcorrection_ne x)⟩ := by
      apply Subtype.ext
      simp only [radialProjection]
      rw [hfactor x]
    _ = complexUnitCircleMul
          (radialProjection 0
            ⟨a * (unitAddCircleEquivComplexUnitCircle x : ℂ), hlinear_ne⟩)
          (radialProjection 0 ⟨correction x, hcorrection_ne x⟩) :=
      radialProjection_zero_mul
        (a * (unitAddCircleEquivComplexUnitCircle x : ℂ)) (correction x)
        hlinear_ne (hcorrection_ne x)

/-- The correction left after factoring the first harmonic out of a
positive-frequency Fourier polynomial. -/
def dominantHarmonicCorrection {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (x : UnitAddCircle) : ℂ :=
  1 + ∑ k, (a k / a₁) *
    (unitAddCircleEquivComplexUnitCircle x : ℂ) ^ (m k - 1)

theorem continuous_dominantHarmonicCorrection
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) :
    Continuous (dominantHarmonicCorrection a₁ m a) := by
  unfold dominantHarmonicCorrection
  have hz : Continuous (fun x : UnitAddCircle ↦
      (unitAddCircleEquivComplexUnitCircle x : ℂ)) :=
    continuous_subtype_val.comp unitAddCircleEquivComplexUnitCircle.continuous
  exact continuous_const.add (continuous_finset_sum Finset.univ fun k _ ↦
    continuous_const.mul (hz.pow (m k - 1)))

/-- Exact factorization of the Fourier curve by its first harmonic. -/
theorem dominantHarmonicCurve_factor
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (ha₁ : a₁ ≠ 0) (hm : ∀ k, 1 ≤ m k) (x : UnitAddCircle) :
    dominantHarmonicCurve a₁ m a
        (unitAddCircleEquivComplexUnitCircle x) =
      a₁ * (unitAddCircleEquivComplexUnitCircle x : ℂ) *
        dominantHarmonicCorrection a₁ m a x := by
  unfold dominantHarmonicCurve dominantHarmonicCorrection
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  have hmk : m k = (m k - 1) + 1 := (Nat.sub_add_cancel (hm k)).symm
  rw [hmk, pow_succ]
  field_simp [ha₁]
  ring

/-- Under ordinary (unweighted) strict dominance, the correction remains
strictly inside the open unit ball centered at `1`. -/
theorem dominantHarmonicCorrection_sub_one_norm_lt_one
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, ‖a k‖) < ‖a₁‖) (x : UnitAddCircle) :
    ‖dominantHarmonicCorrection a₁ m a x - 1‖ < 1 := by
  have ha₁norm : 0 < ‖a₁‖ := lt_of_le_of_lt
    (Finset.sum_nonneg fun k _ ↦ norm_nonneg (a k)) hdom
  have hratio : (∑ k, ‖a k‖) / ‖a₁‖ < 1 :=
    (div_lt_one ha₁norm).mpr hdom
  calc
    ‖dominantHarmonicCorrection a₁ m a x - 1‖ =
        ‖∑ k, (a k / a₁) *
          (unitAddCircleEquivComplexUnitCircle x : ℂ) ^ (m k - 1)‖ := by
      simp [dominantHarmonicCorrection]
    _ ≤ ∑ k, ‖(a k / a₁) *
          (unitAddCircleEquivComplexUnitCircle x : ℂ) ^ (m k - 1)‖ :=
      norm_sum_le _ _
    _ = ∑ k, ‖a k‖ / ‖a₁‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [norm_mul, norm_div, norm_pow,
        (unitAddCircleEquivComplexUnitCircle x).property, one_pow, mul_one]
    _ = (∑ k, ‖a k‖) / ‖a₁‖ := by rw [Finset.sum_div]
    _ < 1 := hratio

theorem dominantHarmonicCorrection_ne_zero
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, ‖a k‖) < ‖a₁‖) (x : UnitAddCircle) :
    dominantHarmonicCorrection a₁ m a x ≠ 0 := by
  intro hx
  have hbound := dominantHarmonicCorrection_sub_one_norm_lt_one
    a₁ m a hdom x
  rw [hx] at hbound
  norm_num at hbound

/-- The normalized correction cannot point in the negative-real
direction.  This makes its half-turn cut explicit. -/
theorem radial_dominantHarmonicCorrection_ne_neg_one
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, ‖a k‖) < ‖a₁‖) (x : UnitAddCircle) :
    radialMap (dominantHarmonicCorrection a₁ m a) 0
        (dominantHarmonicCorrection_ne_zero a₁ m a hdom) x ≠
      (⟨(-1 : ℂ), by norm_num⟩ : ComplexUnitCircle) := by
  intro hx
  let c := dominantHarmonicCorrection a₁ m a x
  have hcne : c ≠ 0 := dominantHarmonicCorrection_ne_zero a₁ m a hdom x
  have hval : c / (‖c‖ : ℂ) = -1 := by
    simpa [c, radialMap, radialProjection] using congrArg Subtype.val hx
  have hnormne : (‖c‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hcne)
  have hc : c = -(‖c‖ : ℂ) := by
    calc
      c = (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) := by
        exact (div_mul_cancel₀ c hnormne).symm
      _ = (-1 : ℂ) * (‖c‖ : ℂ) := by rw [hval]
      _ = -(‖c‖ : ℂ) := by ring
  have hnorm : ‖c - 1‖ = ‖c‖ + 1 := by
    have hdiff : c - 1 = -((‖c‖ + 1 : ℝ) : ℂ) := by
      calc
        c - 1 = -(‖c‖ : ℂ) - 1 := congrArg (fun z : ℂ ↦ z - 1) hc
        _ = -((‖c‖ + 1 : ℝ) : ℂ) := by
          push_cast
          ring
    rw [hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hbound := dominantHarmonicCorrection_sub_one_norm_lt_one
    a₁ m a hdom x
  change ‖c - 1‖ < 1 at hbound
  rw [hnorm] at hbound
  linarith [norm_nonneg c]

theorem dominantHarmonicCurve_ne_zero
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ k, 1 ≤ m k)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖)
    (x : UnitAddCircle) :
    dominantHarmonicCurve a₁ m a
      (unitAddCircleEquivComplexUnitCircle x) ≠ 0 := by
  have ha₁pos : 0 < ‖a₁‖ := lt_of_le_of_lt
    (Finset.sum_nonneg fun k _ ↦ mul_nonneg
      (Nat.cast_nonneg _) (norm_nonneg _)) hdom
  have ha₁ : a₁ ≠ 0 := norm_ne_zero_iff.mp ha₁pos.ne'
  have hdom' : (∑ k, ‖a k‖) < ‖a₁‖ :=
    (Finset.sum_le_sum fun k _ ↦ by
      have hmk : (1 : ℝ) ≤ m k := by exact_mod_cast hm k
      nlinarith [norm_nonneg (a k)]).trans_lt hdom
  rw [dominantHarmonicCurve_factor a₁ m a ha₁ hm x]
  exact mul_ne_zero (mul_ne_zero ha₁
    (norm_ne_zero_iff.mp (by
      rw [(unitAddCircleEquivComplexUnitCircle x).property]
      norm_num)))
    (dominantHarmonicCorrection_ne_zero a₁ m a hdom' x)

/-- A positive-frequency Fourier curve with a strictly dominant first
harmonic has winding degree `+1` about the origin. -/
theorem dominantHarmonicCurve_degree_one
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ k, 1 ≤ m k)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    HasComplexCircleDegree
      (radialMap
        (fun x : UnitAddCircle ↦ dominantHarmonicCurve a₁ m a
          (unitAddCircleEquivComplexUnitCircle x))
        0
        (dominantHarmonicCurve_ne_zero a₁ m a hm hdom))
      1 := by
  have ha₁pos : 0 < ‖a₁‖ := lt_of_le_of_lt
    (Finset.sum_nonneg fun k _ ↦ mul_nonneg
      (Nat.cast_nonneg _) (norm_nonneg _)) hdom
  have ha₁ : a₁ ≠ 0 := norm_ne_zero_iff.mp ha₁pos.ne'
  have hdom' : (∑ k, ‖a k‖) < ‖a₁‖ :=
    (Finset.sum_le_sum fun k _ ↦ by
      have hmk : (1 : ℝ) ≤ m k := by exact_mod_cast hm k
      nlinarith [norm_nonneg (a k)]).trans_lt hdom
  apply hasComplexCircleDegree_one_of_factor
    (fun x : UnitAddCircle ↦ dominantHarmonicCurve a₁ m a
      (unitAddCircleEquivComplexUnitCircle x))
    (dominantHarmonicCorrection a₁ m a) a₁ ha₁
    (continuous_dominantHarmonicCorrection a₁ m a)
    (dominantHarmonicCorrection_ne_zero a₁ m a hdom')
    (dominantHarmonicCurve_factor a₁ m a ha₁ hm)
    (radial_dominantHarmonicCorrection_ne_neg_one a₁ m a hdom')

end

end GromovFilling
