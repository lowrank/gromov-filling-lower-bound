import GromovFilling.NonlinearProfileFourierBridge

/-!
# Fourier correlation identities on an interval

This file supplies the one-dimensional inner-product form of Parseval's
identity and the shift-correlation consequences needed by the nonlinear
profile argument.  Mathlib's one-dimensional additive-circle file contains
norm Parseval, while the corresponding inner-product theorem is currently
only exposed for multidimensional additive tori; the proof below is the
same Hilbert-basis argument specialized to one dimension.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GromovFilling

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- Inner-product Parseval for square-integrable functions on an additive
circle. -/
theorem hasSum_prod_fourierCoeff
    {T : ℝ} [Fact (0 < T)]
    (f g : Lp ℂ 2 (@AddCircle.haarAddCircle T inferInstance)) :
    HasSum
      (fun i : ℤ ↦
        starRingEnd ℂ (fourierCoeff f i) * fourierCoeff g i)
      (∫ t : AddCircle T,
        starRingEnd ℂ (f t) * g t ∂AddCircle.haarAddCircle) := by
  simp_rw [mul_comm (starRingEnd ℂ _)]
  refine HasSum.congr_fun
    (fourierBasis.hasSum_inner_mul_inner f g) (fun n ↦ ?_)
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply,
    inner_conj_symm, mul_comm (inner ℂ f _)]

/-- Inner-product Parseval for functions square-integrable on `(a, b]`,
with the same normalized interval convention as `fourierCoeffOn`. -/
theorem hasSum_prod_fourierCoeffOn
    {a b : ℝ} {f g : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    HasSum
      (fun i : ℤ ↦
        starRingEnd ℂ (fourierCoeffOn hab f i) *
          fourierCoeffOn hab g i)
      ((b - a)⁻¹ •
        ∫ x in a..b, starRingEnd ℂ (f x) * g x) := by
  letI : Fact (0 < b - a) := ⟨by linarith⟩
  have hf' := hf
  have hg' := hg
  rw [← add_sub_cancel a b] at hf' hg'
  have hflift := hf'.memLp_liftIoc.haarAddCircle
  have hglift := hg'.memLp_liftIoc.haarAddCircle
  convert hasSum_prod_fourierCoeff hflift.toLp hglift.toLp using 1
  · simp [fourierCoeff_congr_ae hflift.coeFn_toLp,
      fourierCoeff_congr_ae hglift.coeFn_toLp,
      fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral]
    have hnormalize :
        (b - a)⁻¹ •
            ∫ t : AddCircle (b - a),
              AddCircle.liftIoc (b - a) a
                (fun x ↦ starRingEnd ℂ (f x) * g x) t =
          ∫ t : AddCircle (b - a),
            AddCircle.liftIoc (b - a) a
              (fun x ↦ starRingEnd ℂ (f x) * g x) t
              ∂AddCircle.haarAddCircle :=
      (AddCircle.integral_haarAddCircle (T := b - a)).symm
    rw [hnormalize]
    apply integral_congr_ae
    filter_upwards [hflift.coeFn_toLp, hglift.coeFn_toLp] with x hfx hgx
    rw [hfx, hgx]
    rfl

/-- Multiplication by a circle character shifts interval Fourier
coefficients by the corresponding integer. -/
theorem fourierCoeffOn_fourier_mul
    {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) (m n : ℤ) :
    fourierCoeffOn hab
        (fun x ↦ fourier m (x : AddCircle (b - a)) * f x) n =
      fourierCoeffOn hab f (n - m) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← fourier_add]
  rw [show -n + m = -(n - m) by omega]

private theorem fourierCoeffOn_const_one_ne_zero
    {a b : ℝ} (hab : a < b) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hab (fun _x : ℝ ↦ (1 : ℂ)) n = 0 := by
  have hzero :
      fourierCoeffOn hab (fun _x : ℝ ↦ (0 : ℂ)) n = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp
  rw [fourierCoeffOn_of_hasDerivAt
    (f' := fun _x : ℝ ↦ (0 : ℂ)) hab hn
    (fun x _hx ↦ hasDerivAt_const x 1)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _x : ℝ ↦ (0 : ℂ)) volume a b), hzero]
  simp

/-- A normalized interval Fourier coefficient is bounded by the normalized
integral of the pointwise norm. -/
theorem norm_fourierCoeffOn_le_normalized_integral_norm
    {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn hab f n‖ ≤
      (b - a)⁻¹ * ∫ x in a..b, ‖f x‖ := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hfactor : ‖(1 / (b - a) : ℝ)‖ = (b - a)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (sub_pos.mpr hab)),
      one_div]
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  calc
    ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤
        ∫ x in a..b,
          ‖fourier (-n) (x : AddCircle (b - a)) • f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab.le
    _ = ∫ x in a..b, ‖f x‖ := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change ‖fourier (-n) (x : AddCircle (b - a)) • f x‖ = ‖f x‖
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

private theorem fourierCoeffOn_sub
    {a b : ℝ} (hab : a < b) {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (n : ℤ) :
    fourierCoeffOn hab (fun x ↦ f x - g x) n =
      fourierCoeffOn hab f n - fourierCoeffOn hab g n := by
  have hchar : Continuous
      (fun x : ℝ ↦ fourier (-n) (x : AddCircle (b - a))) :=
    (map_continuous (fourier (-n))).comp
      (AddCircle.continuous_mk' (b - a))
  have hcharf : IntervalIntegrable
      (fun x ↦ fourier (-n) (x : AddCircle (b - a)) • f x)
      volume a b := hf.continuousOn_smul hchar.continuousOn
  have hcharg : IntervalIntegrable
      (fun x ↦ fourier (-n) (x : AddCircle (b - a)) • g x)
      volume a b := hg.continuousOn_smul hchar.continuousOn
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    fourierCoeffOn_eq_integral, ← smul_sub,
    ← intervalIntegral.integral_sub hcharf hcharg]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  change fourier (-n) (x : AddCircle (b - a)) • (f x - g x) =
    fourier (-n) (x : AddCircle (b - a)) • f x -
      fourier (-n) (x : AddCircle (b - a)) • g x
  rw [smul_sub]

/-- The shift-two coefficient correlation is the nonzero Fourier
coefficient of the pointwise squared norm. -/
theorem hasSum_shiftTwo_fourierCoeffOn
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) :
    HasSum
      (fun k : ℤ ↦
        fourierCoeffOn hab f k *
          starRingEnd ℂ (fourierCoeffOn hab f (k + 2)))
      ((b - a)⁻¹ •
        ∫ x in a..b,
          fourier (2 : ℤ) (x : AddCircle (b - a)) *
            (Complex.normSq (f x) : ℂ)) := by
  let modulated : ℝ → ℂ :=
    fun x ↦ fourier (-2 : ℤ) (x : AddCircle (b - a)) * f x
  have hmodMeas : AEStronglyMeasurable modulated
      (volume.restrict (Ioc a b)) := by
    exact (((map_continuous (fourier (-2 : ℤ))).comp
      (AddCircle.continuous_mk' (b - a))).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
  have hmodNorm : ∀ᵐ x ∂volume.restrict (Ioc a b),
      ‖modulated x‖ = ‖f x‖ := by
    filter_upwards [] with x
    unfold modulated
    rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  have hmod : MemLp modulated 2 (volume.restrict (Ioc a b)) :=
    hf.congr_norm hmodMeas (hmodNorm.mono fun _ hx ↦ hx.symm)
  have hparseval := hasSum_prod_fourierCoeffOn hab hmod hf
  convert hparseval using 1
  · funext k
    rw [fourierCoeffOn_fourier_mul hab f (-2 : ℤ) k]
    simp only [sub_neg_eq_add]
    ring
  · apply congrArg ((b - a)⁻¹ • ·)
    apply intervalIntegral.integral_congr
    intro x _hx
    have hchar :
        starRingEnd ℂ
            (fourier (-2 : ℤ) (x : AddCircle (b - a))) =
          fourier (2 : ℤ) (x : AddCircle (b - a)) := by
      rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, fourier_neg]
      simp
    simp only [modulated, map_mul]
    rw [hchar, mul_assoc, ← Complex.normSq_eq_conj_mul_self]

/-- The full shift-two coefficient correlation is exactly the `-2` Fourier
coefficient of the pointwise squared norm. -/
theorem tsum_shiftTwo_fourierCoeffOn_eq_normSqCoeff
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b))) :
    (∑' k : ℤ,
        fourierCoeffOn hab f k *
          starRingEnd ℂ (fourierCoeffOn hab f (k + 2))) =
      fourierCoeffOn hab (fun x ↦ (Complex.normSq (f x) : ℂ))
        (-2 : ℤ) := by
  rw [(hasSum_shiftTwo_fourierCoeffOn hab hf).tsum_eq,
    fourierCoeffOn_eq_integral]
  norm_num
  change ((b : ℂ) - (a : ℂ))⁻¹ * _ =
    (((b - a)⁻¹ : ℝ) : ℂ) * _
  rw [Complex.ofReal_inv]
  norm_num

/-- If the pointwise squared norm is at most one, its nonzero Fourier
coefficient is bounded by the normalized mean deficit. -/
theorem norm_normSq_fourierCoeffOn_le_meanDeficit
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc a b),
      Complex.normSq (f x) ≤ 1) :
    ‖fourierCoeffOn hab (fun x ↦ (Complex.normSq (f x) : ℂ))
        (-2 : ℤ)‖ ≤
      (b - a)⁻¹ *
        ∫ x in a..b, (1 - Complex.normSq (f x)) := by
  have hnormSqReal : IntervalIntegrable
      (fun x ↦ Complex.normSq (f x)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Complex.normSq_eq_norm_sq] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Ioc a b)) hf)
  have hnormSq : IntervalIntegrable
      (fun x ↦ (Complex.normSq (f x) : ℂ)) volume a b :=
    ⟨hnormSqReal.1.ofReal, hnormSqReal.2.ofReal⟩
  have hone : IntervalIntegrable (fun _x : ℝ ↦ (1 : ℂ)) volume a b :=
    (continuous_const : Continuous (fun _x : ℝ ↦ (1 : ℂ)))
      |>.intervalIntegrable a b
  let gap : ℝ → ℂ :=
    fun x ↦ ((1 - Complex.normSq (f x) : ℝ) : ℂ)
  have hgap : IntervalIntegrable gap volume a b := by
    simpa [gap] using hone.sub hnormSq
  have hsplit :
      fourierCoeffOn hab gap (-2 : ℤ) =
        -fourierCoeffOn hab
          (fun x ↦ (Complex.normSq (f x) : ℂ)) (-2 : ℤ) := by
    rw [show gap = (fun x ↦ (1 : ℂ) -
        (Complex.normSq (f x) : ℂ)) by
          funext x
          simp [gap],
      fourierCoeffOn_sub hab hone hnormSq,
      fourierCoeffOn_const_one_ne_zero hab (by norm_num)]
    ring
  have hgapNorm :
      (∫ x in a..b, ‖gap x‖) =
        ∫ x in a..b, (1 - Complex.normSq (f x)) := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le hab.le]
    filter_upwards [hunit] with x hx
    change ‖((1 - Complex.normSq (f x) : ℝ) : ℂ)‖ =
      1 - Complex.normSq (f x)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hx)]
  calc
    ‖fourierCoeffOn hab
        (fun x ↦ (Complex.normSq (f x) : ℂ)) (-2 : ℤ)‖ =
        ‖fourierCoeffOn hab gap (-2 : ℤ)‖ := by
      rw [hsplit, norm_neg]
    _ ≤ (b - a)⁻¹ * ∫ x in a..b, ‖gap x‖ :=
      norm_fourierCoeffOn_le_normalized_integral_norm hab gap (-2 : ℤ)
    _ = (b - a)⁻¹ *
        ∫ x in a..b, (1 - Complex.normSq (f x)) := by
      rw [hgapNorm]

/-- The exact full shift-two correlation obeys the manuscript's Fourier
deficit estimate. -/
theorem norm_tsum_shiftTwo_fourierCoeffOn_le_meanDeficit
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc a b),
      Complex.normSq (f x) ≤ 1) :
    ‖∑' k : ℤ,
        fourierCoeffOn hab f k *
          starRingEnd ℂ (fourierCoeffOn hab f (k + 2))‖ ≤
      (b - a)⁻¹ *
        ∫ x in a..b, (1 - Complex.normSq (f x)) := by
  rw [tsum_shiftTwo_fourierCoeffOn_eq_normSqCoeff hab hf]
  exact norm_normSq_fourierCoeffOn_le_meanDeficit hab hf hunit

/-- The two real tangent-profile columns therefore satisfy the exact full
shift-correlation deficit bound used by the nonlinear argument. -/
theorem norm_tsum_shiftTwo_complexTangentProfileField_le_meanDeficit
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Ioc a b)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Ioc a b)))
    (hjoint : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖(d₀ t : ℂ)‖ ^ 2 + ‖(d₁ t : ℂ)‖ ^ 2 ≤ 1) :
    ‖∑' k : ℤ,
        fourierCoeffOn hab (complexTangentProfileField d₀ d₁) k *
          starRingEnd ℂ
            (fourierCoeffOn hab (complexTangentProfileField d₀ d₁)
              (k + 2))‖ ≤
      (b - a)⁻¹ *
        ∫ x in a..b,
          (1 - Complex.normSq (complexTangentProfileField d₀ d₁ x)) := by
  have hfieldL2 : MemLp (complexTangentProfileField d₀ d₁) 2
      (volume.restrict (Ioc a b)) := by
    simpa [complexTangentProfileField] using
      hd₀L2.add (hd₁L2.const_mul Complex.I)
  have hfieldUnit : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Complex.normSq (complexTangentProfileField d₀ d₁ t) ≤ 1 := by
    filter_upwards [hjoint] with t ht
    simpa [complexTangentProfileField, Complex.normSq_apply,
      Complex.norm_real, sq_abs, pow_two] using ht
  exact norm_tsum_shiftTwo_fourierCoeffOn_le_meanDeficit
    hab hfieldL2 hfieldUnit

/-- On a saturated tangent profile, the full shift-two correlation vanishes
exactly.  This is the Fourier autocorrelation cancellation behind first-order
stationarity. -/
theorem tsum_shiftTwo_fourierCoeffOn_eq_zero_of_ae_normSq_eq_one
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc a b),
      Complex.normSq (f x) = 1) :
    (∑' k : ℤ,
        fourierCoeffOn hab f k *
          starRingEnd ℂ (fourierCoeffOn hab f (k + 2))) = 0 := by
  rw [tsum_shiftTwo_fourierCoeffOn_eq_normSqCoeff hab hf]
  have hae :
      (fun x ↦ (Complex.normSq (f x) : ℂ)) =ᵐ[
        volume.restrict (Ioc a b)] (fun _x : ℝ ↦ (1 : ℂ)) := by
    filter_upwards [hunit] with x hx
    rw [hx]
    norm_num
  rw [congrFun (fourierCoeffOn_congr_ae hab hae) (-2 : ℤ),
    fourierCoeffOn_const_one_ne_zero hab (by norm_num)]

end

end GromovFilling

#print axioms GromovFilling.hasSum_prod_fourierCoeff
#print axioms GromovFilling.hasSum_prod_fourierCoeffOn
#print axioms GromovFilling.fourierCoeffOn_fourier_mul
#print axioms GromovFilling.norm_fourierCoeffOn_le_normalized_integral_norm
#print axioms GromovFilling.hasSum_shiftTwo_fourierCoeffOn
#print axioms GromovFilling.tsum_shiftTwo_fourierCoeffOn_eq_normSqCoeff
#print axioms GromovFilling.norm_normSq_fourierCoeffOn_le_meanDeficit
#print axioms GromovFilling.norm_tsum_shiftTwo_fourierCoeffOn_le_meanDeficit
#print axioms GromovFilling.norm_tsum_shiftTwo_complexTangentProfileField_le_meanDeficit
#print axioms GromovFilling.tsum_shiftTwo_fourierCoeffOn_eq_zero_of_ae_normSq_eq_one
