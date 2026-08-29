import GromovFilling.FourierCorrelation

/-!
# Odd-frequency decomposition of the infinite Fourier correlation

This file turns the full integer-index shift-two autocorrelation into the
positive odd, negative odd, and crossing terms used in the manuscript.
Antiperiodicity of the tangent-profile field is used to eliminate every even
Fourier coefficient, so the decomposition applies directly to the genuine
distance-profile data rather than to a finite surrogate.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GromovFilling

noncomputable section

/-- The complex field assembled from two real antiperiodic columns is itself
antiperiodic. -/
theorem complexTangentProfileField_antiperiodic
    {d₀ d₁ : ℝ → ℝ} {T : ℝ}
    (hd₀ : Function.Antiperiodic d₀ T)
    (hd₁ : Function.Antiperiodic d₁ T) :
    Function.Antiperiodic (complexTangentProfileField d₀ d₁) T := by
  intro t
  simp only [complexTangentProfileField, hd₀ t, hd₁ t]
  push_cast
  ring

private theorem intervalIntegral_eq_zero_of_antiperiodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (T a : ℝ) (hg : Function.Antiperiodic g T)
    (hint : ∀ u v, IntervalIntegrable g volume u v) :
    (∫ x in a..a + 2 * T, g x) = 0 := by
  calc
    (∫ x in a..a + 2 * T, g x) =
        (∫ x in a..a + T, g x) +
          ∫ x in a + T..a + 2 * T, g x := by
      rw [show a + 2 * T = (a + T) + T by ring]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hint a (a + T)) (hint (a + T) ((a + T) + T))).symm
    _ = (∫ x in a..a + T, g x) +
          ∫ x in a..a + T, g (x + T) := by
      rw [intervalIntegral.integral_comp_add_right]
      congr 2
      ring
    _ = (∫ x in a..a + T, g x) +
          ∫ x in a..a + T, -g x := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hg x
    _ = 0 := by
      rw [intervalIntegral.integral_neg]
      abel

private theorem fourier_character_periodic_pi_of_even
    (n : ℤ) (hn : Even n) :
    Function.Periodic
      (fun x : ℝ ↦ fourier (-n)
        (x : AddCircle (Real.pi - -Real.pi))) Real.pi := by
  rcases hn with ⟨m, rfl⟩
  intro x
  simp only [fourier_coe_apply]
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * (-(m + m) : ℤ) *
              ((x + Real.pi : ℝ) : ℂ) /
            ((Real.pi - -Real.pi : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (-(m + m) : ℤ) * (x : ℂ) /
              ((Real.pi - -Real.pi : ℝ) : ℂ) +
          (-m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast
        field_simp [Real.pi_ne_zero]
        ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Every even Fourier coefficient of an antiperiodic `L²` field on
`[-π, π]` vanishes. -/
theorem fourierCoeffOn_eq_zero_of_antiperiodic_of_even
    (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (n : ℤ) (hn : Even n) :
    fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
      f n = 0 := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let g : ℝ → ℂ := fun x ↦
    fourier (-n) (x : AddCircle (Real.pi - -Real.pi)) • f x
  have hchar := fourier_character_periodic_pi_of_even n hn
  have hganti : Function.Antiperiodic g Real.pi := by
    intro x
    simp only [g]
    change
      (fun y : ℝ ↦ fourier (-n)
        (y : AddCircle (Real.pi - -Real.pi))) (x + Real.pi) •
          f (x + Real.pi) = _
    rw [hchar x, hanti x]
    exact smul_neg _ _
  have hfInt : IntervalIntegrable f volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact hf.integrable (by norm_num)
  have hcharCont : Continuous
      (fun x : ℝ ↦ fourier (-n)
        (x : AddCircle (Real.pi - -Real.pi))) :=
    (map_continuous (fourier (-n))).comp
      (AddCircle.continuous_mk' (Real.pi - -Real.pi))
  have hgInt : IntervalIntegrable g volume (-Real.pi) Real.pi :=
    hfInt.continuousOn_smul hcharCont.continuousOn
  have hgIntAll : ∀ u v, IntervalIntegrable g volume u v := by
    have hgBase : IntervalIntegrable g volume (-Real.pi)
        ((-Real.pi) + (2 : ℕ) • Real.pi) := by
      convert hgInt using 1
      ring
    intro u v
    exact hganti.periodic.intervalIntegrable
      (by simp [Real.pi_ne_zero]) hgBase u v
  have hzero : (∫ x in (-Real.pi)..Real.pi, g x) = 0 := by
    convert intervalIntegral_eq_zero_of_antiperiodic
      g Real.pi (-Real.pi) hganti hgIntAll using 1
    ring
  rw [fourierCoeffOn_eq_integral]
  change (1 / (Real.pi - -Real.pi)) •
    (∫ x in (-Real.pi)..Real.pi, g x) = 0
  simp [hzero]

/-- The actual two-column tangent-profile field has no even Fourier modes. -/
theorem fourierCoeffOn_complexTangentProfileField_eq_zero_of_even
    (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd₀anti : Function.Antiperiodic d₀ Real.pi)
    (hd₁anti : Function.Antiperiodic d₁ Real.pi)
    (n : ℤ) (hn : Even n) :
    fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
      (complexTangentProfileField d₀ d₁) n = 0 := by
  have hfieldL2 : MemLp (complexTangentProfileField d₀ d₁) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa [complexTangentProfileField] using
      hd₀L2.add (hd₁L2.const_mul Complex.I)
  exact fourierCoeffOn_eq_zero_of_antiperiodic_of_even
    (complexTangentProfileField d₀ d₁) hfieldL2
      (complexTangentProfileField_antiperiodic hd₀anti hd₁anti) n hn

/-- Positive odd-frequency part of the infinite shift-two correlation. -/
def infinitePositiveShiftCorrelation (c : ℤ → ℂ) : ℂ :=
  ∑' k : ℕ,
    c (oddMode k : ℤ) * star (c (oddMode (k + 1) : ℤ))

/-- Negative odd-frequency part of the infinite shift-two correlation, in
the manuscript convention. -/
def infiniteNegativeShiftCorrelation (c : ℤ → ℂ) : ℂ :=
  ∑' k : ℕ,
    star (c (-(oddMode k : ℤ))) * c (-(oddMode (k + 1) : ℤ))

/-- Full shift-two correlation after separating positive odd frequencies,
negative odd frequencies, and the crossing pair `(-1, 1)`. -/
def infiniteFullOddShiftCorrelation (c : ℤ → ℂ) : ℂ :=
  infinitePositiveShiftCorrelation c + infiniteNegativeShiftCorrelation c +
    c (-1) * star (c 1)

/-- Signed same-direction correlation appearing in the exact first
variation. -/
def infiniteSignedOddShiftCorrelation (c : ℤ → ℂ) : ℂ :=
  infinitePositiveShiftCorrelation c - infiniteNegativeShiftCorrelation c

private theorem tsum_natCast_shiftTwo_eq_infinitePositive_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable
      (fun n : ℕ ↦ c (n : ℤ) * star (c ((n : ℤ) + 2))))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' n : ℕ, c (n : ℤ) * star (c ((n : ℤ) + 2))) =
      infinitePositiveShiftCorrelation c := by
  let corr : ℕ → ℂ :=
    fun n ↦ c (n : ℤ) * star (c ((n : ℤ) + 2))
  have hEven : Summable (fun k : ℕ ↦ corr (2 * k)) := by
    simpa [corr, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k) by
        intro m n hmn
        change 2 * m = 2 * n at hmn
        omega)
  have hOdd : Summable (fun k : ℕ ↦ corr (2 * k + 1)) := by
    simpa [corr, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k + 1) by
        intro m n hmn
        change 2 * m + 1 = 2 * n + 1 at hmn
        omega)
  have hEvenZero : (∑' k : ℕ, corr (2 * k)) = 0 := by
    calc
      (∑' k : ℕ, corr (2 * k)) = ∑' _k : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro k
        unfold corr
        rw [heven (((2 * k : ℕ) : ℤ))]
        · simp
        · exact ⟨(k : ℤ), by push_cast; ring⟩
      _ = 0 := tsum_zero
  have hOddEq : (∑' k : ℕ, corr (2 * k + 1)) =
      infinitePositiveShiftCorrelation c := by
    unfold infinitePositiveShiftCorrelation
    apply tsum_congr
    intro k
    unfold corr oddMode
    push_cast
    congr 2
  calc
    (∑' n : ℕ, c (n : ℤ) * star (c ((n : ℤ) + 2))) =
        ∑' n : ℕ, corr n := rfl
    _ = (∑' k : ℕ, corr (2 * k)) +
          ∑' k : ℕ, corr (2 * k + 1) :=
      (tsum_even_add_odd hEven hOdd).symm
    _ = infinitePositiveShiftCorrelation c := by
      rw [hEvenZero, zero_add, hOddEq]

private theorem tsum_negSucc_shiftTwo_eq_cross_add_infiniteNegative_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable (fun n : ℕ ↦
      c (-((n : ℤ) + 1)) * star (c (-((n : ℤ) + 1) + 2))))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' n : ℕ,
        c (-((n : ℤ) + 1)) * star (c (-((n : ℤ) + 1) + 2))) =
      c (-1) * star (c 1) + infiniteNegativeShiftCorrelation c := by
  let corr : ℕ → ℂ := fun n ↦
    c (-((n : ℤ) + 1)) * star (c (-((n : ℤ) + 1) + 2))
  have hEven : Summable (fun k : ℕ ↦ corr (2 * k)) := by
    simpa [corr, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k) by
        intro m n hmn
        change 2 * m = 2 * n at hmn
        omega)
  have hOdd : Summable (fun k : ℕ ↦ corr (2 * k + 1)) := by
    simpa [corr, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k + 1) by
        intro m n hmn
        change 2 * m + 1 = 2 * n + 1 at hmn
        omega)
  have hOddZero : (∑' k : ℕ, corr (2 * k + 1)) = 0 := by
    calc
      (∑' k : ℕ, corr (2 * k + 1)) = ∑' _k : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro k
        unfold corr
        have hidx : -(((2 * k + 1 : ℕ) : ℤ) + 1) =
            -2 * ((k : ℤ) + 1) := by push_cast; ring
        rw [heven (-(((2 * k + 1 : ℕ) : ℤ) + 1))]
        · simp
        · exact ⟨-((k : ℤ) + 1), by rw [hidx]; ring⟩
      _ = 0 := tsum_zero
  have hEvenEq : (∑' k : ℕ, corr (2 * k)) =
      c (-1) * star (c 1) + infiniteNegativeShiftCorrelation c := by
    rw [hEven.tsum_eq_zero_add]
    unfold infiniteNegativeShiftCorrelation
    change c (-1) * star (c 1) +
        (∑' b : ℕ, corr (2 * (b + 1))) =
      c (-1) * star (c 1) +
        ∑' k : ℕ, star (c (-(oddMode k : ℤ))) *
          c (-(oddMode (k + 1) : ℤ))
    congr 1
    apply tsum_congr
    intro k
    unfold corr oddMode
    push_cast
    ring_nf
  calc
    (∑' n : ℕ,
        c (-((n : ℤ) + 1)) * star (c (-((n : ℤ) + 1) + 2))) =
        ∑' n : ℕ, corr n := rfl
    _ = (∑' k : ℕ, corr (2 * k)) +
          ∑' k : ℕ, corr (2 * k + 1) :=
      (tsum_even_add_odd hEven hOdd).symm
    _ = c (-1) * star (c 1) +
        infiniteNegativeShiftCorrelation c := by
      rw [hEvenEq, hOddZero, add_zero]

/-- If the even coefficients vanish, the full integer-index shift-two
correlation is exactly the sum of the positive odd, negative odd, and crossing
terms. -/
theorem tsum_shiftTwo_eq_infiniteFullOddShiftCorrelation_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable (fun k : ℤ ↦ c k * star (c (k + 2))))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' k : ℤ, c k * star (c (k + 2))) =
      infiniteFullOddShiftCorrelation c := by
  let corr : ℤ → ℂ := fun k ↦ c k * star (c (k + 2))
  have hnat : Summable (fun n : ℕ ↦ corr (n : ℤ)) := by
    simpa [corr, Function.comp_def] using
      hc.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ ↦ corr (-((n : ℤ) + 1))) := by
    have hinj : Function.Injective
        (fun n : ℕ ↦ (-((n : ℤ) + 1) : ℤ)) := by
      intro m n hmn
      change -((m : ℤ) + 1) = -((n : ℤ) + 1) at hmn
      omega
    simpa [corr, Function.comp_def] using hc.comp_injective hinj
  have hpos : (∑' n : ℕ, corr (n : ℤ)) =
      infinitePositiveShiftCorrelation c := by
    exact tsum_natCast_shiftTwo_eq_infinitePositive_of_even_vanishes
      c (by simpa [corr] using hnat) heven
  have hnegative : (∑' n : ℕ, corr (-((n : ℤ) + 1))) =
      c (-1) * star (c 1) + infiniteNegativeShiftCorrelation c := by
    exact tsum_negSucc_shiftTwo_eq_cross_add_infiniteNegative_of_even_vanishes
      c (by simpa [corr] using hneg) heven
  change (∑' k : ℤ, corr k) = _
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hpos, hnegative]
  unfold infiniteFullOddShiftCorrelation
  ring

/-- The genuine antiperiodic interval Fourier field satisfies the exact odd
decomposition of its full shift-two correlation. -/
theorem tsum_shiftTwo_fourierCoeffOn_eq_infiniteFullOddShiftCorrelation
    (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi) :
    (∑' k : ℤ,
        fourierCoeffOn
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f k *
          star (fourierCoeffOn
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f (k + 2))) =
      infiniteFullOddShiftCorrelation
        (fun k ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f k) := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  apply tsum_shiftTwo_eq_infiniteFullOddShiftCorrelation_of_even_vanishes
  · exact (hasSum_shiftTwo_fourierCoeffOn hab hf).summable
  · intro k hk
    exact fourierCoeffOn_eq_zero_of_antiperiodic_of_even f hf hanti k hk

/-- The decomposed odd-frequency correlation inherits the exact normalized
mean-deficit bound. -/
theorem norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_meanDeficit
    (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1) :
    ‖infiniteFullOddShiftCorrelation
        (fun k ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f k)‖ ≤
      (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi, (1 - Complex.normSq (f x)) := by
  rw [← tsum_shiftTwo_fourierCoeffOn_eq_infiniteFullOddShiftCorrelation
    f hf hanti]
  exact norm_tsum_shiftTwo_fourierCoeffOn_le_meanDeficit
    (by linarith [Real.pi_pos]) hf hunit

/-- The actual two-column tangent profile satisfies the manuscript's full
odd-correlation deficit estimate. -/
theorem norm_infiniteFullOddShiftCorrelation_complexTangentProfileField_le_meanDeficit
    (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hd₀anti : Function.Antiperiodic d₀ Real.pi)
    (hd₁anti : Function.Antiperiodic d₁ Real.pi)
    (hjoint : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      ‖(d₀ t : ℂ)‖ ^ 2 + ‖(d₁ t : ℂ)‖ ^ 2 ≤ 1) :
    ‖infiniteFullOddShiftCorrelation
        (fun k ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (complexTangentProfileField d₀ d₁) k)‖ ≤
      (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi,
          (1 - Complex.normSq (complexTangentProfileField d₀ d₁ x)) := by
  have hfieldL2 : MemLp (complexTangentProfileField d₀ d₁) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa [complexTangentProfileField] using
      hd₀L2.add (hd₁L2.const_mul Complex.I)
  have hfieldUnit : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (complexTangentProfileField d₀ d₁ t) ≤ 1 := by
    filter_upwards [hjoint] with t ht
    simpa [complexTangentProfileField, Complex.normSq_apply,
      Complex.norm_real, sq_abs, pow_two] using ht
  exact norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_meanDeficit
    (complexTangentProfileField d₀ d₁) hfieldL2
      (complexTangentProfileField_antiperiodic hd₀anti hd₁anti) hfieldUnit

end

end GromovFilling

#print axioms GromovFilling.complexTangentProfileField_antiperiodic
#print axioms GromovFilling.fourierCoeffOn_eq_zero_of_antiperiodic_of_even
#print axioms GromovFilling.fourierCoeffOn_complexTangentProfileField_eq_zero_of_even
#print axioms GromovFilling.tsum_shiftTwo_eq_infiniteFullOddShiftCorrelation_of_even_vanishes
#print axioms GromovFilling.tsum_shiftTwo_fourierCoeffOn_eq_infiniteFullOddShiftCorrelation
#print axioms GromovFilling.norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_meanDeficit
#print axioms GromovFilling.norm_infiniteFullOddShiftCorrelation_complexTangentProfileField_le_meanDeficit
