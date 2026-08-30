import GromovFilling.InfiniteResonantComass

/-!
# Orientation reversal for the infinite resonant comass bound

The positive-base comass estimate is enough for every oriented tangent plane.
Indeed, conjugating the complex tangent-profile field keeps the first real
column and reverses the second.  On Fourier coefficients this conjugates and
reverses the mode index, swaps positive and negative odd energy, and negates
the base, first-order, quadratic, and full symplectic densities.  Absolute
values are therefore unchanged.
-/

open MeasureTheory Set

namespace GromovFilling

noncomputable section

private theorem fourierCoeff_star
    {T : ℝ} [Fact (0 < T)] (g : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (star g) n = star (fourierCoeff g (-n)) := by
  unfold fourierCoeff
  simp only [Pi.star_apply, neg_neg, smul_eq_mul]
  change (∫ t, fourier (-n) t * (starRingEnd ℂ) (g t)
      ∂AddCircle.haarAddCircle) =
    (starRingEnd ℂ)
      (∫ t, fourier n t * g t ∂AddCircle.haarAddCircle)
  calc
    (∫ t, fourier (-n) t * (starRingEnd ℂ) (g t)
        ∂AddCircle.haarAddCircle) =
        ∫ t, (starRingEnd ℂ) (fourier n t * g t)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [map_mul]
      simp
    _ = (starRingEnd ℂ)
        (∫ t, fourier n t * g t ∂AddCircle.haarAddCircle) :=
      integral_conj

/-- Conjugating an interval field conjugates its Fourier coefficients and
reverses the mode index. -/
theorem fourierCoeffOn_star
    {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hab (star f) n =
      star (fourierCoeffOn hab f (-n)) := by
  letI : Fact (0 < b - a) := ⟨by linarith⟩
  unfold fourierCoeffOn
  change fourierCoeff (star (AddCircle.liftIoc (b - a) a f)) n = _
  exact fourierCoeff_star _ _

/-- Reverse the Fourier mode and conjugate its coefficient. -/
def reverseConjugateCoefficients (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  star (c (-n))

/-- Fourier coefficients of the conjugate field are the reverse-conjugate
coefficients of the original field. -/
theorem fourierCoeffOn_star_eq_reverseConjugateCoefficients
    {a b : ℝ} (hab : a < b) (f : ℝ → ℂ) :
    (fun n ↦ fourierCoeffOn hab (star f) n) =
      reverseConjugateCoefficients (fun n ↦ fourierCoeffOn hab f n) := by
  funext n
  exact fourierCoeffOn_star hab f n

/-- Reverse-conjugation swaps positive and negative odd energy. -/
theorem infinitePositiveOddEnergy_reverseConjugate (c : ℤ → ℂ) :
    infinitePositiveOddEnergy (reverseConjugateCoefficients c) =
      infiniteNegativeOddEnergy c := by
  unfold infinitePositiveOddEnergy infiniteNegativeOddEnergy
    infiniteComplexEnergy reverseConjugateCoefficients
  apply tsum_congr
  intro k
  change Complex.normSq (star (c (-(oddMode k : ℤ)))) =
    Complex.normSq (c (-(oddMode k : ℤ)))
  simpa only [Complex.star_def] using
    Complex.normSq_conj (c (-(oddMode k : ℤ)))

/-- Reverse-conjugation swaps negative and positive odd energy. -/
theorem infiniteNegativeOddEnergy_reverseConjugate (c : ℤ → ℂ) :
    infiniteNegativeOddEnergy (reverseConjugateCoefficients c) =
      infinitePositiveOddEnergy c := by
  unfold infinitePositiveOddEnergy infiniteNegativeOddEnergy
    infiniteComplexEnergy reverseConjugateCoefficients
  apply tsum_congr
  intro k
  change Complex.normSq (star (c (-(-(oddMode k : ℤ))))) =
    Complex.normSq (c (oddMode k : ℤ))
  rw [neg_neg]
  simpa only [Complex.star_def] using
    Complex.normSq_conj (c (oddMode k : ℤ))

/-- The oriented base density changes sign under reverse-conjugation. -/
theorem infiniteOddBaseDensity_reverseConjugate (c : ℤ → ℂ) :
    infiniteOddBaseDensity (reverseConjugateCoefficients c) =
      -infiniteOddBaseDensity c := by
  unfold infiniteOddBaseDensity
  rw [infinitePositiveOddEnergy_reverseConjugate,
    infiniteNegativeOddEnergy_reverseConjugate]
  ring

/-- Positive shift correlation becomes negative shift correlation under
orientation reversal. -/
theorem infinitePositiveShiftCorrelation_reverseConjugate (c : ℤ → ℂ) :
    infinitePositiveShiftCorrelation (reverseConjugateCoefficients c) =
      infiniteNegativeShiftCorrelation c := by
  unfold infinitePositiveShiftCorrelation infiniteNegativeShiftCorrelation
  apply tsum_congr
  intro k
  simp only [reverseConjugateCoefficients, star_star]

/-- Negative shift correlation becomes positive shift correlation under
orientation reversal. -/
theorem infiniteNegativeShiftCorrelation_reverseConjugate (c : ℤ → ℂ) :
    infiniteNegativeShiftCorrelation (reverseConjugateCoefficients c) =
      infinitePositiveShiftCorrelation c := by
  unfold infinitePositiveShiftCorrelation infiniteNegativeShiftCorrelation
  apply tsum_congr
  intro k
  simp only [reverseConjugateCoefficients, neg_neg, star_star]

/-- The signed odd shift correlation changes sign under orientation
reversal. -/
theorem infiniteSignedOddShiftCorrelation_reverseConjugate (c : ℤ → ℂ) :
    infiniteSignedOddShiftCorrelation (reverseConjugateCoefficients c) =
      -infiniteSignedOddShiftCorrelation c := by
  unfold infiniteSignedOddShiftCorrelation
  rw [infinitePositiveShiftCorrelation_reverseConjugate,
    infiniteNegativeShiftCorrelation_reverseConjugate]
  ring

/-- The mixed correlation changes sign under orientation reversal. -/
theorem infiniteOddMixedCorrelation_reverseConjugate
    (y : ℕ → ℂ) (c : ℤ → ℂ) :
    infiniteOddMixedCorrelation y (reverseConjugateCoefficients c) =
      -infiniteOddMixedCorrelation y c := by
  unfold infiniteOddMixedCorrelation
  rw [← tsum_neg]
  apply tsum_congr
  intro k
  simp only [reverseConjugateCoefficients, neg_neg, star_star]
  ring

/-- The exact infinite first variation changes sign under orientation
reversal. -/
theorem infiniteResonantFirstVariation_reverseConjugate
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) :
    infiniteResonantFirstVariation a y (reverseConjugateCoefficients c) =
      -infiniteResonantFirstVariation a y c := by
  unfold infiniteResonantFirstVariation
  rw [infiniteSignedOddShiftCorrelation_reverseConjugate,
    infiniteOddMixedCorrelation_reverseConjugate]
  simp only [mul_neg, Complex.neg_re]
  ring

/-- Reversing both the Fourier orientation and the quadratic cluster value
negates the full infinite resonant density. -/
theorem infiniteResonantDensity_reverseConjugate
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (q : ℝ) :
    infiniteResonantDensity lam a y (reverseConjugateCoefficients c) (-q) =
      -infiniteResonantDensity lam a y c q := by
  unfold infiniteResonantDensity
  rw [infiniteOddBaseDensity_reverseConjugate,
    infiniteResonantFirstVariation_reverseConjugate]
  ring

/-- Conjugation preserves anti-periodicity. -/
theorem antiperiodic_star {f : ℝ → ℂ} {c : ℝ}
    (hf : Function.Antiperiodic f c) :
    Function.Antiperiodic (star f) c := by
  intro x
  simpa using congrArg star (hf x)

/-- Full sign-independent infinite Fourier comass estimate.  The negative
base branch is reduced to the positive branch by conjugating the tangent
profile field, which reverses the second oriented tangent column. -/
theorem abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi)
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam a y
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      comassBound lam := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  by_cases hbase0 : 0 ≤ infiniteOddBaseDensity c
  · simpa [c] using
      abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound_of_base_nonneg
        lam a y f q hlam0 hlam hy hf hanti hunit hprofile hapi hbase0 hq
  · let f' : ℝ → ℂ := star f
    let c' : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f' n
    have hf' : MemLp f' 2
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
      simpa [f'] using hf.star
    have hanti' : Function.Antiperiodic f' Real.pi := by
      simpa [f'] using antiperiodic_star hanti
    have hunit' : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
        Complex.normSq (f' x) ≤ 1 := by
      filter_upwards [hunit] with x hx
      simpa only [f', Pi.star_apply, Complex.star_def,
        Complex.normSq_conj] using hx
    have hc' : c' = reverseConjugateCoefficients c := by
      simpa [c', c, f'] using
        fourierCoeffOn_star_eq_reverseConjugateCoefficients hab f
    have hbase' : 0 ≤ infiniteOddBaseDensity c' := by
      rw [hc', infiniteOddBaseDensity_reverseConjugate]
      exact neg_nonneg.mpr (le_of_not_ge hbase0)
    have hq' : |-q| ≤ Qstar := by simpa only [abs_neg] using hq
    have hbound :=
      abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound_of_base_nonneg
        lam a y f' (-q) hlam0 hlam hy hf' hanti' hunit'
          hprofile hapi (by simpa [c'] using hbase') hq'
    change |infiniteResonantDensity lam a y c q| ≤ comassBound lam
    change |infiniteResonantDensity lam a y c' (-q)| ≤
      comassBound lam at hbound
    rw [hc', infiniteResonantDensity_reverseConjugate] at hbound
    simpa only [abs_neg] using hbound

/-- All scalar-profile hypotheses in the sign-independent infinite comass
bound are automatic for the genuine odd distance profile. -/
theorem abs_infiniteResonantDensity_oddProfile_le_comassBound
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X)
    (lam : ℝ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f t) ≤ 1)
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam
        (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      comassBound lam := by
  exact abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound
    lam (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      f q hlam0 hlam
      (summable_normSq_oddProfileFourierMap_tail hboundary x)
      hf hanti hunit
      (oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
        hboundary x)
      (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)
      hq

end

end GromovFilling

#print axioms GromovFilling.fourierCoeffOn_star
#print axioms GromovFilling.fourierCoeffOn_star_eq_reverseConjugateCoefficients
#print axioms GromovFilling.infinitePositiveOddEnergy_reverseConjugate
#print axioms GromovFilling.infiniteNegativeOddEnergy_reverseConjugate
#print axioms GromovFilling.infiniteOddBaseDensity_reverseConjugate
#print axioms GromovFilling.infinitePositiveShiftCorrelation_reverseConjugate
#print axioms GromovFilling.infiniteNegativeShiftCorrelation_reverseConjugate
#print axioms GromovFilling.infiniteSignedOddShiftCorrelation_reverseConjugate
#print axioms GromovFilling.infiniteOddMixedCorrelation_reverseConjugate
#print axioms GromovFilling.infiniteResonantFirstVariation_reverseConjugate
#print axioms GromovFilling.infiniteResonantDensity_reverseConjugate
#print axioms GromovFilling.antiperiodic_star
#print axioms GromovFilling.abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound
#print axioms GromovFilling.abs_infiniteResonantDensity_oddProfile_le_comassBound
