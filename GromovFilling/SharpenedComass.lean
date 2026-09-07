import GromovFilling.SharpenedInfiniteVariation
import GromovFilling.InfiniteResonantComassLimit

/-!
# The revised first variation and comass bound

These bounds retain the full Fourier field, including both orientations.
The additional profile input is the energy of frequencies five and above.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace GromovFilling

noncomputable section

private lemma abs_two_re_add_four_re_le_infinite (u v : ℂ) :
    |2 * u.re + 4 * v.re| ≤ 2 * ‖u‖ + 4 * ‖v‖ := by
  calc
    |2 * u.re + 4 * v.re| ≤ |2 * u.re| + |4 * v.re| := abs_add_le _ _
    _ = 2 * |u.re| + 4 * |v.re| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * ‖u‖ + 4 * ‖v‖ := by
      gcongr
      · exact Complex.abs_re_le_norm u
      · exact Complex.abs_re_le_norm v

/-- Direct infinite first-variation estimate before normalizing the square
root of the deficit. -/
theorem abs_infiniteResonantFirstVariation_le_cancelled_raw
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (delta : ℝ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1)
    (hFull :
      ‖infiniteFullOddShiftCorrelation c‖ ≤
        delta - 2 * infiniteNegativeOddEnergy c) :
    |infiniteResonantFirstVariation a y c| ≤
      2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
        4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
          Real.sqrt (delta / 2) := by
  let negEnergy := infiniteNegativeOddEnergy c
  have hnegNonneg : 0 ≤ negEnergy := infiniteComplexEnergy_nonneg _
  have hnegDelta : negEnergy ≤ delta / 2 := by
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hsqrtNeg : Real.sqrt negEnergy ≤ Real.sqrt (delta / 2) :=
    Real.sqrt_le_sqrt hnegDelta
  have hshift :=
    norm_infiniteSignedOddShiftCorrelation_le_delta_add_sqrt
      c delta hpos hneg hPos hFull
  have hmixed := norm_infiniteOddMixedCorrelation_le_cancelled
    y c hy hpos hneg hPos
  unfold infiniteResonantFirstVariation
  calc
    |2 * (star a ^ 2 * infiniteSignedOddShiftCorrelation c).re +
        4 * (star a * infiniteOddMixedCorrelation y c).re| ≤
        2 * ‖star a ^ 2 * infiniteSignedOddShiftCorrelation c‖ +
          4 * ‖star a * infiniteOddMixedCorrelation y c‖ :=
      abs_two_re_add_four_re_le_infinite _ _
    _ = 2 * ‖a‖ ^ 2 * ‖infiniteSignedOddShiftCorrelation c‖ +
          4 * ‖a‖ * ‖infiniteOddMixedCorrelation y c‖ := by
      simp only [norm_mul, norm_pow, norm_star]
      ring
    _ ≤ 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ *
            (Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
              Real.sqrt negEnergy) := by gcongr
    _ ≤ 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ *
            (Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
              Real.sqrt (delta / 2)) := by gcongr
    _ = 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
            Real.sqrt (delta / 2) := by ring

private lemma sqrt_div_two_eq_infinite
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    Real.sqrt (delta / 2) = Real.sqrt 2 * Real.sqrt delta / 2 := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  have hhalf : 0 ≤ delta / 2 := by positivity
  have hsHalf := Real.sq_sqrt hhalf
  have hsDelta := Real.sq_sqrt hdelta
  have hsTwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- Infinite first-variation bound in the manuscript's exact quantitative
form. -/
theorem abs_infiniteResonantFirstVariation_le_cancelled_manuscript
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (delta : ℝ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1)
    (hFull :
      ‖infiniteFullOddShiftCorrelation c‖ ≤
        delta - 2 * infiniteNegativeOddEnergy c) :
    |infiniteResonantFirstVariation a y c| ≤
      2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 + 2 * ‖a‖ * Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1)))) *
          Real.sqrt delta := by
  have hdelta : 0 ≤ delta := by
    have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg _
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hraw := abs_infiniteResonantFirstVariation_le_cancelled_raw
    a y c delta hy hpos hneg hPos hFull
  calc
    |infiniteResonantFirstVariation a y c| ≤
        2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1))) *
            Real.sqrt (delta / 2) := hraw
    _ = 2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 + 2 * ‖a‖ * Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1)))) *
          Real.sqrt delta := by
      rw [sqrt_div_two_eq_infinite delta hdelta]
      ring

/-- The infinite first variation feeds into the verified sharp scalar
constants without any finite-truncation loss. -/
theorem abs_infiniteResonantFirstVariation_le_sharpenedCstar_Dstar
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (delta : ℝ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1)
    (hFull :
      ‖infiniteFullOddShiftCorrelation c‖ ≤
        delta - 2 * infiniteNegativeOddEnergy c)
    (hprofile : ‖a‖ ^ 2 + 25 * infiniteComplexEnergy (fun k ↦ y (k + 1)) ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |infiniteResonantFirstVariation a y c| ≤
      sharpenedCstar * Real.sqrt delta + Dstar * delta := by
  have hdelta : 0 ≤ delta := by
    have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg _
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hySq := Real.sq_sqrt (infiniteComplexEnergy_nonneg (fun k ↦ y (k + 1)))
  apply firstVariation_le_sharpenedCstar_Dstar
    ‖a‖ (Real.sqrt (infiniteComplexEnergy (fun k ↦ y (k + 1)))) delta
      (infiniteResonantFirstVariation a y c)
      (norm_nonneg a) hdelta
  · simpa only [hySq] using hprofile
  · exact hapi
  · exact abs_infiniteResonantFirstVariation_le_cancelled_manuscript
      a y c delta hy hpos hneg hPos hFull

/-- The genuine Fourier first variation satisfies the verified sharp
`Cstar`, `Dstar` estimate. -/
theorem abs_infiniteResonantFirstVariation_fourierCoeffOn_le_sharpenedCstar_Dstar
    (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 25 * infiniteComplexEnergy (fun k ↦ y (k + 1)) ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    let delta := infiniteOddOrientedDeficit c
    |infiniteResonantFirstVariation a y c| ≤
      sharpenedCstar * Real.sqrt delta + Dstar * delta := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  have hpos' : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))) := by
    simpa [c] using hpos
  have hneg' : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))) := by
    simpa [c] using hneg
  have hFull :
      ‖infiniteFullOddShiftCorrelation c‖ ≤
        infiniteOddOrientedDeficit c -
          2 * infiniteNegativeOddEnergy c := by
    simpa [c] using
      norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_deficit_sub_two_neg
        f hf hanti hunit
  have hPos : infinitePositiveOddEnergy c ≤ 1 := by
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg _
    unfold infiniteOddOrientedDeficit infiniteOddBaseDensity at hFull
    linarith
  change |infiniteResonantFirstVariation a y c| ≤ _
  exact abs_infiniteResonantFirstVariation_le_sharpenedCstar_Dstar
    a y c (infiniteOddOrientedDeficit c)
      hy hpos' hneg' hPos hFull hprofile hapi

theorem abs_base_add_lam_first_add_lam_sq_quadratic_le_sharpenedComassBound
    (lam base first quadratic : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hbase : |base| ≤ 1)
    (hfirst : |first| ≤
      sharpenedCstar * Real.sqrt (1 - |base|) + Dstar * (1 - |base|))
    (hquadratic : |quadratic| ≤ Qstar) :
    |base + lam * first + lam ^ 2 * quadratic| ≤ sharpenedComassBound lam := by
  let delta : ℝ := 1 - |base|
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    linarith
  have homega :
      |base + lam * first + lam ^ 2 * quadratic| ≤
        1 - delta +
          lam * (sharpenedCstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by
    calc
      |base + lam * first + lam ^ 2 * quadratic| ≤
          |base| + |lam * first| + |lam ^ 2 * quadratic| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |base| + lam * |first| + lam ^ 2 * |quadratic| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam0,
          abs_of_nonneg (sq_nonneg lam)]
      _ ≤ |base| +
          lam * (sharpenedCstar * Real.sqrt delta + Dstar * delta) +
          lam ^ 2 * Qstar := by
        gcongr
      _ = 1 - delta +
          lam * (sharpenedCstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by
        dsimp only [delta]
        ring
  simpa only [sharpenedComassBound] using
    nonlinear_comass_optimization lam sharpenedCstar Dstar Qstar
      (base + lam * first + lam ^ 2 * quadratic) delta hdelta
      (comass_denominator_pos_of_admissible hlam) homega

/-- Positive-base branch of the genuine infinite Fourier comass estimate.
The negative-base branch is obtained geometrically by reversing the ordered
orthonormal frame. -/
theorem abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound_of_base_nonneg
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 25 * infiniteComplexEnergy (fun k ↦ y (k + 1)) ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi)
    (hbase0 : 0 ≤ infiniteOddBaseDensity
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n))
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam a y
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      sharpenedComassBound lam := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1 := by
    simpa [c] using
      infiniteOddEnergies_fourierCoeffOn_le_one f hf hanti hunit
  have hbaseLe : infiniteOddBaseDensity c ≤ 1 := by
    unfold infiniteOddBaseDensity
    have hneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg (fun k ↦ c (-(oddMode k : ℤ)))
    linarith
  have hbaseAbs : |infiniteOddBaseDensity c| ≤ 1 := by
    rw [abs_of_nonneg (by simpa [c] using hbase0)]
    exact hbaseLe
  have hfirst :=
    abs_infiniteResonantFirstVariation_fourierCoeffOn_le_sharpenedCstar_Dstar
      a y f hy hf hanti hunit hprofile hapi
  have hfirst' :
      |infiniteResonantFirstVariation a y c| ≤
        sharpenedCstar * Real.sqrt (1 - |infiniteOddBaseDensity c|) +
          Dstar * (1 - |infiniteOddBaseDensity c|) := by
    have hbaseAbs : |infiniteOddBaseDensity c| =
        infiniteOddBaseDensity c :=
      abs_of_nonneg (by simpa [c] using hbase0)
    rw [hbaseAbs]
    simpa [c, infiniteOddOrientedDeficit] using hfirst
  change |infiniteResonantDensity lam a y c q| ≤ sharpenedComassBound lam
  unfold infiniteResonantDensity
  exact abs_base_add_lam_first_add_lam_sq_quadratic_le_sharpenedComassBound
    lam (infiniteOddBaseDensity c)
      (infiniteResonantFirstVariation a y c) q
      hlam0 hlam hbaseAbs hfirst' hq

/-- Full sign-independent infinite Fourier comass estimate.  The negative
base branch is reduced to the positive branch by conjugating the tangent
profile field, which reverses the second oriented tangent column. -/
theorem abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 25 * infiniteComplexEnergy (fun k ↦ y (k + 1)) ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi)
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam a y
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      sharpenedComassBound lam := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  by_cases hbase0 : 0 ≤ infiniteOddBaseDensity c
  · simpa [c] using
      abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound_of_base_nonneg
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
      abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound_of_base_nonneg
        lam a y f' (-q) hlam0 hlam hy hf' hanti' hunit'
          hprofile hapi (by simpa [c'] using hbase') hq'
    change |infiniteResonantDensity lam a y c q| ≤ sharpenedComassBound lam
    change |infiniteResonantDensity lam a y c' (-q)| ≤
      sharpenedComassBound lam at hbound
    rw [hc', infiniteResonantDensity_reverseConjugate] at hbound
    simpa only [abs_neg] using hbound

/-- For genuine antiperiodic tangent-profile Fourier data, every finite
resonant density obeys the sharp comass bound up to the explicit vanishing
base/first-variation error. -/
theorem abs_finiteTruncationResonantDensity_fourierCoeffOn_le_sharpenedComassBound_add_error
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (N : ℕ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hprofile25 : ‖a‖ ^ 2 + 25 * infiniteComplexEnergy (fun k ↦ y (k + 1)) ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    |finiteTruncationResonantDensity lam a y c N| ≤
      sharpenedComassBound lam +
        |finiteTruncationResonantBaseFirstError lam a y c N| := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  have hpos' : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))) := by
    simpa [c] using hpos
  have hneg' : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))) := by
    simpa [c] using hneg
  have hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1 := by
    simpa [c] using
      infiniteOddEnergies_fourierCoeffOn_le_one f hf hanti hunit
  have hquadratic :
      |finiteTruncationResonantQuadraticVariation a y c N| ≤ Qstar :=
    abs_finiteTruncationResonantQuadraticVariation_le_Qstar
      a y c N hy hpos' hneg' hcoeff hprofile hapi
  have hinfinite : ∀ q : ℝ, |q| ≤ Qstar →
      |infiniteResonantDensity lam a y c q| ≤ sharpenedComassBound lam := by
    intro q hq
    simpa [c] using
      abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound
        lam a y f q hlam0 hlam hy hf hanti hunit hprofile25 hapi hq
  change |finiteTruncationResonantDensity lam a y c N| ≤
    sharpenedComassBound lam +
      |finiteTruncationResonantBaseFirstError lam a y c N|
  rw [finiteTruncationResonantDensity_eq_infinite_add_baseFirstError]
  exact (abs_add_le _ _).trans (add_le_add
    (hinfinite _ hquadratic) le_rfl)

end

end GromovFilling

#print axioms GromovFilling.abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound
#print axioms GromovFilling.abs_finiteTruncationResonantDensity_fourierCoeffOn_le_sharpenedComassBound_add_error
