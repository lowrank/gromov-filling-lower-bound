import GromovFilling.InfiniteResonantVariation
import GromovFilling.OddProfileParameterFourierBounds

/-!
# Infinite resonant comass envelope

This file connects the exact infinite first-variation estimate to the finite
resonant differential used by the Stokes truncations.  The base and linear
terms converge exactly, while the quadratic truncations obey the uniform
`Qstar` estimate.  This is the lossless replacement for the generally false
claim that every raw finite truncation separately satisfies the full Hardy
correlation-deficit inequality.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Base odd symplectic density of the first `N` positive and negative odd
Fourier pairs. -/
def finiteTruncationOddBaseDensity (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  let cPos : Fin (N + 1) → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : Fin (N + 1) → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  finiteBaseSymplecticDensity
    (finiteFourierTangentVector cPos cNeg)
    (finiteFourierQuarterTurnVector cPos cNeg)

/-- Quadratic resonant density of the first `N` odd output coordinates. -/
def finiteTruncationResonantQuadraticVariation
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  let cPos : Fin (N + 1) → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : Fin (N + 1) → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  finiteResonantQuadraticVariation a (fun k : Fin N ↦ y k)
    (finiteFourierTangentVector cPos cNeg)
    (finiteFourierQuarterTurnVector cPos cNeg)

/-- Full finite resonant density written in base/linear/quadratic form. -/
def finiteTruncationResonantDensity
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  finiteTruncationOddBaseDensity c N +
    lam * finiteTruncationResonantFirstVariation a y c N +
    lam ^ 2 * finiteTruncationResonantQuadraticVariation a y c N

/-- The infinite base/linear expression plus an arbitrary quadratic cluster
value.  Later Stokes passages only need that the cluster value is bounded by
`Qstar`. -/
def infiniteResonantDensity
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (q : ℝ) : ℝ :=
  infiniteOddBaseDensity c + lam * infiniteResonantFirstVariation a y c +
    lam ^ 2 * q

/-- A finite prefix of a summable squared-energy sequence is bounded by its
full infinite energy. -/
theorem finiteComplexEnergy_truncation_le_infiniteComplexEnergy
    (c : ℕ → ℂ) (hc : Summable (fun k ↦ Complex.normSq (c k))) (N : ℕ) :
    finiteComplexEnergy (fun k : Fin N ↦ c k) ≤ infiniteComplexEnergy c := by
  have hsum := hc.sum_le_tsum (Finset.range N)
    (fun k _hk ↦ Complex.normSq_nonneg (c k))
  unfold finiteComplexEnergy infiniteComplexEnergy
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ Complex.normSq (c k)) N]
  exact hsum

/-- The genuine odd-distance profile has a summable infinite tail of odd
Fourier coefficients. -/
theorem summable_normSq_oddProfileFourierMap_tail
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    Summable (fun n : ℕ ↦ Complex.normSq
      (oddProfileFourierMap boundary (oddMode n.succ) x)) := by
  let a : ℂ := oddProfileFourierMap boundary (oddMode 0) x
  let tail : ℕ → ℂ := fun n ↦
    oddProfileFourierMap boundary (oddMode n.succ) x
  apply summable_of_sum_range_le (c := 2 / 9)
    (fun n ↦ Complex.normSq_nonneg (tail n))
  intro N
  have hfinite :=
    oddProfileFourierMap_first_add_nine_tail_energy_le_two
      hboundary x N
  change ‖a‖ ^ 2 + 9 * finiteComplexEnergy
    (fun n : Fin N ↦ tail n) ≤ 2 at hfinite
  unfold finiteComplexEnergy at hfinite
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ Complex.normSq (tail n)) N] at hfinite
  have hprefix :
      ‖a‖ ^ 2 + 9 * (∑ n ∈ Finset.range N,
        Complex.normSq (tail n)) ≤ 2 := hfinite
  have ha : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Infinite form of the sharp profile estimate: the first mode has weight
one and the whole remaining odd tail has weight at least nine. -/
theorem oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
        9 * infiniteComplexEnergy (fun n ↦
          oddProfileFourierMap boundary (oddMode n.succ) x) ≤ 2 := by
  let a : ℂ := oddProfileFourierMap boundary (oddMode 0) x
  let tail : ℕ → ℂ := fun n ↦
    oddProfileFourierMap boundary (oddMode n.succ) x
  have htail : Summable (fun n ↦ Complex.normSq (tail n)) := by
    simpa [tail] using summable_normSq_oddProfileFourierMap_tail hboundary x
  have hprefix (N : ℕ) :
      ‖a‖ ^ 2 + 9 * (∑ n ∈ Finset.range N,
        Complex.normSq (tail n)) ≤ 2 := by
    have hfinite :=
      oddProfileFourierMap_first_add_nine_tail_energy_le_two
        hboundary x N
    change ‖a‖ ^ 2 + 9 * finiteComplexEnergy
      (fun n : Fin N ↦ tail n) ≤ 2 at hfinite
    unfold finiteComplexEnergy at hfinite
    rw [Fin.sum_univ_eq_sum_range
      (fun n : ℕ ↦ Complex.normSq (tail n)) N] at hfinite
    exact hfinite
  have hsum :
      infiniteComplexEnergy tail ≤ (2 - ‖a‖ ^ 2) / 9 := by
    unfold infiniteComplexEnergy
    apply Real.tsum_le_of_sum_range_le
      (fun n ↦ Complex.normSq_nonneg (tail n))
    intro N
    have h := hprefix N
    nlinarith
  change ‖a‖ ^ 2 + 9 * infiniteComplexEnergy tail ≤ 2
  nlinarith

/-- The positive and negative odd Fourier half-energies of a unit-bounded
antiperiodic field have total energy at most one. -/
theorem infiniteOddEnergies_fourierCoeffOn_le_one
    (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c ≤ 1 := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hfull :=
    norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_meanDeficit
      f hf hanti hunit
  have hmean :=
    normalized_meanDeficit_eq_one_sub_infiniteOddEnergies f hf hanti
  have hmeanNonneg :
      0 ≤ (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi, (1 - Complex.normSq (f x)) :=
    (norm_nonneg _).trans hfull
  change infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c ≤ 1
  have hidentity :
      (Real.pi - -Real.pi)⁻¹ *
          ∫ x in (-Real.pi)..Real.pi, (1 - Complex.normSq (f x)) =
        1 - infinitePositiveOddEnergy c - infiniteNegativeOddEnergy c := by
    simpa [c] using hmean
  rw [hidentity] at hmeanNonneg
  linarith

/-- The finite base densities converge to the exact infinite positive-minus-
negative odd energy. -/
theorem tendsto_finiteTruncationOddBaseDensity
    (c : ℤ → ℂ)
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Filter.Tendsto (finiteTruncationOddBaseDensity c)
      Filter.atTop (nhds (infiniteOddBaseDensity c)) := by
  let pos : ℕ → ℝ := fun k ↦ Complex.normSq (c (oddMode k : ℤ))
  let neg : ℕ → ℝ := fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))
  have hpos' : Summable pos := by simpa [pos] using hpos
  have hneg' : Summable neg := by simpa [neg] using hneg
  have hposT : Filter.Tendsto
      (fun N ↦ ∑ k ∈ Finset.range N, pos k)
      Filter.atTop (nhds (∑' k, pos k)) :=
    hpos'.hasSum.tendsto_sum_nat
  have hnegT : Filter.Tendsto
      (fun N ↦ ∑ k ∈ Finset.range N, neg k)
      Filter.atTop (nhds (∑' k, neg k)) :=
    hneg'.hasSum.tendsto_sum_nat
  have hsub := hposT.sub hnegT
  convert hsub using 1
  · funext N
    unfold finiteTruncationOddBaseDensity
    rw [finiteBaseSymplecticDensity_fourier]
    change (∑ n : Fin N, (pos n - neg n)) = _
    simp only [Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range pos N,
      Fin.sum_univ_eq_sum_range neg N]

/-- The finite base-plus-first-variation expressions converge exactly to the
infinite correlation formula. -/
theorem tendsto_finiteTruncationResonantBaseFirst
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Filter.Tendsto
      (fun N ↦ finiteTruncationOddBaseDensity c N +
        lam * finiteTruncationResonantFirstVariation a y c N)
      Filter.atTop
      (nhds (infiniteOddBaseDensity c +
        lam * infiniteResonantFirstVariation a y c)) := by
  exact (tendsto_finiteTruncationOddBaseDensity c hpos hneg).add
    (tendsto_const_nhds.mul
      (tendsto_finiteTruncationResonantFirstVariation
        a y c hy hpos hneg))

/-- Every quadratic truncation obeys the same `Qstar` bound as the full
resonant differential. -/
theorem abs_finiteTruncationResonantQuadraticVariation_le_Qstar
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |finiteTruncationResonantQuadraticVariation a y c N| ≤ Qstar := by
  let cPos : Fin (N + 1) → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : Fin (N + 1) → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  have hposPrefix : finiteComplexEnergy cPos ≤
      infinitePositiveOddEnergy c := by
    exact finiteComplexEnergy_truncation_le_infiniteComplexEnergy
      (fun k ↦ c (oddMode k : ℤ)) hpos (N + 1)
  have hnegPrefix : finiteComplexEnergy cNeg ≤
      infiniteNegativeOddEnergy c := by
    exact finiteComplexEnergy_truncation_le_infiniteComplexEnergy
      (fun k ↦ c (-(oddMode k : ℤ))) hneg (N + 1)
  have hcoeffPrefix :
      finiteComplexEnergy cPos + finiteComplexEnergy cNeg ≤ 1 :=
    (add_le_add hposPrefix hnegPrefix).trans hcoeff
  have hyPrefix :
      finiteComplexEnergy (fun k : Fin N ↦ y k) ≤
        infiniteComplexEnergy y :=
    finiteComplexEnergy_truncation_le_infiniteComplexEnergy y hy N
  have hprofilePrefix :
      ‖a‖ ^ 2 +
          9 * finiteComplexEnergy (fun k : Fin N ↦ y k) ≤ 2 :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hyPrefix (by norm_num))).trans
      hprofile
  unfold finiteTruncationResonantQuadraticVariation
  exact abs_finiteResonantQuadraticVariation_le_Qstar
    a (fun k : Fin N ↦ y k)
      (finiteFourierTangentVector cPos cNeg)
      (finiteFourierQuarterTurnVector cPos cNeg)
      hprofilePrefix hapi (by
        rw [finiteFourier_pair_energy]
        linarith)

/-- Scalar assembly of the nonlinear comass estimate from a sharp
first-variation deficit and a uniformly bounded quadratic term. -/
theorem abs_base_add_lam_first_add_lam_sq_quadratic_le_comassBound
    (lam base first quadratic : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hbase : |base| ≤ 1)
    (hfirst : |first| ≤
      Cstar * Real.sqrt (1 - |base|) + Dstar * (1 - |base|))
    (hquadratic : |quadratic| ≤ Qstar) :
    |base + lam * first + lam ^ 2 * quadratic| ≤ comassBound lam := by
  let delta : ℝ := 1 - |base|
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    linarith
  have homega :
      |base + lam * first + lam ^ 2 * quadratic| ≤
        1 - delta +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by
    calc
      |base + lam * first + lam ^ 2 * quadratic| ≤
          |base| + |lam * first| + |lam ^ 2 * quadratic| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |base| + lam * |first| + lam ^ 2 * |quadratic| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam0,
          abs_of_nonneg (sq_nonneg lam)]
      _ ≤ |base| +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          lam ^ 2 * Qstar := by
        gcongr
      _ = 1 - delta +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by
        dsimp only [delta]
        ring
  simpa only [comassBound] using
    nonlinear_comass_optimization lam Cstar Dstar Qstar
      (base + lam * first + lam ^ 2 * quadratic) delta hdelta
      (comass_denominator_pos_of_admissible hlam) homega

/-- Positive-base branch of the genuine infinite Fourier comass estimate.
The negative-base branch is obtained geometrically by reversing the ordered
orthonormal frame. -/
theorem abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound_of_base_nonneg
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi)
    (hbase0 : 0 ≤ infiniteOddBaseDensity
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n))
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam a y
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      comassBound lam := by
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
    abs_infiniteResonantFirstVariation_fourierCoeffOn_le_Cstar_Dstar
      a y f hy hf hanti hunit hprofile hapi
  have hfirst' :
      |infiniteResonantFirstVariation a y c| ≤
        Cstar * Real.sqrt (1 - |infiniteOddBaseDensity c|) +
          Dstar * (1 - |infiniteOddBaseDensity c|) := by
    have hbaseAbs : |infiniteOddBaseDensity c| =
        infiniteOddBaseDensity c :=
      abs_of_nonneg (by simpa [c] using hbase0)
    rw [hbaseAbs]
    simpa [c, infiniteOddOrientedDeficit] using hfirst
  change |infiniteResonantDensity lam a y c q| ≤ comassBound lam
  unfold infiniteResonantDensity
  exact abs_base_add_lam_first_add_lam_sq_quadratic_le_comassBound
    lam (infiniteOddBaseDensity c)
      (infiniteResonantFirstVariation a y c) q
      hlam0 hlam hbaseAbs hfirst' hq

/-- All scalar-profile hypotheses in the positive-base infinite comass bound
are automatic for the genuine odd distance profile. -/
theorem abs_infiniteResonantDensity_oddProfile_le_comassBound_of_base_nonneg
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X)
    (lam : ℝ) (f : ℝ → ℂ) (q : ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f t) ≤ 1)
    (hbase0 : 0 ≤ infiniteOddBaseDensity
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n))
    (hq : |q| ≤ Qstar) :
    |infiniteResonantDensity lam
        (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) q| ≤
      comassBound lam := by
  exact
    abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound_of_base_nonneg
      lam (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      f q hlam0 hlam
      (summable_normSq_oddProfileFourierMap_tail hboundary x)
      hf hanti hunit
      (oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
        hboundary x)
      (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)
      hbase0 hq

end

end GromovFilling

#print axioms GromovFilling.finiteComplexEnergy_truncation_le_infiniteComplexEnergy
#print axioms GromovFilling.summable_normSq_oddProfileFourierMap_tail
#print axioms GromovFilling.oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
#print axioms GromovFilling.infiniteOddEnergies_fourierCoeffOn_le_one
#print axioms GromovFilling.tendsto_finiteTruncationOddBaseDensity
#print axioms GromovFilling.tendsto_finiteTruncationResonantBaseFirst
#print axioms GromovFilling.abs_finiteTruncationResonantQuadraticVariation_le_Qstar
#print axioms GromovFilling.abs_base_add_lam_first_add_lam_sq_quadratic_le_comassBound
#print axioms GromovFilling.abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound_of_base_nonneg
#print axioms GromovFilling.abs_infiniteResonantDensity_oddProfile_le_comassBound_of_base_nonneg
