import GromovFilling.InfiniteCorrelationBounds
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Infinite resonant first variation

This module closes the infinite-dimensional analytic passage in Lemma 10.1.
It develops squared `ℓ²` energies for the positive and negative odd Fourier
halves, proves the exact Parseval decomposition and normalized mean-deficit
identity, and derives the signed shift and mixed-correlation estimates with
the manuscript's constants.

The verified finite resonant differential is then shown to converge to the
exact infinite first-variation correlation formula.  Specializations to a
genuine antiperiodic interval Fourier field prove the sharp `Cstar`/`Dstar`
bound and positive-saturation stationarity.  The global Hilbert-valued
Stokes/comass argument and the final Riemannian-surface theorem remain
separate geometric obligations.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace GromovFilling

noncomputable section

def infiniteComplexEnergy (c : ℕ → ℂ) : ℝ :=
  ∑' k, Complex.normSq (c k)

lemma infiniteComplexEnergy_nonneg (c : ℕ → ℂ) :
    0 ≤ infiniteComplexEnergy c := by
  exact tsum_nonneg fun k ↦ Complex.normSq_nonneg (c k)

lemma norm_le_sqrt_infiniteComplexEnergy
    (c : ℕ → ℂ)
    (hc : Summable (fun k ↦ Complex.normSq (c k))) (k : ℕ) :
    ‖c k‖ ≤ Real.sqrt (infiniteComplexEnergy c) := by
  apply Real.le_sqrt_of_sq_le
  rw [Complex.sq_norm]
  exact le_hasSum hc.hasSum k fun j _hj ↦ Complex.normSq_nonneg (c j)

private lemma infiniteComplexEnergy_succ_le
    (c : ℕ → ℂ)
    (hc : Summable (fun k ↦ Complex.normSq (c k))) :
    infiniteComplexEnergy (fun k ↦ c (k + 1)) ≤
      infiniteComplexEnergy c := by
  have htail : Summable (fun k ↦ Complex.normSq (c (k + 1))) := by
    simpa [Function.comp_def] using hc.comp_injective Nat.succ_injective
  exact Summable.tsum_le_tsum_of_inj Nat.succ Nat.succ_injective
    (fun j _hj ↦ Complex.normSq_nonneg (c j)) (fun _k ↦ le_rfl)
      htail hc

theorem norm_tsum_mul_le_sqrt_infiniteComplexEnergy
    (f g : ℕ → ℂ)
    (hf : Summable (fun k ↦ Complex.normSq (f k)))
    (hg : Summable (fun k ↦ Complex.normSq (g k))) :
    ‖∑' k, f k * g k‖ ≤
      Real.sqrt (infiniteComplexEnergy f) *
        Real.sqrt (infiniteComplexEnergy g) := by
  have hfLp : Memℓp f (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num)]
    simpa [Complex.sq_norm] using hf
  have hgLp : Memℓp g (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num)]
    simpa [Complex.sq_norm] using hg
  let F : lp (fun _ : ℕ ↦ ℂ) (2 : ℝ≥0∞) := ⟨f, hfLp⟩
  let G : lp (fun _ : ℕ ↦ ℂ) (2 : ℝ≥0∞) := ⟨g, hgLp⟩
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    exact Real.HolderConjugate.two_two
  have hHolder := lp.tsum_mul_le_mul_norm
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hholder F G
  have hprodNorm : Summable (fun k ↦ ‖f k * g k‖) := by
    simpa [F, G, norm_mul] using hHolder.1
  have hF_sq : ‖F‖ ^ 2 = infiniteComplexEnergy f := by
    simpa [F, infiniteComplexEnergy, Complex.sq_norm] using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) F)
  have hG_sq : ‖G‖ ^ 2 = infiniteComplexEnergy g := by
    simpa [G, infiniteComplexEnergy, Complex.sq_norm] using
      (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) G)
  have hF : ‖F‖ = Real.sqrt (infiniteComplexEnergy f) := by
    calc
      ‖F‖ = Real.sqrt (‖F‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg F)).symm
      _ = Real.sqrt (infiniteComplexEnergy f) := by rw [hF_sq]
  have hG : ‖G‖ = Real.sqrt (infiniteComplexEnergy g) := by
    calc
      ‖G‖ = Real.sqrt (‖G‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg G)).symm
      _ = Real.sqrt (infiniteComplexEnergy g) := by rw [hG_sq]
  calc
    ‖∑' k, f k * g k‖ ≤ ∑' k, ‖f k * g k‖ :=
      norm_tsum_le_tsum_norm hprodNorm
    _ = ∑' k, ‖f k‖ * ‖g k‖ := by simp only [norm_mul]
    _ ≤ ‖F‖ * ‖G‖ := by simpa [F, G] using hHolder.2
    _ = Real.sqrt (infiniteComplexEnergy f) *
        Real.sqrt (infiniteComplexEnergy g) := by rw [hF, hG]

private lemma summable_mul_of_summable_normSq
    (f g : ℕ → ℂ)
    (hf : Summable (fun k ↦ Complex.normSq (f k)))
    (hg : Summable (fun k ↦ Complex.normSq (g k))) :
    Summable (fun k ↦ f k * g k) := by
  have hfLp : Memℓp f (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num)]
    simpa [Complex.sq_norm] using hf
  have hgLp : Memℓp g (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num)]
    simpa [Complex.sq_norm] using hg
  let F : lp (fun _ : ℕ ↦ ℂ) (2 : ℝ≥0∞) := ⟨f, hfLp⟩
  let G : lp (fun _ : ℕ ↦ ℂ) (2 : ℝ≥0∞) := ⟨g, hgLp⟩
  have hHolder := lp.tsum_mul_le_mul_norm
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      Real.HolderConjugate.two_two F G
  apply Summable.of_norm
  simpa [F, G, norm_mul] using hHolder.1

/-- Squared energy in the positive odd frequencies of an integer sequence. -/
def infinitePositiveOddEnergy (c : ℤ → ℂ) : ℝ :=
  infiniteComplexEnergy (fun k ↦ c (oddMode k : ℤ))

/-- Squared energy in the negative odd frequencies of an integer sequence. -/
def infiniteNegativeOddEnergy (c : ℤ → ℂ) : ℝ :=
  infiniteComplexEnergy (fun k ↦ c (-(oddMode k : ℤ)))

/-- Base oriented symplectic density `P - N` of the odd Fourier data. -/
def infiniteOddBaseDensity (c : ℤ → ℂ) : ℝ :=
  infinitePositiveOddEnergy c - infiniteNegativeOddEnergy c

/-- Positive-orientation deficit `1 - (P - N)`. -/
def infiniteOddOrientedDeficit (c : ℤ → ℂ) : ℝ :=
  1 - infiniteOddBaseDensity c

private theorem tsum_natCast_normSq_eq_positiveOddEnergy_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable (fun n : ℕ ↦ Complex.normSq (c (n : ℤ))))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' n : ℕ, Complex.normSq (c (n : ℤ))) =
      infinitePositiveOddEnergy c := by
  let energy : ℕ → ℝ := fun n ↦ Complex.normSq (c (n : ℤ))
  have hEven : Summable (fun k : ℕ ↦ energy (2 * k)) := by
    simpa [energy, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k) by
        intro m n hmn
        exact Nat.mul_left_cancel (by norm_num) hmn)
  have hOdd : Summable (fun k : ℕ ↦ energy (2 * k + 1)) := by
    simpa [energy, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k + 1) by
        intro m n hmn
        exact Nat.mul_left_cancel (by norm_num)
          (Nat.add_right_cancel hmn))
  have hEvenZero : (∑' k : ℕ, energy (2 * k)) = 0 := by
    calc
      (∑' k : ℕ, energy (2 * k)) = ∑' _k : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro k
        unfold energy
        rw [heven (((2 * k : ℕ) : ℤ))]
        · simp
        · exact ⟨(k : ℤ), by push_cast; ring⟩
      _ = 0 := tsum_zero
  have hOddEq : (∑' k : ℕ, energy (2 * k + 1)) =
      infinitePositiveOddEnergy c := by
    unfold infinitePositiveOddEnergy infiniteComplexEnergy
    apply tsum_congr
    intro k
    unfold energy oddMode
    congr 2
  calc
    (∑' n : ℕ, Complex.normSq (c (n : ℤ))) =
        ∑' n : ℕ, energy n := rfl
    _ = (∑' k : ℕ, energy (2 * k)) +
          ∑' k : ℕ, energy (2 * k + 1) :=
      (tsum_even_add_odd hEven hOdd).symm
    _ = infinitePositiveOddEnergy c := by
      rw [hEvenZero, zero_add, hOddEq]

private theorem tsum_negSucc_normSq_eq_negativeOddEnergy_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable (fun n : ℕ ↦
      Complex.normSq (c (-((n : ℤ) + 1)))))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' n : ℕ, Complex.normSq (c (-((n : ℤ) + 1)))) =
      infiniteNegativeOddEnergy c := by
  let energy : ℕ → ℝ :=
    fun n ↦ Complex.normSq (c (-((n : ℤ) + 1)))
  have hEven : Summable (fun k : ℕ ↦ energy (2 * k)) := by
    simpa [energy, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k) by
        intro m n hmn
        exact Nat.mul_left_cancel (by norm_num) hmn)
  have hOdd : Summable (fun k : ℕ ↦ energy (2 * k + 1)) := by
    simpa [energy, Function.comp_def] using hc.comp_injective
      (show Function.Injective (fun k : ℕ ↦ 2 * k + 1) by
        intro m n hmn
        exact Nat.mul_left_cancel (by norm_num)
          (Nat.add_right_cancel hmn))
  have hOddZero : (∑' k : ℕ, energy (2 * k + 1)) = 0 := by
    calc
      (∑' k : ℕ, energy (2 * k + 1)) = ∑' _k : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro k
        unfold energy
        have hidx : -(((2 * k + 1 : ℕ) : ℤ) + 1) =
            -2 * ((k : ℤ) + 1) := by push_cast; ring
        rw [heven (-(((2 * k + 1 : ℕ) : ℤ) + 1))]
        · simp
        · exact ⟨-((k : ℤ) + 1), by rw [hidx]; ring⟩
      _ = 0 := tsum_zero
  have hEvenEq : (∑' k : ℕ, energy (2 * k)) =
      infiniteNegativeOddEnergy c := by
    unfold infiniteNegativeOddEnergy infiniteComplexEnergy
    apply tsum_congr
    intro k
    unfold energy oddMode
    push_cast
    congr 2
  calc
    (∑' n : ℕ, Complex.normSq (c (-((n : ℤ) + 1)))) =
        ∑' n : ℕ, energy n := rfl
    _ = (∑' k : ℕ, energy (2 * k)) +
          ∑' k : ℕ, energy (2 * k + 1) :=
      (tsum_even_add_odd hEven hOdd).symm
    _ = infiniteNegativeOddEnergy c := by
      rw [hEvenEq, hOddZero, add_zero]

/-- Parseval energy of an even-vanishing integer sequence is exactly the
sum of its positive-odd and negative-odd energies. -/
theorem tsum_normSq_eq_infiniteOddEnergies_of_even_vanishes
    (c : ℤ → ℂ)
    (hc : Summable (fun k : ℤ ↦ Complex.normSq (c k)))
    (heven : ∀ k : ℤ, Even k → c k = 0) :
    (∑' k : ℤ, Complex.normSq (c k)) =
      infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c := by
  let energy : ℤ → ℝ := fun k ↦ Complex.normSq (c k)
  have hnat : Summable (fun n : ℕ ↦ energy (n : ℤ)) := by
    simpa [energy, Function.comp_def] using
      hc.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ ↦ energy (-((n : ℤ) + 1))) := by
    have hinj : Function.Injective
        (fun n : ℕ ↦ (-((n : ℤ) + 1) : ℤ)) := by
      intro m n hmn
      change -((m : ℤ) + 1) = -((n : ℤ) + 1) at hmn
      have hplus : (m : ℤ) + 1 = (n : ℤ) + 1 := neg_injective hmn
      exact Int.ofNat_inj.mp (add_right_cancel hplus)
    simpa [energy, Function.comp_def] using hc.comp_injective hinj
  have hpositive : (∑' n : ℕ, energy (n : ℤ)) =
      infinitePositiveOddEnergy c := by
    exact tsum_natCast_normSq_eq_positiveOddEnergy_of_even_vanishes
      c (by simpa [energy] using hnat) heven
  have hnegative : (∑' n : ℕ, energy (-((n : ℤ) + 1))) =
      infiniteNegativeOddEnergy c := by
    exact tsum_negSucc_normSq_eq_negativeOddEnergy_of_even_vanishes
      c (by simpa [energy] using hneg) heven
  change (∑' k : ℤ, energy k) = _
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hpositive, hnegative]

/-- Both odd Fourier half-energies are summable for an interval `L²`
field. -/
theorem summable_odd_fourierCoeffOn_energies
    (f : ℝ → ℂ)
    (hf : MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi))) :
    Summable (fun k ↦ Complex.normSq
        (fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          f (oddMode k : ℤ))) ∧
      Summable (fun k ↦ Complex.normSq
        (fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          f (-(oddMode k : ℤ)))) := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hall : Summable (fun n : ℤ ↦
      Complex.normSq (fourierCoeffOn hab f n)) := by
    simpa [← Complex.sq_norm] using
      (hasSum_sq_fourierCoeffOn hab hf).summable
  have hposInj : Function.Injective
      (fun k : ℕ ↦ (oddMode k : ℤ)) := by
    intro m n hmn
    unfold oddMode at hmn
    push_cast at hmn
    omega
  have hnegInj : Function.Injective
      (fun k : ℕ ↦ (-(oddMode k : ℤ) : ℤ)) :=
    neg_injective.comp hposInj
  constructor
  · simpa [hab, Function.comp_def] using hall.comp_injective hposInj
  · simpa [hab, Function.comp_def] using hall.comp_injective hnegInj

/-- Parseval is exact after decomposing an antiperiodic field into its
positive and negative odd Fourier half-energies. -/
theorem infiniteOddEnergies_fourierCoeffOn_eq_normalizedIntegral
    (f : ℝ → ℂ)
    (hf : MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c =
      (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hall : Summable (fun n : ℤ ↦ Complex.normSq (c n)) := by
    simpa [c, ← Complex.sq_norm] using
      (hasSum_sq_fourierCoeffOn hab hf).summable
  have heven : ∀ n : ℤ, Even n → c n = 0 := by
    intro n hn
    exact fourierCoeffOn_eq_zero_of_antiperiodic_of_even f hf hanti n hn
  have hdecomp :=
    tsum_normSq_eq_infiniteOddEnergies_of_even_vanishes c hall heven
  have hparse := (hasSum_sq_fourierCoeffOn hab hf).tsum_eq
  change infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c = _
  calc
    infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c =
        ∑' n : ℤ, Complex.normSq (c n) := hdecomp.symm
    _ = ∑' n : ℤ, ‖fourierCoeffOn hab f n‖ ^ 2 := by
      apply tsum_congr
      intro n
      simp [c, Complex.sq_norm]
    _ = (Real.pi - -Real.pi)⁻¹ •
        ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := hparse
    _ = (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := by
      rw [smul_eq_mul]

/-- The normalized pointwise norm deficit is exactly `1 - P - N` for the
odd Fourier half-energies. -/
theorem normalized_meanDeficit_eq_one_sub_infiniteOddEnergies
    (f : ℝ → ℂ)
    (hf : MemLp f 2
      (MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    (Real.pi - -Real.pi)⁻¹ *
        ∫ x in (-Real.pi)..Real.pi, (1 - Complex.normSq (f x)) =
      1 - infinitePositiveOddEnergy c - infiniteNegativeOddEnergy c := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hnormSq : IntervalIntegrable
      (fun x ↦ Complex.normSq (f x)) volume
        (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn, Complex.normSq_eq_norm_sq] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict
          (Set.Ioc (-Real.pi) Real.pi)) hf)
  have hone : IntervalIntegrable (fun _x : ℝ ↦ (1 : ℝ))
      volume (-Real.pi) Real.pi :=
    (continuous_const : Continuous (fun _x : ℝ ↦ (1 : ℝ)))
      |>.intervalIntegrable _ _
  have henergy :=
    infiniteOddEnergies_fourierCoeffOn_eq_normalizedIntegral f hf hanti
  change (Real.pi - -Real.pi)⁻¹ *
      ∫ x in (-Real.pi)..Real.pi, (1 - Complex.normSq (f x)) =
    1 - infinitePositiveOddEnergy c - infiniteNegativeOddEnergy c
  rw [intervalIntegral.integral_sub hone hnormSq]
  have honeIntegral :
      (∫ _x in (-Real.pi)..Real.pi, (1 : ℝ)) =
        Real.pi - -Real.pi := by simp
  rw [honeIntegral]
  change (Real.pi - -Real.pi)⁻¹ *
      ((Real.pi - -Real.pi) -
        ∫ x in (-Real.pi)..Real.pi, Complex.normSq (f x)) = _
  have hnormIntegral :
      (Real.pi - -Real.pi)⁻¹ *
          ∫ x in (-Real.pi)..Real.pi, Complex.normSq (f x) =
        infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c := by
    have henergy' :
        infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c =
          (Real.pi - -Real.pi)⁻¹ *
            ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := by
      simpa [c] using henergy
    calc
      (Real.pi - -Real.pi)⁻¹ *
          ∫ x in (-Real.pi)..Real.pi, Complex.normSq (f x) =
          (Real.pi - -Real.pi)⁻¹ *
            ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _hx
        exact (Complex.sq_norm (f x)).symm
      _ = infinitePositiveOddEnergy c + infiniteNegativeOddEnergy c :=
        henergy'.symm
  rw [mul_sub, inv_mul_cancel₀ (by linarith [Real.pi_pos] :
    Real.pi - -Real.pi ≠ 0), hnormIntegral]
  ring

/-- The actual antiperiodic Fourier data satisfy the full-correlation
hypothesis in exactly the `delta - 2N` form used by the nonlinear estimate. -/
theorem norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_deficit_sub_two_neg
    (f : ℝ → ℂ)
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    ‖infiniteFullOddShiftCorrelation c‖ ≤
      infiniteOddOrientedDeficit c -
        2 * infiniteNegativeOddEnergy c := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hfull :=
    norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_meanDeficit
      f hf hanti hunit
  have hmean :=
    normalized_meanDeficit_eq_one_sub_infiniteOddEnergies f hf hanti
  change ‖infiniteFullOddShiftCorrelation c‖ ≤ _
  calc
    ‖infiniteFullOddShiftCorrelation c‖ ≤
        (Real.pi - -Real.pi)⁻¹ *
          ∫ x in (-Real.pi)..Real.pi,
            (1 - Complex.normSq (f x)) := by
      simpa [c] using hfull
    _ = 1 - infinitePositiveOddEnergy c -
        infiniteNegativeOddEnergy c := by
      simpa [c] using hmean
    _ = infiniteOddOrientedDeficit c -
        2 * infiniteNegativeOddEnergy c := by
      unfold infiniteOddOrientedDeficit infiniteOddBaseDensity
      ring

/-- The mixed profile/Fourier correlation in the infinite first variation. -/
def infiniteOddMixedCorrelation (y : ℕ → ℂ) (c : ℤ → ℂ) : ℂ :=
  ∑' k, y k *
    (-star (c (-(oddMode k : ℤ))) * c 1 +
      star (c (-1)) * c (oddMode k : ℤ))

private lemma infiniteOddMixedCorrelation_decomposition
    (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    infiniteOddMixedCorrelation y c =
      -(∑' k, y k * star (c (-(oddMode k : ℤ)))) * c 1 +
        star (c (-1)) * (∑' k, y k * c (oddMode k : ℤ)) := by
  have hnegStar : Summable
      (fun k ↦ Complex.normSq (star (c (-(oddMode k : ℤ))))) := by
    simpa [← Complex.sq_norm] using hneg
  have hfirst : Summable
      (fun k ↦ y k * star (c (-(oddMode k : ℤ)))) :=
    summable_mul_of_summable_normSq y
      (fun k ↦ star (c (-(oddMode k : ℤ)))) hy hnegStar
  have hsecond : Summable
      (fun k ↦ y k * c (oddMode k : ℤ)) :=
    summable_mul_of_summable_normSq y
      (fun k ↦ c (oddMode k : ℤ)) hy hpos
  unfold infiniteOddMixedCorrelation
  calc
    (∑' k, y k *
        (-star (c (-(oddMode k : ℤ))) * c 1 +
          star (c (-1)) * c (oddMode k : ℤ))) =
        ∑' k,
          (-(y k * star (c (-(oddMode k : ℤ)))) * c 1 +
            star (c (-1)) * (y k * c (oddMode k : ℤ))) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k, -(y k * star (c (-(oddMode k : ℤ)))) * c 1) +
        ∑' k, star (c (-1)) * (y k * c (oddMode k : ℤ)) :=
      (hfirst.neg.mul_right (c 1)).tsum_add
        (hsecond.mul_left (star (c (-1))))
    _ = -(∑' k, y k * star (c (-(oddMode k : ℤ)))) * c 1 +
        star (c (-1)) * (∑' k, y k * c (oddMode k : ℤ)) := by
      rw [hfirst.neg.tsum_mul_right, tsum_neg,
        hsecond.tsum_mul_left]

theorem norm_infiniteOddMixedCorrelation_le
    (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1) :
    ‖infiniteOddMixedCorrelation y c‖ ≤
      2 * Real.sqrt (infiniteComplexEnergy y) *
        Real.sqrt (infiniteNegativeOddEnergy c) := by
  let cPos : ℕ → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : ℕ → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  have hnegStar : Summable (fun k ↦ Complex.normSq (star (cNeg k))) := by
    simpa [cNeg, ← Complex.sq_norm] using hneg
  have hnegStarEnergy :
      infiniteComplexEnergy (fun k ↦ star (cNeg k)) =
        infiniteNegativeOddEnergy c := by
    simp [infiniteComplexEnergy, infiniteNegativeOddEnergy, cNeg,
      ← Complex.sq_norm]
  have hfirst :
      ‖∑' k, y k * star (cNeg k)‖ ≤
        Real.sqrt (infiniteComplexEnergy y) *
          Real.sqrt (infiniteNegativeOddEnergy c) := by
    have hbound := norm_tsum_mul_le_sqrt_infiniteComplexEnergy y
      (fun k ↦ star (cNeg k)) hy hnegStar
    rw [hnegStarEnergy] at hbound
    exact hbound
  have hsecondRaw :
      ‖∑' k, y k * cPos k‖ ≤
        Real.sqrt (infiniteComplexEnergy y) *
          Real.sqrt (infinitePositiveOddEnergy c) := by
    simpa [infinitePositiveOddEnergy, cPos] using
      norm_tsum_mul_le_sqrt_infiniteComplexEnergy y cPos hy (by
        simpa [cPos] using hpos)
  have hposNonneg : 0 ≤ infinitePositiveOddEnergy c :=
    infiniteComplexEnergy_nonneg _
  have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
    infiniteComplexEnergy_nonneg _
  have hsqrtPos : Real.sqrt (infinitePositiveOddEnergy c) ≤ 1 := by
    nlinarith [Real.sq_sqrt hposNonneg,
      Real.sqrt_nonneg (infinitePositiveOddEnergy c)]
  have hsecond :
      ‖∑' k, y k * cPos k‖ ≤ Real.sqrt (infiniteComplexEnergy y) := by
    calc
      ‖∑' k, y k * cPos k‖ ≤
          Real.sqrt (infiniteComplexEnergy y) *
            Real.sqrt (infinitePositiveOddEnergy c) := hsecondRaw
      _ ≤ Real.sqrt (infiniteComplexEnergy y) * 1 := by gcongr
      _ = Real.sqrt (infiniteComplexEnergy y) := mul_one _
  have hcPosOne : ‖c 1‖ ≤ 1 := by
    have h0 := norm_le_sqrt_infiniteComplexEnergy cPos (by
      simpa [cPos] using hpos) 0
    have hc0 : cPos 0 = c 1 := by simp [cPos, oddMode]
    rw [hc0] at h0
    exact h0.trans hsqrtPos
  have hcNeg : ‖c (-1)‖ ≤ Real.sqrt (infiniteNegativeOddEnergy c) := by
    have h0 := norm_le_sqrt_infiniteComplexEnergy cNeg (by
      simpa [cNeg] using hneg) 0
    simpa [cNeg, infiniteNegativeOddEnergy, oddMode] using h0
  rw [infiniteOddMixedCorrelation_decomposition y c hy hpos hneg]
  change
    ‖-(∑' k, y k * star (cNeg k)) * c 1 +
        star (c (-1)) * (∑' k, y k * cPos k)‖ ≤ _
  calc
    ‖-(∑' k, y k * star (cNeg k)) * c 1 +
        star (c (-1)) * (∑' k, y k * cPos k)‖ ≤
        ‖-(∑' k, y k * star (cNeg k)) * c 1‖ +
          ‖star (c (-1)) * (∑' k, y k * cPos k)‖ := norm_add_le _ _
    _ = ‖∑' k, y k * star (cNeg k)‖ * ‖c 1‖ +
          ‖c (-1)‖ * ‖∑' k, y k * cPos k‖ := by
      simp only [norm_mul, norm_neg, norm_star]
    _ ≤ (Real.sqrt (infiniteComplexEnergy y) *
            Real.sqrt (infiniteNegativeOddEnergy c)) * 1 +
          Real.sqrt (infiniteNegativeOddEnergy c) *
            Real.sqrt (infiniteComplexEnergy y) := by gcongr
    _ = 2 * Real.sqrt (infiniteComplexEnergy y) *
        Real.sqrt (infiniteNegativeOddEnergy c) := by ring

theorem norm_infiniteNegativeShiftCorrelation_le
    (c : ℤ → ℂ)
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    ‖infiniteNegativeShiftCorrelation c‖ ≤ infiniteNegativeOddEnergy c := by
  let cNeg : ℕ → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  have htail : Summable (fun k ↦ Complex.normSq (cNeg (k + 1))) := by
    simpa [Function.comp_def] using hneg.comp_injective Nat.succ_injective
  have hstar : Summable (fun k ↦ Complex.normSq (star (cNeg k))) := by
    simpa [← Complex.sq_norm] using hneg
  have hcs := norm_tsum_mul_le_sqrt_infiniteComplexEnergy
    (fun k ↦ star (cNeg k)) (fun k ↦ cNeg (k + 1)) hstar htail
  have htailEnergy := infiniteComplexEnergy_succ_le cNeg (by
    simpa [cNeg] using hneg)
  have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
    infiniteComplexEnergy_nonneg _
  unfold infiniteNegativeShiftCorrelation
  change ‖∑' k, star (cNeg k) * cNeg (k + 1)‖ ≤ _
  calc
    ‖∑' k, star (cNeg k) * cNeg (k + 1)‖ ≤
        Real.sqrt (infiniteComplexEnergy (fun k ↦ star (cNeg k))) *
          Real.sqrt (infiniteComplexEnergy (fun k ↦ cNeg (k + 1))) := hcs
    _ = Real.sqrt (infiniteNegativeOddEnergy c) *
          Real.sqrt (infiniteComplexEnergy (fun k ↦ cNeg (k + 1))) := by
      congr 2
      simp [infiniteComplexEnergy, infiniteNegativeOddEnergy, cNeg,
        ← Complex.sq_norm]
    _ ≤ Real.sqrt (infiniteNegativeOddEnergy c) *
          Real.sqrt (infiniteNegativeOddEnergy c) := by
      gcongr
      simpa [infiniteNegativeOddEnergy, cNeg] using htailEnergy
    _ = infiniteNegativeOddEnergy c :=
      Real.mul_self_sqrt hnegNonneg

/-- Infinite quantitative signed shift-correlation estimate. -/
theorem norm_infiniteSignedOddShiftCorrelation_le_delta_add_sqrt
    (c : ℤ → ℂ) (delta : ℝ)
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hPos : infinitePositiveOddEnergy c ≤ 1)
    (hFull :
      ‖infiniteFullOddShiftCorrelation c‖ ≤
        delta - 2 * infiniteNegativeOddEnergy c) :
    ‖infiniteSignedOddShiftCorrelation c‖ ≤
      delta + Real.sqrt (delta / 2) := by
  let cPos : ℕ → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : ℕ → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  let negEnergy := infiniteNegativeOddEnergy c
  have hnegNonneg : 0 ≤ negEnergy := infiniteComplexEnergy_nonneg _
  have hnegDelta : negEnergy ≤ delta / 2 := by
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hsqrtNeg : Real.sqrt negEnergy ≤ Real.sqrt (delta / 2) :=
    Real.sqrt_le_sqrt hnegDelta
  have hposNonneg : 0 ≤ infinitePositiveOddEnergy c :=
    infiniteComplexEnergy_nonneg _
  have hsqrtPos : Real.sqrt (infinitePositiveOddEnergy c) ≤ 1 := by
    nlinarith [Real.sq_sqrt hposNonneg,
      Real.sqrt_nonneg (infinitePositiveOddEnergy c)]
  have hcPosOne : ‖c 1‖ ≤ 1 := by
    have h0 := norm_le_sqrt_infiniteComplexEnergy cPos (by
      simpa [cPos] using hpos) 0
    have hc0 : cPos 0 = c 1 := by simp [cPos, oddMode]
    rw [hc0] at h0
    exact h0.trans hsqrtPos
  have hcNeg : ‖c (-1)‖ ≤ Real.sqrt negEnergy := by
    have h0 := norm_le_sqrt_infiniteComplexEnergy cNeg (by
      simpa [cNeg] using hneg) 0
    simpa [cNeg, negEnergy, infiniteNegativeOddEnergy, oddMode] using h0
  have hcross :
      ‖c (-1) * star (c 1)‖ ≤ Real.sqrt negEnergy := by
    calc
      ‖c (-1) * star (c 1)‖ = ‖c (-1)‖ * ‖c 1‖ := by
        simp only [norm_mul, norm_star]
      _ ≤ Real.sqrt negEnergy * 1 := by gcongr
      _ = Real.sqrt negEnergy := mul_one _
  have hnegative := norm_infiniteNegativeShiftCorrelation_le c hneg
  have hidentity :
      infiniteSignedOddShiftCorrelation c =
        infiniteFullOddShiftCorrelation c -
          c (-1) * star (c 1) -
          2 * infiniteNegativeShiftCorrelation c := by
    unfold infiniteSignedOddShiftCorrelation
      infiniteFullOddShiftCorrelation
    ring
  rw [hidentity]
  calc
    ‖infiniteFullOddShiftCorrelation c - c (-1) * star (c 1) -
        2 * infiniteNegativeShiftCorrelation c‖ ≤
        ‖infiniteFullOddShiftCorrelation c‖ +
          ‖c (-1) * star (c 1)‖ +
          ‖2 * infiniteNegativeShiftCorrelation c‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (delta - 2 * negEnergy) + Real.sqrt negEnergy +
          2 * negEnergy := by
      have htwo :
          ‖(2 : ℂ) * infiniteNegativeShiftCorrelation c‖ =
            2 * ‖infiniteNegativeShiftCorrelation c‖ := by
        rw [norm_mul]
        norm_num
      rw [htwo]
      exact add_le_add (add_le_add hFull hcross) (by
        gcongr)
    _ = delta + Real.sqrt negEnergy := by ring
    _ ≤ delta + Real.sqrt (delta / 2) := by gcongr

/-- Exact correlation formula for the infinite resonant first variation. -/
def infiniteResonantFirstVariation
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) : ℝ :=
  2 * (star a ^ 2 * infiniteSignedOddShiftCorrelation c).re +
    4 * (star a * infiniteOddMixedCorrelation y c).re

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
theorem abs_infiniteResonantFirstVariation_le_raw
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
        8 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y) *
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
  have hmixed := norm_infiniteOddMixedCorrelation_le
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
            (2 * Real.sqrt (infiniteComplexEnergy y) *
              Real.sqrt negEnergy) := by gcongr
    _ ≤ 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ *
            (2 * Real.sqrt (infiniteComplexEnergy y) *
              Real.sqrt (delta / 2)) := by gcongr
    _ = 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          8 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y) *
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
theorem abs_infiniteResonantFirstVariation_le_manuscript
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
          (‖a‖ ^ 2 + 4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y)) *
          Real.sqrt delta := by
  have hdelta : 0 ≤ delta := by
    have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg _
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hraw := abs_infiniteResonantFirstVariation_le_raw
    a y c delta hy hpos hneg hPos hFull
  calc
    |infiniteResonantFirstVariation a y c| ≤
        2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          8 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y) *
            Real.sqrt (delta / 2) := hraw
    _ = 2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 + 4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y)) *
          Real.sqrt delta := by
      rw [sqrt_div_two_eq_infinite delta hdelta]
      ring

/-- The infinite first variation feeds into the verified sharp scalar
constants without any finite-truncation loss. -/
theorem abs_infiniteResonantFirstVariation_le_Cstar_Dstar
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
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |infiniteResonantFirstVariation a y c| ≤
      Cstar * Real.sqrt delta + Dstar * delta := by
  have hdelta : 0 ≤ delta := by
    have hnegNonneg : 0 ≤ infiniteNegativeOddEnergy c :=
      infiniteComplexEnergy_nonneg _
    have hfullNonneg : 0 ≤ ‖infiniteFullOddShiftCorrelation c‖ :=
      norm_nonneg _
    linarith
  have hySq := Real.sq_sqrt (infiniteComplexEnergy_nonneg y)
  apply firstVariation_le_Cstar_Dstar
    ‖a‖ (Real.sqrt (infiniteComplexEnergy y)) delta
      (infiniteResonantFirstVariation a y c)
      (norm_nonneg a) hdelta
  · simpa only [hySq] using hprofile
  · exact hapi
  · exact abs_infiniteResonantFirstVariation_le_manuscript
      a y c delta hy hpos hneg hPos hFull

private theorem tendsto_finiteResonantShiftCorrelation_to_infinite
    (c : ℤ → ℂ)
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Filter.Tendsto
      (fun N ↦ finiteResonantShiftCorrelation
        (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
        (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))))
      Filter.atTop (nhds (infiniteSignedOddShiftCorrelation c)) := by
  let cPos : ℕ → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : ℕ → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  let posCorr : ℕ → ℂ := fun k ↦ cPos k * star (cPos (k + 1))
  let negCorr : ℕ → ℂ := fun k ↦ star (cNeg k) * cNeg (k + 1)
  have hposTail : Summable
      (fun k ↦ Complex.normSq (star (cPos (k + 1)))) := by
    simpa [cPos, Function.comp_def, ← Complex.sq_norm] using
      hpos.comp_injective Nat.succ_injective
  have hnegStar : Summable
      (fun k ↦ Complex.normSq (star (cNeg k))) := by
    simpa [cNeg, ← Complex.sq_norm] using hneg
  have hnegTail : Summable
      (fun k ↦ Complex.normSq (cNeg (k + 1))) := by
    simpa [cNeg, Function.comp_def] using
      hneg.comp_injective Nat.succ_injective
  have hposCorr : Summable posCorr := by
    exact summable_mul_of_summable_normSq cPos
      (fun k ↦ star (cPos (k + 1))) (by simpa [cPos] using hpos) hposTail
  have hnegCorr : Summable negCorr := by
    exact summable_mul_of_summable_normSq
      (fun k ↦ star (cNeg k)) (fun k ↦ cNeg (k + 1))
        hnegStar hnegTail
  have hsum :
      (∑' k, (posCorr k - negCorr k)) =
        infiniteSignedOddShiftCorrelation c := by
    rw [hposCorr.tsum_sub hnegCorr]
    rfl
  have htend := (hposCorr.sub hnegCorr).hasSum.tendsto_sum_nat
  rw [hsum] at htend
  convert htend using 1
  funext N
  unfold finiteResonantShiftCorrelation
  rw [Finset.sum_sub_distrib]
  change
    (∑ k : Fin N, posCorr k) - ∑ k : Fin N, negCorr k =
      ∑ k ∈ Finset.range N, (posCorr k - negCorr k)
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range,
    Finset.sum_sub_distrib]

private theorem tendsto_finiteResonantMixedCorrelation_to_infinite
    (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Filter.Tendsto
      (fun N ↦ finiteResonantMixedCorrelation
        (fun k : Fin N ↦ y k)
        (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
        (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))))
      Filter.atTop (nhds (infiniteOddMixedCorrelation y c)) := by
  let mixed : ℕ → ℂ := fun k ↦ y k *
    (-star (c (-(oddMode k : ℤ))) * c 1 +
      star (c (-1)) * c (oddMode k : ℤ))
  have hnegStar : Summable
      (fun k ↦ Complex.normSq (star (c (-(oddMode k : ℤ))))) := by
    simpa [← Complex.sq_norm] using hneg
  have hfirst : Summable
      (fun k ↦ y k * star (c (-(oddMode k : ℤ)))) :=
    summable_mul_of_summable_normSq y
      (fun k ↦ star (c (-(oddMode k : ℤ)))) hy hnegStar
  have hsecond : Summable
      (fun k ↦ y k * c (oddMode k : ℤ)) :=
    summable_mul_of_summable_normSq y
      (fun k ↦ c (oddMode k : ℤ)) hy hpos
  have hmixed : Summable mixed := by
    apply ((hfirst.neg.mul_right (c 1)).add
      (hsecond.mul_left (star (c (-1))))).congr
    intro k
    unfold mixed
    ring
  have htend := hmixed.hasSum.tendsto_sum_nat
  change Filter.Tendsto _ Filter.atTop (nhds (∑' k, mixed k))
  convert htend using 1
  funext N
  unfold finiteResonantMixedCorrelation
  change (∑ k : Fin N, mixed k) =
    ∑ k ∈ Finset.range N, mixed k
  rw [Fin.sum_univ_eq_sum_range]

/-- The finite differential calculation evaluated on the first `N` odd
Fourier modes of infinite coefficient data. -/
def finiteTruncationResonantFirstVariation
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  let cPos : Fin (N + 1) → ℂ :=
    fun k ↦ c (oddMode k : ℤ)
  let cNeg : Fin (N + 1) → ℂ :=
    fun k ↦ c (-(oddMode k : ℤ))
  finiteResonantFirstVariation a (fun k : Fin N ↦ y k)
    (finiteFourierTangentVector cPos cNeg)
    (finiteFourierQuarterTurnVector cPos cNeg)

/-- Exact infinite-coordinate passage for Lemma 10.1: the verified finite
differential first variations converge to the full signed and mixed
correlation formula. -/
theorem tendsto_finiteTruncationResonantFirstVariation
    (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Filter.Tendsto
      (finiteTruncationResonantFirstVariation a y c)
      Filter.atTop (nhds (infiniteResonantFirstVariation a y c)) := by
  let shiftN : ℕ → ℂ := fun N ↦ finiteResonantShiftCorrelation
    (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
    (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ)))
  let mixedN : ℕ → ℂ := fun N ↦ finiteResonantMixedCorrelation
    (fun k : Fin N ↦ y k)
    (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
    (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ)))
  have hshift : Filter.Tendsto shiftN Filter.atTop
      (nhds (infiniteSignedOddShiftCorrelation c)) := by
    simpa [shiftN] using
      tendsto_finiteResonantShiftCorrelation_to_infinite c hpos hneg
  have hmixed : Filter.Tendsto mixedN Filter.atTop
      (nhds (infiniteOddMixedCorrelation y c)) := by
    simpa [mixedN] using
      tendsto_finiteResonantMixedCorrelation_to_infinite y c hy hpos hneg
  let assemble : ℂ × ℂ → ℝ := fun z ↦
    2 * (star a ^ 2 * z.1).re + 4 * (star a * z.2).re
  have hassemble : Continuous assemble := by
    unfold assemble
    fun_prop
  have htend := hassemble.continuousAt.tendsto.comp
    (hshift.prodMk_nhds hmixed)
  convert htend using 1
  funext N
  unfold finiteTruncationResonantFirstVariation
  rw [finiteResonant_firstVariation_eq_correlations]
  rfl

/-- Lemma 10.1 for genuine interval Fourier coefficients: the finite
differential variations converge to the exact infinite correlation formula. -/
theorem tendsto_finiteTruncationResonantFirstVariation_fourierCoeffOn
    (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    Filter.Tendsto
      (finiteTruncationResonantFirstVariation a y c)
      Filter.atTop (nhds (infiniteResonantFirstVariation a y c)) := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  change Filter.Tendsto
    (finiteTruncationResonantFirstVariation a y c)
      Filter.atTop (nhds (infiniteResonantFirstVariation a y c))
  exact tendsto_finiteTruncationResonantFirstVariation
    a y c hy (by simpa [c] using hpos) (by simpa [c] using hneg)

/-- Quantitative infinite first-variation estimate for a genuine
antiperiodic interval Fourier field. -/
theorem abs_infiniteResonantFirstVariation_fourierCoeffOn_le_manuscript
    (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    let delta := infiniteOddOrientedDeficit c
    |infiniteResonantFirstVariation a y c| ≤
      2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 + 4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y)) *
          Real.sqrt delta := by
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
  exact abs_infiniteResonantFirstVariation_le_manuscript
    a y c (infiniteOddOrientedDeficit c)
      hy hpos' hneg' hPos hFull

/-- The genuine Fourier first variation satisfies the verified sharp
`Cstar`, `Dstar` estimate. -/
theorem abs_infiniteResonantFirstVariation_fourierCoeffOn_le_Cstar_Dstar
    (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    let delta := infiniteOddOrientedDeficit c
    |infiniteResonantFirstVariation a y c| ≤
      Cstar * Real.sqrt delta + Dstar * delta := by
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
  exact abs_infiniteResonantFirstVariation_le_Cstar_Dstar
    a y c (infiniteOddOrientedDeficit c)
      hy hpos' hneg' hPos hFull hprofile hapi

/-- Corollary 10.2 at positive saturation: if the base odd Fourier density
is one, the exact infinite first variation vanishes. -/
theorem infiniteResonantFirstVariation_fourierCoeffOn_eq_zero_of_baseDensity_eq_one
    (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hbase :
      infiniteOddBaseDensity
        (fun n ↦ fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) = 1) :
    infiniteResonantFirstVariation a y
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) = 0 := by
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hbound :=
    abs_infiniteResonantFirstVariation_fourierCoeffOn_le_manuscript
      a y f hy hf hanti hunit
  have hbase' : infiniteOddBaseDensity c = 1 := by
    simpa [c] using hbase
  change infiniteResonantFirstVariation a y c = 0
  change |infiniteResonantFirstVariation a y c| ≤
      2 * ‖a‖ ^ 2 * infiniteOddOrientedDeficit c +
        Real.sqrt 2 *
          (‖a‖ ^ 2 + 4 * ‖a‖ * Real.sqrt (infiniteComplexEnergy y)) *
          Real.sqrt (infiniteOddOrientedDeficit c) at hbound
  have hdelta : infiniteOddOrientedDeficit c = 0 := by
    simp [infiniteOddOrientedDeficit, hbase']
  rw [hdelta] at hbound
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

end

end GromovFilling

#print axioms GromovFilling.infiniteComplexEnergy_nonneg
#print axioms GromovFilling.norm_le_sqrt_infiniteComplexEnergy
#print axioms GromovFilling.norm_tsum_mul_le_sqrt_infiniteComplexEnergy
#print axioms GromovFilling.tsum_normSq_eq_infiniteOddEnergies_of_even_vanishes
#print axioms GromovFilling.summable_odd_fourierCoeffOn_energies
#print axioms GromovFilling.infiniteOddEnergies_fourierCoeffOn_eq_normalizedIntegral
#print axioms GromovFilling.normalized_meanDeficit_eq_one_sub_infiniteOddEnergies
#print axioms GromovFilling.norm_infiniteFullOddShiftCorrelation_fourierCoeffOn_le_deficit_sub_two_neg
#print axioms GromovFilling.norm_infiniteOddMixedCorrelation_le
#print axioms GromovFilling.norm_infiniteNegativeShiftCorrelation_le
#print axioms GromovFilling.norm_infiniteSignedOddShiftCorrelation_le_delta_add_sqrt
#print axioms GromovFilling.abs_infiniteResonantFirstVariation_le_raw
#print axioms GromovFilling.abs_infiniteResonantFirstVariation_le_manuscript
#print axioms GromovFilling.abs_infiniteResonantFirstVariation_le_Cstar_Dstar
#print axioms GromovFilling.tendsto_finiteTruncationResonantFirstVariation
#print axioms GromovFilling.tendsto_finiteTruncationResonantFirstVariation_fourierCoeffOn
#print axioms GromovFilling.abs_infiniteResonantFirstVariation_fourierCoeffOn_le_manuscript
#print axioms GromovFilling.abs_infiniteResonantFirstVariation_fourierCoeffOn_le_Cstar_Dstar
#print axioms GromovFilling.infiniteResonantFirstVariation_fourierCoeffOn_eq_zero_of_baseDensity_eq_one
