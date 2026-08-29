import GromovFilling.NonlinearSymplecticCalculus
import GromovFilling.Oriented

/-!
# Finite nonlinear correlation bounds

This file develops the finite-dimensional Cauchy--Schwarz estimates used by
the quantitative part of Lemma 10.1.  It is deliberately phrased in terms of
finite complex energies so that the later infinite-coordinate passage can use
monotone convergence without changing the algebraic constants.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Squared `ℓ²` energy of a finite complex family. -/
def finiteComplexEnergy {N : ℕ} (c : Fin N → ℂ) : ℝ :=
  ∑ k, Complex.normSq (c k)

lemma finiteComplexEnergy_nonneg {N : ℕ} (c : Fin N → ℂ) :
    0 ≤ finiteComplexEnergy c := by
  unfold finiteComplexEnergy
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

lemma normSq_le_finiteComplexEnergy {N : ℕ}
    (c : Fin N → ℂ) (k : Fin N) :
    Complex.normSq (c k) ≤ finiteComplexEnergy c := by
  unfold finiteComplexEnergy
  exact Finset.single_le_sum
    (fun i _ ↦ Complex.normSq_nonneg (c i)) (Finset.mem_univ k)

lemma norm_le_sqrt_finiteComplexEnergy {N : ℕ}
    (c : Fin N → ℂ) (k : Fin N) :
    ‖c k‖ ≤ Real.sqrt (finiteComplexEnergy c) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [Complex.sq_norm] using normSq_le_finiteComplexEnergy c k

lemma norm_le_one_of_finiteComplexEnergy_le_one {N : ℕ}
    (c : Fin N → ℂ) (henergy : finiteComplexEnergy c ≤ 1) (k : Fin N) :
    ‖c k‖ ≤ 1 := by
  have hsq : ‖c k‖ ^ 2 ≤ 1 := by
    calc
      ‖c k‖ ^ 2 = Complex.normSq (c k) := Complex.sq_norm _
      _ ≤ finiteComplexEnergy c := normSq_le_finiteComplexEnergy c k
      _ ≤ 1 := henergy
  nlinarith [norm_nonneg (c k)]

/-- Dropping the final coordinate cannot increase finite energy. -/
lemma finiteComplexEnergy_castSucc_le {N : ℕ}
    (c : Fin (N + 1) → ℂ) :
    finiteComplexEnergy (fun k : Fin N ↦ c k.castSucc) ≤
      finiteComplexEnergy c := by
  unfold finiteComplexEnergy
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- Dropping the initial coordinate cannot increase finite energy. -/
lemma finiteComplexEnergy_succ_le {N : ℕ}
    (c : Fin (N + 1) → ℂ) :
    finiteComplexEnergy (fun k : Fin N ↦ c k.succ) ≤
      finiteComplexEnergy c := by
  unfold finiteComplexEnergy
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (Complex.normSq_nonneg _)

/-- Finite complex Cauchy--Schwarz, expressed in squared `ℓ²` energies. -/
theorem norm_sum_mul_le_sqrt_finiteComplexEnergy {N : ℕ}
    (f g : Fin N → ℂ) :
    ‖∑ k, f k * g k‖ ≤
      Real.sqrt (finiteComplexEnergy f) *
        Real.sqrt (finiteComplexEnergy g) := by
  calc
    ‖∑ k, f k * g k‖ ≤ ∑ k, ‖f k * g k‖ := norm_sum_le _ _
    _ = ∑ k, ‖f k‖ * ‖g k‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ k, ‖f k‖ ^ 2) *
          Real.sqrt (∑ k, ‖g k‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun k ↦ ‖f k‖) (fun k ↦ ‖g k‖)
    _ = Real.sqrt (finiteComplexEnergy f) *
          Real.sqrt (finiteComplexEnergy g) := by
      simp only [finiteComplexEnergy, Complex.sq_norm]

lemma finiteComplexEnergy_const_mul {N : ℕ}
    (a : ℂ) (f : Fin N → ℂ) :
    finiteComplexEnergy (fun k ↦ a * f k) =
      Complex.normSq a * finiteComplexEnergy f := by
  simp [finiteComplexEnergy, Complex.normSq_mul, Finset.mul_sum]

lemma sqrt_finiteComplexEnergy_const_mul {N : ℕ}
    (a : ℂ) (f : Fin N → ℂ) :
    Real.sqrt (finiteComplexEnergy (fun k ↦ a * f k)) =
      ‖a‖ * Real.sqrt (finiteComplexEnergy f) := by
  rw [finiteComplexEnergy_const_mul, Complex.normSq_eq_norm_sq,
    Real.sqrt_mul (sq_nonneg ‖a‖), Real.sqrt_sq (norm_nonneg a)]

/-- Finite `ℓ²` triangle inequality, stated without introducing a separate
finite-dimensional Hilbert-space wrapper. -/
theorem finiteComplexEnergy_add_le {N : ℕ} (f g : Fin N → ℂ) :
    finiteComplexEnergy (fun k ↦ f k + g k) ≤
      (Real.sqrt (finiteComplexEnergy f) +
        Real.sqrt (finiteComplexEnergy g)) ^ 2 := by
  let cross : ℂ := ∑ k, f k * star (g k)
  have hcross :
      ‖cross‖ ≤ Real.sqrt (finiteComplexEnergy f) *
        Real.sqrt (finiteComplexEnergy g) := by
    calc
      ‖cross‖ ≤ Real.sqrt (finiteComplexEnergy f) *
          Real.sqrt (finiteComplexEnergy (fun k ↦ star (g k))) :=
        norm_sum_mul_le_sqrt_finiteComplexEnergy f (fun k ↦ star (g k))
      _ = Real.sqrt (finiteComplexEnergy f) *
          Real.sqrt (finiteComplexEnergy g) := by
        simp only [finiteComplexEnergy, ← Complex.sq_norm, norm_star]
  have hcrossRe :
      cross.re ≤ Real.sqrt (finiteComplexEnergy f) *
        Real.sqrt (finiteComplexEnergy g) :=
    (le_trans (le_abs_self cross.re) (Complex.abs_re_le_norm cross)).trans hcross
  have hidentity :
      finiteComplexEnergy (fun k ↦ f k + g k) =
        finiteComplexEnergy f + finiteComplexEnergy g + 2 * cross.re := by
    unfold finiteComplexEnergy cross
    simp_rw [Complex.normSq_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Complex.re_sum]
    rfl
  rw [hidentity]
  have hf := Real.sq_sqrt (finiteComplexEnergy_nonneg f)
  have hg := Real.sq_sqrt (finiteComplexEnergy_nonneg g)
  nlinarith

private lemma two_term_cauchy_sq (A B x y : ℝ) :
    (A * x + B * y) ^ 2 ≤
      (A ^ 2 + B ^ 2) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (A * y - B * x)]

/-- Squared `ℓ²` operator bound for the resonant differential. -/
theorem finiteComplexEnergy_resonantDifferentialVariation_le {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ) (p : Fin (N + 1) → ℂ) :
    finiteComplexEnergy (resonantDifferentialVariation a y p) ≤
      (‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y) *
        finiteComplexEnergy p := by
  let first : Fin N → ℂ :=
    fun n ↦ (2 * star a * star (p 0)) * y n
  let second : Fin N → ℂ :=
    fun n ↦ star a ^ 2 * p n.succ
  have hvariation :
      resonantDifferentialVariation a y p =
        fun n ↦ first n + second n := by
    funext n
    unfold resonantDifferentialVariation first second
    ring
  have hfirst :
      Real.sqrt (finiteComplexEnergy first) =
        2 * ‖a‖ * ‖p 0‖ * Real.sqrt (finiteComplexEnergy y) := by
    have h := sqrt_finiteComplexEnergy_const_mul
      (2 * star a * star (p 0)) y
    norm_num at h
    simpa only [first, norm_mul, norm_star] using h
  have hsecond :
      Real.sqrt (finiteComplexEnergy second) =
        ‖a‖ ^ 2 *
          Real.sqrt (finiteComplexEnergy (fun n : Fin N ↦ p n.succ)) := by
    have h := sqrt_finiteComplexEnergy_const_mul
      (star a ^ 2) (fun n : Fin N ↦ p n.succ)
    simpa only [second, norm_pow, norm_star] using h
  have hpEnergy :
      ‖p 0‖ ^ 2 +
          finiteComplexEnergy (fun n : Fin N ↦ p n.succ) =
        finiteComplexEnergy p := by
    unfold finiteComplexEnergy
    rw [Fin.sum_univ_succ, Complex.sq_norm]
  have hySqrt := Real.sq_sqrt (finiteComplexEnergy_nonneg y)
  have hpTailSqrt := Real.sq_sqrt
    (finiteComplexEnergy_nonneg (fun n : Fin N ↦ p n.succ))
  calc
    finiteComplexEnergy (resonantDifferentialVariation a y p) =
        finiteComplexEnergy (fun n ↦ first n + second n) := by rw [hvariation]
    _ ≤ (Real.sqrt (finiteComplexEnergy first) +
          Real.sqrt (finiteComplexEnergy second)) ^ 2 :=
      finiteComplexEnergy_add_le first second
    _ = (2 * ‖a‖ * ‖p 0‖ * Real.sqrt (finiteComplexEnergy y) +
          ‖a‖ ^ 2 *
            Real.sqrt (finiteComplexEnergy (fun n : Fin N ↦ p n.succ))) ^ 2 := by
      rw [hfirst, hsecond]
    _ ≤ ((2 * ‖a‖ * Real.sqrt (finiteComplexEnergy y)) ^ 2 +
          (‖a‖ ^ 2) ^ 2) *
        (‖p 0‖ ^ 2 +
          (Real.sqrt
            (finiteComplexEnergy (fun n : Fin N ↦ p n.succ))) ^ 2) := by
      convert two_term_cauchy_sq
        (2 * ‖a‖ * Real.sqrt (finiteComplexEnergy y))
        (‖a‖ ^ 2) ‖p 0‖
        (Real.sqrt (finiteComplexEnergy (fun n : Fin N ↦ p n.succ))) using 1;
        ring
    _ = (‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y) *
          finiteComplexEnergy p := by
      simp only [hpTailSqrt, hpEnergy]
      ring_nf
      rw [hySqrt]
      ring

/-- The standard finite complex symplectic form is bounded by the product of
the two finite `ℓ²` energies. -/
theorem abs_standardComplexSymplectic_le_sqrt_finiteComplexEnergy
    {N : ℕ} (p q : Fin N → ℂ) :
    |standardComplexSymplectic p q| ≤
      Real.sqrt (finiteComplexEnergy p) *
        Real.sqrt (finiteComplexEnergy q) := by
  calc
    |standardComplexSymplectic p q| =
        |(∑ k, star (p k) * q k).im| := by
      unfold standardComplexSymplectic
      rw [Complex.im_sum]
    _ ≤ ‖∑ k, star (p k) * q k‖ := Complex.abs_im_le_norm _
    _ ≤ Real.sqrt (finiteComplexEnergy (fun k ↦ star (p k))) *
          Real.sqrt (finiteComplexEnergy q) :=
      norm_sum_mul_le_sqrt_finiteComplexEnergy (fun k ↦ star (p k)) q
    _ = Real.sqrt (finiteComplexEnergy p) *
          Real.sqrt (finiteComplexEnergy q) := by
      simp only [finiteComplexEnergy, ← Complex.sq_norm, norm_star]

private lemma sqrt_mul_sqrt_le_average (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt A * Real.sqrt B ≤ (A + B) / 2 := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]

/-- Uniform finite quadratic-variation estimate with the exact resonance
coefficient from the manuscript. -/
theorem abs_finiteResonantQuadraticVariation_le_coefficient {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ) (p q : Fin (N + 1) → ℂ)
    (hpq : finiteComplexEnergy p + finiteComplexEnergy q ≤ 2) :
    |finiteResonantQuadraticVariation a y p q| ≤
      ‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y := by
  let K := ‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y
  have hK : 0 ≤ K := by
    have hy0 := finiteComplexEnergy_nonneg y
    unfold K
    positivity
  have hp := finiteComplexEnergy_resonantDifferentialVariation_le a y p
  have hq := finiteComplexEnergy_resonantDifferentialVariation_le a y q
  have hRp := finiteComplexEnergy_nonneg
    (resonantDifferentialVariation a y p)
  have hRq := finiteComplexEnergy_nonneg
    (resonantDifferentialVariation a y q)
  unfold finiteResonantQuadraticVariation
  calc
    |standardComplexSymplectic
        (resonantDifferentialVariation a y p)
        (resonantDifferentialVariation a y q)| ≤
        Real.sqrt (finiteComplexEnergy
          (resonantDifferentialVariation a y p)) *
          Real.sqrt (finiteComplexEnergy
            (resonantDifferentialVariation a y q)) :=
      abs_standardComplexSymplectic_le_sqrt_finiteComplexEnergy _ _
    _ ≤ (finiteComplexEnergy (resonantDifferentialVariation a y p) +
          finiteComplexEnergy (resonantDifferentialVariation a y q)) / 2 :=
      sqrt_mul_sqrt_le_average _ _ hRp hRq
    _ ≤ (K * finiteComplexEnergy p + K * finiteComplexEnergy q) / 2 := by
      gcongr
    _ = K * (finiteComplexEnergy p + finiteComplexEnergy q) / 2 := by ring
    _ ≤ K * 2 / 2 := by gcongr
    _ = ‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y := by
      unfold K
      ring

/-- The profile and first-mode bounds imply the manuscript's uniform `Qstar`
bound for the finite quadratic variation. -/
theorem abs_finiteResonantQuadraticVariation_le_Qstar {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ) (p q : Fin (N + 1) → ℂ)
    (hprofile : ‖a‖ ^ 2 + 9 * finiteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi)
    (hpq : finiteComplexEnergy p + finiteComplexEnergy q ≤ 2) :
    |finiteResonantQuadraticVariation a y p q| ≤ Qstar := by
  have hy := Real.sq_sqrt (finiteComplexEnergy_nonneg y)
  have hprofile' :
      ‖a‖ ^ 2 + 9 * (Real.sqrt (finiteComplexEnergy y)) ^ 2 ≤ 2 := by
    simpa only [hy] using hprofile
  have hcoefficient := resonance_coefficient_le_Qstar
    ‖a‖ (Real.sqrt (finiteComplexEnergy y)) (norm_nonneg a)
      hprofile' hapi
  exact (abs_finiteResonantQuadraticVariation_le_coefficient
    a y p q hpq).trans (by simpa only [hy] using hcoefficient)

private lemma finiteResonantMixedCorrelation_decomposition {N : ℕ}
    (y : Fin N → ℂ) (cPos cNeg : Fin (N + 1) → ℂ) :
    finiteResonantMixedCorrelation y cPos cNeg =
      -(∑ n : Fin N, y n * star (cNeg n.castSucc)) * cPos 0 +
        star (cNeg 0) * (∑ n : Fin N, y n * cPos n.castSucc) := by
  unfold finiteResonantMixedCorrelation
  calc
    (∑ n : Fin N, y n *
        (-star (cNeg n.castSucc) * cPos 0 +
          star (cNeg 0) * cPos n.castSucc)) =
        ∑ n : Fin N,
          (-(y n * star (cNeg n.castSucc)) * cPos 0 +
            star (cNeg 0) * (y n * cPos n.castSucc)) := by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = -(∑ n : Fin N, y n * star (cNeg n.castSucc)) * cPos 0 +
        star (cNeg 0) * (∑ n : Fin N, y n * cPos n.castSucc) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- The mixed correlation has the manuscript's `2 Y √N` bound when the
positive Fourier energy is at most one. -/
theorem norm_finiteResonantMixedCorrelation_le {N : ℕ}
    (y : Fin N → ℂ) (cPos cNeg : Fin (N + 1) → ℂ)
    (hPos : finiteComplexEnergy cPos ≤ 1) :
    ‖finiteResonantMixedCorrelation y cPos cNeg‖ ≤
      2 * Real.sqrt (finiteComplexEnergy y) *
        Real.sqrt (finiteComplexEnergy cNeg) := by
  let yEnergy := finiteComplexEnergy y
  let negEnergy := finiteComplexEnergy cNeg
  have hy : 0 ≤ Real.sqrt yEnergy := Real.sqrt_nonneg _
  have hn : 0 ≤ Real.sqrt negEnergy := Real.sqrt_nonneg _
  have hnegTail :
      finiteComplexEnergy (fun n : Fin N ↦ cNeg n.castSucc) ≤ negEnergy := by
    exact finiteComplexEnergy_castSucc_le cNeg
  have hposTail :
      finiteComplexEnergy (fun n : Fin N ↦ cPos n.castSucc) ≤
        finiteComplexEnergy cPos := finiteComplexEnergy_castSucc_le cPos
  have hsqrtNegTail :
      Real.sqrt (finiteComplexEnergy (fun n : Fin N ↦ cNeg n.castSucc)) ≤
        Real.sqrt negEnergy := Real.sqrt_le_sqrt hnegTail
  have hsqrtPosTail :
      Real.sqrt (finiteComplexEnergy (fun n : Fin N ↦ cPos n.castSucc)) ≤ 1 := by
    have htailOne := hposTail.trans hPos
    nlinarith [Real.sq_sqrt (finiteComplexEnergy_nonneg
      (fun n : Fin N ↦ cPos n.castSucc)), Real.sqrt_nonneg
        (finiteComplexEnergy (fun n : Fin N ↦ cPos n.castSucc))]
  have hfirst :
      ‖∑ n : Fin N, y n * star (cNeg n.castSucc)‖ ≤
        Real.sqrt yEnergy * Real.sqrt negEnergy := by
    calc
      ‖∑ n : Fin N, y n * star (cNeg n.castSucc)‖ ≤
          Real.sqrt yEnergy *
            Real.sqrt (finiteComplexEnergy
              (fun n : Fin N ↦ star (cNeg n.castSucc))) :=
        norm_sum_mul_le_sqrt_finiteComplexEnergy y
          (fun n : Fin N ↦ star (cNeg n.castSucc))
      _ = Real.sqrt yEnergy *
            Real.sqrt (finiteComplexEnergy
              (fun n : Fin N ↦ cNeg n.castSucc)) := by
        simp only [finiteComplexEnergy, ← Complex.sq_norm, norm_star]
      _ ≤ Real.sqrt yEnergy * Real.sqrt negEnergy := by gcongr
  have hsecond :
      ‖∑ n : Fin N, y n * cPos n.castSucc‖ ≤
        Real.sqrt yEnergy := by
    calc
      ‖∑ n : Fin N, y n * cPos n.castSucc‖ ≤
          Real.sqrt yEnergy *
            Real.sqrt (finiteComplexEnergy
              (fun n : Fin N ↦ cPos n.castSucc)) :=
        norm_sum_mul_le_sqrt_finiteComplexEnergy y
          (fun n : Fin N ↦ cPos n.castSucc)
      _ ≤ Real.sqrt yEnergy * 1 := by gcongr
      _ = Real.sqrt yEnergy := mul_one _
  rw [finiteResonantMixedCorrelation_decomposition]
  calc
    ‖-(∑ n : Fin N, y n * star (cNeg n.castSucc)) * cPos 0 +
        star (cNeg 0) * (∑ n : Fin N, y n * cPos n.castSucc)‖ ≤
        ‖-(∑ n : Fin N, y n * star (cNeg n.castSucc)) * cPos 0‖ +
          ‖star (cNeg 0) *
            (∑ n : Fin N, y n * cPos n.castSucc)‖ := norm_add_le _ _
    _ = ‖∑ n : Fin N, y n * star (cNeg n.castSucc)‖ * ‖cPos 0‖ +
          ‖cNeg 0‖ * ‖∑ n : Fin N, y n * cPos n.castSucc‖ := by
      simp only [norm_mul, norm_neg, norm_star]
    _ ≤ (Real.sqrt yEnergy * Real.sqrt negEnergy) * 1 +
          Real.sqrt negEnergy * Real.sqrt yEnergy := by
      gcongr
      · exact norm_le_one_of_finiteComplexEnergy_le_one cPos hPos 0
      · exact norm_le_sqrt_finiteComplexEnergy cNeg 0
    _ = 2 * Real.sqrt yEnergy * Real.sqrt negEnergy := by ring

/-- Positive-frequency part of the shift-two autocorrelation. -/
def finitePositiveShiftCorrelation {N : ℕ}
    (cPos : Fin (N + 1) → ℂ) : ℂ :=
  ∑ n : Fin N, cPos n.castSucc * star (cPos n.succ)

/-- Negative-frequency part of the shift-two autocorrelation, written with
the convention used in the manuscript. -/
def finiteNegativeShiftCorrelation {N : ℕ}
    (cNeg : Fin (N + 1) → ℂ) : ℂ :=
  ∑ n : Fin N, star (cNeg n.castSucc) * cNeg n.succ

/-- The finite full shift-two correlation, including the crossing term at
frequencies `-1` and `1`. -/
def finiteFullShiftCorrelation {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) : ℂ :=
  finitePositiveShiftCorrelation cPos +
    finiteNegativeShiftCorrelation cNeg +
    cNeg 0 * star (cPos 0)

lemma finiteResonantShiftCorrelation_eq {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) :
    finiteResonantShiftCorrelation cPos cNeg =
      finitePositiveShiftCorrelation cPos -
        finiteNegativeShiftCorrelation cNeg := by
  unfold finiteResonantShiftCorrelation finitePositiveShiftCorrelation
    finiteNegativeShiftCorrelation
  rw [Finset.sum_sub_distrib]

/-- The negative shift correlation is bounded by the total negative Fourier
energy. -/
theorem norm_finiteNegativeShiftCorrelation_le {N : ℕ}
    (cNeg : Fin (N + 1) → ℂ) :
    ‖finiteNegativeShiftCorrelation cNeg‖ ≤ finiteComplexEnergy cNeg := by
  let negEnergy := finiteComplexEnergy cNeg
  have hneg : 0 ≤ negEnergy := finiteComplexEnergy_nonneg cNeg
  have hcast :
      finiteComplexEnergy (fun n : Fin N ↦ star (cNeg n.castSucc)) ≤
        negEnergy := by
    simpa only [negEnergy, finiteComplexEnergy, ← Complex.sq_norm,
      norm_star] using
      finiteComplexEnergy_castSucc_le cNeg
  have hsucc :
      finiteComplexEnergy (fun n : Fin N ↦ cNeg n.succ) ≤ negEnergy :=
    finiteComplexEnergy_succ_le cNeg
  unfold finiteNegativeShiftCorrelation
  calc
    ‖∑ n : Fin N, star (cNeg n.castSucc) * cNeg n.succ‖ ≤
        Real.sqrt (finiteComplexEnergy
            (fun n : Fin N ↦ star (cNeg n.castSucc))) *
          Real.sqrt (finiteComplexEnergy
            (fun n : Fin N ↦ cNeg n.succ)) :=
      norm_sum_mul_le_sqrt_finiteComplexEnergy
        (fun n : Fin N ↦ star (cNeg n.castSucc))
        (fun n : Fin N ↦ cNeg n.succ)
    _ ≤ Real.sqrt negEnergy * Real.sqrt negEnergy := by
      gcongr
    _ = negEnergy := Real.mul_self_sqrt hneg

/-- Quantitative finite shift-correlation estimate.  The hypothesis is the
finite analogue of bounding a nonzero Fourier coefficient of `1 - |W|²` by
its mean deficit. -/
theorem norm_finiteResonantShiftCorrelation_le_delta_add_sqrt {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) (delta : ℝ)
    (hPos : finiteComplexEnergy cPos ≤ 1)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg) :
    ‖finiteResonantShiftCorrelation cPos cNeg‖ ≤
      delta + Real.sqrt (delta / 2) := by
  let negEnergy := finiteComplexEnergy cNeg
  have hneg : 0 ≤ negEnergy := finiteComplexEnergy_nonneg cNeg
  have hdeltaNeg : negEnergy ≤ delta / 2 := by
    have hfullNonneg : 0 ≤ ‖finiteFullShiftCorrelation cPos cNeg‖ :=
      norm_nonneg _
    linarith
  have hsqrtNeg : Real.sqrt negEnergy ≤ Real.sqrt (delta / 2) :=
    Real.sqrt_le_sqrt hdeltaNeg
  have hcross :
      ‖cNeg 0 * star (cPos 0)‖ ≤ Real.sqrt negEnergy := by
    calc
      ‖cNeg 0 * star (cPos 0)‖ = ‖cNeg 0‖ * ‖cPos 0‖ := by
        simp only [norm_mul, norm_star]
      _ ≤ Real.sqrt negEnergy * 1 := by
        gcongr
        · exact norm_le_sqrt_finiteComplexEnergy cNeg 0
        · exact norm_le_one_of_finiteComplexEnergy_le_one cPos hPos 0
      _ = Real.sqrt negEnergy := mul_one _
  have hnegative := norm_finiteNegativeShiftCorrelation_le cNeg
  have hidentity :
      finiteResonantShiftCorrelation cPos cNeg =
        finiteFullShiftCorrelation cPos cNeg -
          cNeg 0 * star (cPos 0) -
          2 * finiteNegativeShiftCorrelation cNeg := by
    rw [finiteResonantShiftCorrelation_eq]
    unfold finiteFullShiftCorrelation
    ring
  rw [hidentity]
  calc
    ‖finiteFullShiftCorrelation cPos cNeg -
        cNeg 0 * star (cPos 0) -
        2 * finiteNegativeShiftCorrelation cNeg‖ ≤
        ‖finiteFullShiftCorrelation cPos cNeg‖ +
          ‖cNeg 0 * star (cPos 0)‖ +
          ‖2 * finiteNegativeShiftCorrelation cNeg‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (delta - 2 * negEnergy) + Real.sqrt negEnergy +
          2 * negEnergy := by
      calc
        ‖finiteFullShiftCorrelation cPos cNeg‖ +
            ‖cNeg 0 * star (cPos 0)‖ +
            ‖2 * finiteNegativeShiftCorrelation cNeg‖ ≤
            (delta - 2 * negEnergy) + Real.sqrt negEnergy +
              2 * ‖finiteNegativeShiftCorrelation cNeg‖ := by
          have htwo :
              ‖(2 : ℂ) * finiteNegativeShiftCorrelation cNeg‖ =
                2 * ‖finiteNegativeShiftCorrelation cNeg‖ := by
            rw [norm_mul]
            norm_num
          rw [htwo]
          exact add_le_add (add_le_add hFull hcross)
            le_rfl
        _ ≤ (delta - 2 * negEnergy) + Real.sqrt negEnergy +
              2 * negEnergy := by gcongr
    _ = delta + Real.sqrt negEnergy := by ring
    _ ≤ delta + Real.sqrt (delta / 2) := by gcongr

private lemma abs_two_re_add_four_re_le (u v : ℂ) :
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

/-- Direct finite first-variation estimate before rewriting
`√(δ / 2)` as `√2 √δ / 2`. -/
theorem abs_finiteResonantFirstVariation_le_raw {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ) (delta : ℝ)
    (hPos : finiteComplexEnergy cPos ≤ 1)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg) :
    |finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤
      2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
        8 * ‖a‖ * Real.sqrt (finiteComplexEnergy y) *
          Real.sqrt (delta / 2) := by
  let negEnergy := finiteComplexEnergy cNeg
  have hneg : 0 ≤ negEnergy := finiteComplexEnergy_nonneg cNeg
  have hnegDelta : negEnergy ≤ delta / 2 := by
    have hfullNonneg : 0 ≤ ‖finiteFullShiftCorrelation cPos cNeg‖ :=
      norm_nonneg _
    linarith
  have hsqrtNeg : Real.sqrt negEnergy ≤ Real.sqrt (delta / 2) :=
    Real.sqrt_le_sqrt hnegDelta
  have hshift := norm_finiteResonantShiftCorrelation_le_delta_add_sqrt
    cPos cNeg delta hPos hFull
  have hmixed := norm_finiteResonantMixedCorrelation_le y cPos cNeg hPos
  rw [finiteResonant_firstVariation_eq_correlations]
  unfold finiteResonantCorrelationFirstVariation
  calc
    |2 *
          (star a ^ 2 * finiteResonantShiftCorrelation cPos cNeg).re +
        4 *
          (star a * finiteResonantMixedCorrelation y cPos cNeg).re| ≤
        2 * ‖star a ^ 2 * finiteResonantShiftCorrelation cPos cNeg‖ +
          4 * ‖star a * finiteResonantMixedCorrelation y cPos cNeg‖ :=
      abs_two_re_add_four_re_le _ _
    _ = 2 * ‖a‖ ^ 2 * ‖finiteResonantShiftCorrelation cPos cNeg‖ +
          4 * ‖a‖ * ‖finiteResonantMixedCorrelation y cPos cNeg‖ := by
      simp only [norm_mul, norm_pow, norm_star]
      ring
    _ ≤ 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ *
            (2 * Real.sqrt (finiteComplexEnergy y) *
              Real.sqrt negEnergy) := by
      gcongr
    _ ≤ 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          4 * ‖a‖ *
            (2 * Real.sqrt (finiteComplexEnergy y) *
              Real.sqrt (delta / 2)) := by
      gcongr
    _ = 2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          8 * ‖a‖ * Real.sqrt (finiteComplexEnergy y) *
            Real.sqrt (delta / 2) := by ring

private lemma sqrt_div_two_eq (delta : ℝ) (hdelta : 0 ≤ delta) :
    Real.sqrt (delta / 2) =
      Real.sqrt 2 * Real.sqrt delta / 2 := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  have hhalf : 0 ≤ delta / 2 := by positivity
  have hsHalf := Real.sq_sqrt hhalf
  have hsDelta := Real.sq_sqrt hdelta
  have hsTwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- Finite first-variation bound in exactly the quantitative form used in
the manuscript and by `firstVariation_le_Cstar_Dstar`. -/
theorem abs_finiteResonantFirstVariation_le_manuscript {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ) (delta : ℝ)
    (hPos : finiteComplexEnergy cPos ≤ 1)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg) :
    |finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤
      2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 +
            4 * ‖a‖ * Real.sqrt (finiteComplexEnergy y)) *
          Real.sqrt delta := by
  have hdelta : 0 ≤ delta := by
    have hneg := finiteComplexEnergy_nonneg cNeg
    have hfullNonneg : 0 ≤ ‖finiteFullShiftCorrelation cPos cNeg‖ :=
      norm_nonneg _
    linarith
  have hraw := abs_finiteResonantFirstVariation_le_raw
    a y cPos cNeg delta hPos hFull
  calc
    |finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤
        2 * ‖a‖ ^ 2 * (delta + Real.sqrt (delta / 2)) +
          8 * ‖a‖ * Real.sqrt (finiteComplexEnergy y) *
            Real.sqrt (delta / 2) := hraw
    _ = 2 * ‖a‖ ^ 2 * delta +
        Real.sqrt 2 *
          (‖a‖ ^ 2 +
            4 * ‖a‖ * Real.sqrt (finiteComplexEnergy y)) *
          Real.sqrt delta := by
      rw [sqrt_div_two_eq delta hdelta]
      ring

private lemma fourier_pair_energy_pointwise (c b : ℂ) :
    Complex.normSq (b + star c) +
        Complex.normSq (Complex.I * (star c - b)) =
      2 * (Complex.normSq c + Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The two reconstructed real tangent vectors have twice the total Fourier
coefficient energy. -/
theorem finiteFourier_pair_energy {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) :
    finiteComplexEnergy (finiteFourierTangentVector cPos cNeg) +
        finiteComplexEnergy (finiteFourierQuarterTurnVector cPos cNeg) =
      2 * (finiteComplexEnergy cPos + finiteComplexEnergy cNeg) := by
  unfold finiteComplexEnergy
  calc
    (∑ k, Complex.normSq (finiteFourierTangentVector cPos cNeg k)) +
        ∑ k, Complex.normSq (finiteFourierQuarterTurnVector cPos cNeg k) =
        ∑ k,
          (Complex.normSq (finiteFourierTangentVector cPos cNeg k) +
            Complex.normSq
              (finiteFourierQuarterTurnVector cPos cNeg k)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ k, 2 * (Complex.normSq (cPos k) + Complex.normSq (cNeg k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact fourier_pair_energy_pointwise (cPos k) (cNeg k)
    _ = 2 * ((∑ k, Complex.normSq (cPos k)) +
        ∑ k, Complex.normSq (cNeg k)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- The finite first variation feeds directly into the already verified
`Cstar`, `Dstar` scalar estimate. -/
theorem abs_finiteResonantFirstVariation_le_Cstar_Dstar {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ) (delta : ℝ)
    (hPos : finiteComplexEnergy cPos ≤ 1)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg)
    (hprofile : ‖a‖ ^ 2 + 9 * finiteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤
      Cstar * Real.sqrt delta + Dstar * delta := by
  have hdelta : 0 ≤ delta := by
    have hneg := finiteComplexEnergy_nonneg cNeg
    have hfullNonneg : 0 ≤ ‖finiteFullShiftCorrelation cPos cNeg‖ :=
      norm_nonneg _
    linarith
  have hy := Real.sq_sqrt (finiteComplexEnergy_nonneg y)
  apply firstVariation_le_Cstar_Dstar
    ‖a‖ (Real.sqrt (finiteComplexEnergy y)) delta
      (finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg))
      (norm_nonneg a) hdelta
  · simpa only [hy] using hprofile
  · exact hapi
  · exact abs_finiteResonantFirstVariation_le_manuscript
      a y cPos cNeg delta hPos hFull

/-- Finite nonlinear comass assembly.  All analytic input is exposed as the
coefficient-energy, profile, autocorrelation-deficit, and base-density
hypotheses that must later be supplied almost everywhere by the distance
profile. -/
theorem abs_finiteResonantSymplectic_le_comassBound {N : ℕ}
    (lam delta : ℝ) (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hcoeffEnergy :
      finiteComplexEnergy cPos + finiteComplexEnergy cNeg ≤ 1)
    (hbase :
      |finiteBaseSymplecticDensity
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤ 1 - delta)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg)
    (hprofile : ‖a‖ ^ 2 + 9 * finiteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |standardComplexSymplectic
        (finiteResonantTangentMap lam a y
          (finiteFourierTangentVector cPos cNeg))
        (finiteResonantTangentMap lam a y
          (finiteFourierQuarterTurnVector cPos cNeg))| ≤
      comassBound lam := by
  have hPos : finiteComplexEnergy cPos ≤ 1 := by
    have hneg := finiteComplexEnergy_nonneg cNeg
    linarith
  have hpq :
      finiteComplexEnergy (finiteFourierTangentVector cPos cNeg) +
          finiteComplexEnergy (finiteFourierQuarterTurnVector cPos cNeg) ≤ 2 := by
    rw [finiteFourier_pair_energy]
    linarith
  have hdelta : 0 ≤ delta := by
    have hneg := finiteComplexEnergy_nonneg cNeg
    have hfullNonneg : 0 ≤ ‖finiteFullShiftCorrelation cPos cNeg‖ :=
      norm_nonneg _
    linarith
  have hL := abs_finiteResonantFirstVariation_le_Cstar_Dstar
    a y cPos cNeg delta hPos hFull hprofile hapi
  have hQ := abs_finiteResonantQuadraticVariation_le_Qstar
    a y (finiteFourierTangentVector cPos cNeg)
      (finiteFourierQuarterTurnVector cPos cNeg) hprofile hapi hpq
  have homega :
      |standardComplexSymplectic
          (finiteResonantTangentMap lam a y
            (finiteFourierTangentVector cPos cNeg))
          (finiteResonantTangentMap lam a y
            (finiteFourierQuarterTurnVector cPos cNeg))| ≤
        1 - delta +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by
    rw [finiteResonant_symplectic_expansion]
    calc
      |finiteBaseSymplecticDensity
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg) +
          lam * finiteResonantFirstVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg) +
          lam ^ 2 * finiteResonantQuadraticVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| ≤
          |finiteBaseSymplecticDensity
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| +
          |lam * finiteResonantFirstVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| +
          |lam ^ 2 * finiteResonantQuadraticVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ = |finiteBaseSymplecticDensity
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| +
          lam * |finiteResonantFirstVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| +
          lam ^ 2 * |finiteResonantQuadraticVariation a y
            (finiteFourierTangentVector cPos cNeg)
            (finiteFourierQuarterTurnVector cPos cNeg)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hlam0,
          abs_of_nonneg (sq_nonneg lam)]
      _ ≤ (1 - delta) +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          lam ^ 2 * Qstar := by gcongr
      _ = 1 - delta +
          lam * (Cstar * Real.sqrt delta + Dstar * delta) +
          Qstar * lam ^ 2 := by ring
  unfold comassBound
  exact nonlinear_comass_optimization lam Cstar Dstar Qstar
    (standardComplexSymplectic
      (finiteResonantTangentMap lam a y
        (finiteFourierTangentVector cPos cNeg))
      (finiteResonantTangentMap lam a y
        (finiteFourierQuarterTurnVector cPos cNeg)))
    delta hdelta (comass_denominator_pos_of_admissible hlam) homega

#print axioms norm_sum_mul_le_sqrt_finiteComplexEnergy
#print axioms finiteComplexEnergy_resonantDifferentialVariation_le
#print axioms abs_finiteResonantQuadraticVariation_le_Qstar
#print axioms norm_finiteResonantMixedCorrelation_le
#print axioms norm_finiteNegativeShiftCorrelation_le
#print axioms norm_finiteResonantShiftCorrelation_le_delta_add_sqrt
#print axioms abs_finiteResonantFirstVariation_le_raw
#print axioms abs_finiteResonantFirstVariation_le_manuscript
#print axioms finiteFourier_pair_energy
#print axioms abs_finiteResonantFirstVariation_le_Cstar_Dstar
#print axioms abs_finiteResonantSymplectic_le_comassBound

end

end GromovFilling
