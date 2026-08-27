import GromovFilling.DominantHarmonicDisk
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex

/-!
# Jacobian area of a dominant-harmonic polynomial disk

This file supplies the analytic half of the polynomial-disk model.  The
real Jacobian of a holomorphic polynomial is the squared norm of its complex
derivative, and the injective change-of-variables theorem identifies the
Lebesgue measure of the disk image with the corresponding disk integral.
-/

open MeasureTheory Set intervalIntegral
open scoped BigOperators ENNReal

namespace GromovFilling

noncomputable section

/-- The complex derivative of `dominantHarmonicPolynomial`. -/
def dominantHarmonicPolynomialDeriv {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  a₁ + ∑ k, (m k : ℂ) * a k * z ^ (m k - 1)

theorem hasDerivAt_dominantHarmonicPolynomial
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ℂ) :
    HasDerivAt (dominantHarmonicPolynomial a₁ m a)
      (dominantHarmonicPolynomialDeriv a₁ m a z) z := by
  unfold dominantHarmonicPolynomial dominantHarmonicPolynomialDeriv
  apply HasDerivAt.add
  · simpa only [mul_one] using (hasDerivAt_id z).const_mul a₁
  · have hsum : HasDerivAt
        (∑ k, fun w : ℂ ↦ a k * w ^ m k)
        (∑ k, (m k : ℂ) * a k * z ^ (m k - 1)) z := by
      apply HasDerivAt.sum
      intro k _
      convert ((hasDerivAt_id z).pow (m k)).const_mul (a k) using 1
      simp only [id_eq]
      ring
    rw [Finset.sum_fn] at hsum
    exact hsum

/-- Complex scalar multiplication has real determinant equal to the squared
complex norm of the scalar. -/
theorem det_complex_smul_one (c : ℂ) :
    (c • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq c := by
  change LinearMap.det (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap = _
  have hmap :
      (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap = Algebra.lmul ℝ ℂ c := by
    ext z
    change c * z = c * z
    rfl
  rw [hmap]
  calc
    LinearMap.det (Algebra.lmul ℝ ℂ c) =
        (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          (Algebra.lmul ℝ ℂ c)).det :=
      (LinearMap.det_toMatrix Complex.basisOneI
        (Algebra.lmul ℝ ℂ c)).symm
    _ = (Algebra.leftMulMatrix Complex.basisOneI c).det := rfl
    _ = Complex.normSq c := by
      rw [Algebra.leftMulMatrix_complex, Matrix.det_fin_two]
      simp [Complex.normSq_apply]

/-- The real Fréchet derivative of the polynomial has determinant equal to
the squared norm of its complex derivative. -/
theorem det_fderiv_dominantHarmonicPolynomial
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ℂ) :
    (fderiv ℝ (dominantHarmonicPolynomial a₁ m a) z).det =
      Complex.normSq (dominantHarmonicPolynomialDeriv a₁ m a z) := by
  have hreal :=
    (hasDerivAt_dominantHarmonicPolynomial a₁ m a z).complexToReal_fderiv
  rw [hreal.fderiv]
  exact det_complex_smul_one _

set_option backward.isDefEq.respectTransparency false in
/-- Orthogonality of the integer complex exponentials on `[-π, π]`. -/
theorem integral_cexp_int_mul_I (d : ℤ) :
    (∫ t in -Real.pi..Real.pi,
      Complex.exp ((d : ℂ) * t * Complex.I)) =
      if d = 0 then 2 * Real.pi else 0 := by
  by_cases hd : d = 0
  · subst d
    rw [if_pos rfl]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const]
    simp only [Complex.real_smul]
    push_cast
    ring
  · rw [if_neg hd]
    have hc : (d : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hd) Complex.I_ne_zero
    have hfun :
        (fun t : ℝ ↦ Complex.exp ((d : ℂ) * t * Complex.I)) =
          fun t : ℝ ↦ Complex.exp (((d : ℂ) * Complex.I) * t) := by
      funext t
      congr 1
      ring
    rw [hfun, integral_exp_mul_complex
      (c := (d : ℂ) * Complex.I) hc]
    have hexp :
        Complex.exp (((d : ℂ) * Complex.I) * Real.pi) =
          Complex.exp (((d : ℂ) * Complex.I) * (-Real.pi)) := by
      rw [show ((d : ℂ) * Complex.I) * Real.pi =
          ((d : ℂ) * Complex.I) * (-Real.pi) +
            (d : ℂ) * (2 * Real.pi * Complex.I) by ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    push_cast
    rw [hexp, sub_self, zero_div]

/-- The elementary radial moment used in the disk monomial integral. -/
theorem integral_Ioo_zero_one_complex_pow (n : ℕ) :
    (∫ r : ℝ in Ioo 0 1, ((r : ℂ) ^ n)) =
      (1 : ℂ) / (n + 1) := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
  rw [← intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)]
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal]
  rw [integral_pow]
  push_cast
  norm_num

/-- Orthogonality and normalization of complex monomials on the open unit
disk.  The proof includes the polar-coordinate Jacobian `r`. -/
theorem integral_ball_monomial_mul_conj (p q : ℕ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      z ^ p * starRingEnd ℂ (z ^ q) ∂volume) =
      if p = q then (Real.pi : ℂ) / (p + 1) else 0 := by
  let T : Set (ℝ × ℝ) := Complex.polarCoord.target
  let S : Set (ℝ × ℝ) := {x | x.1 < 1}
  let F : ℂ → ℂ := fun z ↦ z ^ p * starRingEnd ℂ (z ^ q)
  have hT : T = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi :=
    Complex.polarCoord_target
  have hSMeasurable : MeasurableSet S :=
    measurableSet_lt measurable_fst measurable_const
  have hTS :
      T ∩ S = Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext x
    simp only [T, S, hT, mem_inter_iff, mem_prod, mem_Ioi,
      mem_Ioo, mem_setOf_eq]
    tauto
  have hpolar (r t : ℝ) :
      r • F (Complex.polarCoord.symm (r, t)) =
        (r : ℂ) ^ (p + q + 1) *
          Complex.exp ((((p : ℤ) - (q : ℤ) : ℤ) : ℂ) *
            t * Complex.I) := by
    dsimp only [F]
    rw [Complex.polarCoord_symm_apply]
    have he : (Real.cos t + Real.sin t * Complex.I : ℂ) =
        Complex.exp (t * Complex.I) := by
      rw [Complex.exp_mul_I]
      norm_cast
    rw [he]
    simp only [map_pow, map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul]
    push_cast
    simp only [Complex.real_smul]
    rw [pow_succ, pow_add]
    calc
      _ = ((r : ℂ) ^ p * (r : ℂ) ^ q * r) *
          (Complex.exp ((p : ℂ) * (t * Complex.I)) *
            Complex.exp ((q : ℂ) * (-(t * Complex.I)))) := by ring
      _ = ((r : ℂ) ^ p * (r : ℂ) ^ q * r) *
          Complex.exp ((((p : ℂ) - (q : ℂ)) *
            t * Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
  calc
    (∫ z in Metric.ball (0 : ℂ) 1,
        z ^ p * starRingEnd ℂ (z ^ q) ∂volume) =
        ∫ z : ℂ, (Metric.ball (0 : ℂ) 1).indicator F z ∂volume :=
      (MeasureTheory.integral_indicator measurableSet_ball).symm
    _ = ∫ x in T, x.1 •
        (Metric.ball (0 : ℂ) 1).indicator F
          (Complex.polarCoord.symm x) ∂volume := by
      simpa only [T] using
        (Complex.integral_comp_polarCoord_symm
          ((Metric.ball (0 : ℂ) 1).indicator F)).symm
    _ = ∫ x in T, S.indicator
        (fun x ↦ x.1 • F (Complex.polarCoord.symm x)) x ∂volume := by
      apply setIntegral_congr_fun
        Complex.polarCoord.open_target.measurableSet
      intro x hx
      have hxpos : 0 < x.1 := by
        have hx' : x ∈ T := by simpa only [T] using hx
        rw [hT] at hx'
        exact hx'.1
      have hball :
          Complex.polarCoord.symm x ∈ Metric.ball (0 : ℂ) 1 ↔
            x ∈ S := by
        rw [Metric.mem_ball, dist_zero_right,
          Complex.norm_polarCoord_symm, abs_of_pos hxpos]
        rfl
      change x.1 • (Metric.ball (0 : ℂ) 1).indicator F
          (Complex.polarCoord.symm x) =
        S.indicator
          (fun y ↦ y.1 • F (Complex.polarCoord.symm y)) x
      by_cases hxS : x ∈ S
      · rw [Set.indicator_of_mem hxS,
          Set.indicator_of_mem (hball.mpr hxS)]
      · rw [Set.indicator_of_notMem hxS,
          Set.indicator_of_notMem (fun h ↦ hxS (hball.mp h)),
          Complex.real_smul, mul_zero]
    _ = ∫ x in T ∩ S,
        x.1 • F (Complex.polarCoord.symm x) ∂volume :=
      setIntegral_indicator hSMeasurable
    _ = ∫ x in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        (x.1 : ℂ) ^ (p + q + 1) *
          Complex.exp ((((p : ℤ) - (q : ℤ) : ℤ) : ℂ) *
            x.2 * Complex.I) ∂volume := by
      rw [hTS]
      apply setIntegral_congr_fun
        (measurableSet_Ioo.prod measurableSet_Ioo)
      intro x _
      exact hpolar x.1 x.2
    _ = (∫ r : ℝ in Ioo 0 1, (r : ℂ) ^ (p + q + 1)) *
        ∫ t : ℝ in Ioo (-Real.pi) Real.pi,
          Complex.exp ((((p : ℤ) - (q : ℤ) : ℤ) : ℂ) *
            t * Complex.I) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact setIntegral_prod_mul
        (fun r : ℝ ↦ (r : ℂ) ^ (p + q + 1))
        (fun t : ℝ ↦
          Complex.exp ((((p : ℤ) - (q : ℤ) : ℤ) : ℂ) *
            t * Complex.I))
        (Ioo (0 : ℝ) 1) (Ioo (-Real.pi) Real.pi)
    _ = (1 : ℂ) / (p + q + 2) *
        (if (p : ℤ) - (q : ℤ) = 0 then 2 * Real.pi else 0) := by
      rw [integral_Ioo_zero_one_complex_pow]
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
      rw [← intervalIntegral.integral_of_le
        (by linarith [Real.pi_pos])]
      rw [integral_cexp_int_mul_I]
      push_cast
      rw [show (p : ℂ) + q + 1 + 1 = p + q + 2 by ring]
    _ = if p = q then (Real.pi : ℂ) / (p + 1) else 0 := by
      by_cases hpq : p = q
      · subst q
        rw [if_pos rfl, if_pos (sub_self _)]
        push_cast
        have h₁ : (p : ℂ) + 1 ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero p
        rw [show (p : ℂ) + p + 2 = 2 * (p + 1) by ring]
        field_simp [h₁]
      · rw [if_neg hpq]
        have hne : (p : ℤ) - (q : ℤ) ≠ 0 := by omega
        simp [if_neg hne]

/-- A finite complex polynomial written directly as a sum of monomials. -/
def finiteMonomialSum {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (b : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, b i * z ^ n i

/-- Parseval's identity on the unit disk for a finite collection of
monomials with distinct exponents. -/
theorem integral_ball_finiteMonomialSum_mul_conj
    {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (b : ι → ℂ) (hn : Function.Injective n) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      finiteMonomialSum n b z *
        starRingEnd ℂ (finiteMonomialSum n b z) ∂volume) =
      (Real.pi : ℂ) * ∑ i,
        (Complex.normSq (b i) : ℂ) / (n i + 1) := by
  have hexpand (z : ℂ) :
      finiteMonomialSum n b z *
          starRingEnd ℂ (finiteMonomialSum n b z) =
        ∑ i, ∑ j,
          (b i * starRingEnd ℂ (b j)) *
            (z ^ n i * starRingEnd ℂ (z ^ n j)) := by
    unfold finiteMonomialSum
    simp only [map_sum, map_mul, map_pow, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintegrable (i j : ι) :
      IntegrableOn
        (fun z : ℂ ↦
          (b i * starRingEnd ℂ (b j)) *
            (z ^ n i * starRingEnd ℂ (z ^ n j)))
        (Metric.ball (0 : ℂ) 1) := by
    apply IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) 1)
        (by fun_prop : ContinuousOn
          (fun z : ℂ ↦
            (b i * starRingEnd ℂ (b j)) *
              (z ^ n i * starRingEnd ℂ (z ^ n j)))
          (Metric.closedBall (0 : ℂ) 1)))
    exact Metric.ball_subset_closedBall
  calc
    (∫ z in Metric.ball (0 : ℂ) 1,
        finiteMonomialSum n b z *
          starRingEnd ℂ (finiteMonomialSum n b z) ∂volume) =
        ∫ z in Metric.ball (0 : ℂ) 1,
          ∑ i, ∑ j,
            (b i * starRingEnd ℂ (b j)) *
              (z ^ n i * starRingEnd ℂ (z ^ n j)) ∂volume := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z _
      exact hexpand z
    _ = ∑ i, ∑ j,
        ∫ z in Metric.ball (0 : ℂ) 1,
          (b i * starRingEnd ℂ (b j)) *
            (z ^ n i * starRingEnd ℂ (z ^ n j)) ∂volume := by
      rw [integral_finset_sum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finset_sum Finset.univ]
        intro j _
        exact hintegrable i j
      · intro i _
        exact integrable_finset_sum Finset.univ
          (fun j _ ↦ hintegrable i j)
    _ = ∑ i, ∑ j,
        (b i * starRingEnd ℂ (b j)) *
          (if n i = n j then (Real.pi : ℂ) / (n i + 1)
            else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (b i * starRingEnd ℂ (b j)) *
            ∫ z in Metric.ball (0 : ℂ) 1,
              z ^ n i * starRingEnd ℂ (z ^ n j) ∂volume :=
          MeasureTheory.integral_const_mul _ _
        _ = _ := by rw [integral_ball_monomial_mul_conj]
    _ = (Real.pi : ℂ) * ∑ i,
        (Complex.normSq (b i) : ℂ) / (n i + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      · intro j _ hji
        rw [if_neg (fun h ↦ hji (hn h).symm), mul_zero]
      · simp

/-- The complex-valued form of the exact disk integral of the derivative of
a dominant-harmonic polynomial. -/
theorem integral_ball_dominantHarmonicPolynomialDeriv_normSq_complex
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ i, 2 ≤ m i) (hminj : Function.Injective m) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      (Complex.normSq
        (dominantHarmonicPolynomialDeriv a₁ m a z) : ℂ) ∂volume) =
      (Real.pi : ℂ) *
        ((Complex.normSq a₁ : ℂ) +
          ∑ i, (m i : ℂ) * (Complex.normSq (a i) : ℂ)) := by
  let n : Option ι → ℕ := fun o ↦ o.elim 0 (fun i ↦ m i - 1)
  let b : Option ι → ℂ := fun o ↦
    o.elim a₁ (fun i ↦ (m i : ℂ) * a i)
  have hn : Function.Injective n := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some j =>
            dsimp only [n, Option.elim_none, Option.elim_some] at hxy
            have hj := hm j
            omega
    | some i =>
        cases y with
        | none =>
            dsimp only [n, Option.elim_none, Option.elim_some] at hxy
            have hi := hm i
            omega
        | some j =>
            congr 1
            apply hminj
            dsimp only [n, Option.elim_some] at hxy
            have hi := hm i
            have hj := hm j
            omega
  have hderiv (z : ℂ) :
      finiteMonomialSum n b z =
        dominantHarmonicPolynomialDeriv a₁ m a z := by
    unfold finiteMonomialSum dominantHarmonicPolynomialDeriv
    rw [Fintype.sum_option]
    simp only [n, b, Option.elim_none, Option.elim_some, pow_zero,
      mul_one]
  have hparseval :=
    integral_ball_finiteMonomialSum_mul_conj n b hn
  rw [show (∫ z in Metric.ball (0 : ℂ) 1,
      (Complex.normSq
        (dominantHarmonicPolynomialDeriv a₁ m a z) : ℂ) ∂volume) =
      ∫ z in Metric.ball (0 : ℂ) 1,
        finiteMonomialSum n b z *
          starRingEnd ℂ (finiteMonomialSum n b z) ∂volume by
    apply setIntegral_congr_fun measurableSet_ball
    intro z _
    change (Complex.normSq
        (dominantHarmonicPolynomialDeriv a₁ m a z) : ℂ) =
      finiteMonomialSum n b z *
        starRingEnd ℂ (finiteMonomialSum n b z)
    rw [hderiv]
    rw [Complex.normSq_eq_conj_mul_self]
    ring]
  rw [hparseval]
  congr 1
  rw [Fintype.sum_option]
  simp only [n, b, Option.elim_none, Option.elim_some, Nat.cast_zero,
    zero_add, div_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hmi_two := hm i
  have hcast : ((m i - 1 : ℕ) : ℂ) + 1 = (m i : ℂ) := by
    norm_cast
    omega
  rw [hcast]
  rw [Complex.normSq_mul, Complex.normSq_natCast]
  push_cast
  have hmi : (m i : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : m i ≠ 0)
  field_simp [hmi]

/-- Real-valued form of the exact derivative-energy integral. -/
theorem integral_ball_dominantHarmonicPolynomialDeriv_normSq
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ i, 2 ≤ m i) (hminj : Function.Injective m) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      Complex.normSq
        (dominantHarmonicPolynomialDeriv a₁ m a z) ∂volume) =
      Real.pi *
        (Complex.normSq a₁ +
          ∑ i, (m i : ℝ) * Complex.normSq (a i)) := by
  apply Complex.ofReal_injective
  refine _root_.integral_ofReal.symm.trans ?_
  push_cast
  exact integral_ball_dominantHarmonicPolynomialDeriv_normSq_complex
    a₁ m a hm hminj

/-- The nonnegative Lebesgue integral of the squared derivative has the same
closed form. -/
theorem lintegral_ball_dominantHarmonicPolynomialDeriv_normSq
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ i, 2 ≤ m i) (hminj : Function.Injective m) :
    (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal
        (Complex.normSq
          (dominantHarmonicPolynomialDeriv a₁ m a z)) ∂volume) =
      ENNReal.ofReal
        (Real.pi *
          (Complex.normSq a₁ +
            ∑ i, (m i : ℝ) * Complex.normSq (a i))) := by
  have hint : IntegrableOn
      (fun z : ℂ ↦ Complex.normSq
        (dominantHarmonicPolynomialDeriv a₁ m a z))
      (Metric.ball (0 : ℂ) 1) := by
    apply IntegrableOn.mono_set
      (ContinuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) 1)
        ((Complex.continuous_normSq.comp (by
            unfold dominantHarmonicPolynomialDeriv
            fun_prop)).continuousOn))
    exact Metric.ball_subset_closedBall
  have hconvert := ofReal_integral_eq_lintegral_ofReal hint.integrable
    (Filter.Eventually.of_forall fun z ↦ Complex.normSq_nonneg _)
  rw [← hconvert]
  rw [integral_ball_dominantHarmonicPolynomialDeriv_normSq
    a₁ m a hm hminj]

/-- Exact area formula before evaluating the polynomial derivative integral.
The change-of-variables theorem applies because dominance gives injectivity
on the entire closed disk. -/
theorem volume_dominantHarmonicPolynomial_image_ball_eq_lintegral
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    volume (dominantHarmonicPolynomial a₁ m a '' Metric.ball 0 1) =
      ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal
          (Complex.normSq (dominantHarmonicPolynomialDeriv a₁ m a z))
          ∂volume := by
  have hinj : Set.InjOn (dominantHarmonicPolynomial a₁ m a)
      (Metric.ball (0 : ℂ) 1) :=
    (dominantHarmonicPolynomial_injOn_closedBall a₁ m a hdom).mono
      Metric.ball_subset_closedBall
  have hchange := lintegral_abs_det_fderiv_eq_addHaar_image
    (μ := volume) (f := dominantHarmonicPolynomial a₁ m a)
    (f' := fun z ↦
      dominantHarmonicPolynomialDeriv a₁ m a z •
        (1 : ℂ →L[ℝ] ℂ))
    measurableSet_ball
    (fun z _ ↦
      (hasDerivAt_dominantHarmonicPolynomial a₁ m a z).complexToReal_fderiv.hasFDerivWithinAt)
    hinj
  rw [show (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal
        (Complex.normSq (dominantHarmonicPolynomialDeriv a₁ m a z)) ∂volume) =
      ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal
          |(dominantHarmonicPolynomialDeriv a₁ m a z •
            (1 : ℂ →L[ℝ] ℂ)).det| ∂volume by
    apply setLIntegral_congr_fun measurableSet_ball
    intro z _
    change ENNReal.ofReal
      (Complex.normSq (dominantHarmonicPolynomialDeriv a₁ m a z)) =
      ENNReal.ofReal
        |(dominantHarmonicPolynomialDeriv a₁ m a z •
          (1 : ℂ →L[ℝ] ℂ)).det|
    rw [det_complex_smul_one]
    rw [abs_of_nonneg (Complex.normSq_nonneg _)]]
  exact hchange.symm

/-- Exact Lebesgue area of the injective dominant-harmonic polynomial disk. -/
theorem volume_dominantHarmonicPolynomial_image_ball
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ i, 2 ≤ m i) (hminj : Function.Injective m)
    (hdom : (∑ i, (m i : ℝ) * ‖a i‖) < ‖a₁‖) :
    volume (dominantHarmonicPolynomial a₁ m a '' Metric.ball 0 1) =
      ENNReal.ofReal
        (Real.pi *
          (Complex.normSq a₁ +
            ∑ i, (m i : ℝ) * Complex.normSq (a i))) := by
  rw [volume_dominantHarmonicPolynomial_image_ball_eq_lintegral
    a₁ m a hdom]
  exact lintegral_ball_dominantHarmonicPolynomialDeriv_normSq
    a₁ m a hm hminj

end

end GromovFilling
