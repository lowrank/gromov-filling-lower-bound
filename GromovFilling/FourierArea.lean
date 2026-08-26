import GromovFilling.BoundaryCertificate

/-!
# Green area of a finite Fourier curve

We evaluate the Green integral of a finite positive-frequency Fourier
curve.  This supplies the analytic area identity in Lemma 5.3 of the note;
the proof includes differentiation and all cross-term orthogonality.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace GromovFilling

noncomputable section

/-- The two real coordinates of a finite positive-frequency Fourier curve. -/
def fourierCurveX {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, a k * Real.cos ((m k : ℝ) * t)

def fourierCurveY {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, a k * Real.sin ((m k : ℝ) * t)

/-- The explicit derivatives of the two coordinate sums. -/
def fourierCurveDX {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, -((m k : ℝ) * a k * Real.sin ((m k : ℝ) * t))

def fourierCurveDY {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ k, (m k : ℝ) * a k * Real.cos ((m k : ℝ) * t)

theorem hasDerivAt_fourierCurveX {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fourierCurveX m a) (fourierCurveDX m a t) t := by
  unfold fourierCurveX fourierCurveDX
  apply HasDerivAt.sum
  intro k _
  convert ((Real.hasDerivAt_cos ((m k : ℝ) * t)).comp t
    ((hasDerivAt_id t).const_mul (m k : ℝ))).const_mul (a k) using 1
  all_goals ring

theorem hasDerivAt_fourierCurveY {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fourierCurveY m a) (fourierCurveDY m a t) t := by
  unfold fourierCurveY fourierCurveDY
  apply HasDerivAt.sum
  intro k _
  convert ((Real.hasDerivAt_sin ((m k : ℝ) * t)).comp t
    ((hasDerivAt_id t).const_mul (m k : ℝ))).const_mul (a k) using 1
  all_goals ring

/-- Green's signed-area functional for the finite Fourier curve. -/
def fourierGreenArea {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..2 * Real.pi,
    (fourierCurveX m a t * fourierCurveDY m a t -
      fourierCurveY m a t * fourierCurveDX m a t)

/-- Cosines at unequal natural frequencies are orthogonal on a full
period.  We state the result in the difference form used after applying
`cos_sub`. -/
lemma integral_cos_natCast_sub_mul (p q : ℕ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Real.cos (((p : ℝ) - (q : ℝ)) * t)) =
        if p = q then 2 * Real.pi else 0 := by
  by_cases hpq : p = q
  · subst q
    simp
  · have hc : (p : ℝ) - (q : ℝ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hpq)
    rw [intervalIntegral.integral_comp_mul_left Real.cos hc]
    simp only [zero_mul, integral_cos, Real.sin_zero, sub_zero]
    have hsin :
        Real.sin (((p : ℝ) - (q : ℝ)) * (2 * Real.pi)) = 0 := by
      have hcast : (p : ℝ) - (q : ℝ) = ((p : ℤ) - (q : ℤ) : ℤ) := by
        push_cast
        rfl
      rw [hcast]
      convert Real.sin_int_mul_pi (2 * ((p : ℤ) - (q : ℤ))) using 1
      all_goals
        push_cast
        ring
    rw [hsin]
    simp [hpq]

private lemma fourier_green_integrand {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (t : ℝ) :
    fourierCurveX m a t * fourierCurveDY m a t -
        fourierCurveY m a t * fourierCurveDX m a t =
      ∑ l, ∑ k,
        a k * a l * (m l : ℝ) *
          Real.cos (((m k : ℝ) - (m l : ℝ)) * t) := by
  simp only [fourierCurveX, fourierCurveY, fourierCurveDX, fourierCurveDY,
    Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ((m k : ℝ) - (m l : ℝ)) * t =
      (m k : ℝ) * t - (m l : ℝ) * t by ring]
  rw [Real.cos_sub]
  ring

/-- Exact Green-area formula for distinct positive frequencies. -/
theorem fourierGreenArea_eq {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (a : ι → ℝ) (hm : Function.Injective m) :
    fourierGreenArea m a =
      Real.pi * ∑ k, (m k : ℝ) * a k ^ 2 := by
  unfold fourierGreenArea
  simp_rw [fourier_green_integrand]
  rw [intervalIntegral.integral_finset_sum (fun l _ ↦ by
    apply Continuous.intervalIntegrable
    fun_prop)]
  have hinner (l : ι) :
      (∫ t in (0 : ℝ)..2 * Real.pi,
          ∑ k, a k * a l * (m l : ℝ) *
            Real.cos (((m k : ℝ) - (m l : ℝ)) * t)) =
        ∑ k, ∫ t in (0 : ℝ)..2 * Real.pi,
          a k * a l * (m l : ℝ) *
            Real.cos (((m k : ℝ) - (m l : ℝ)) * t) := by
    exact intervalIntegral.integral_finset_sum (fun k _ ↦ by
      apply Continuous.intervalIntegrable
      fun_prop)
  rw [show (∑ l, ∫ t in (0 : ℝ)..2 * Real.pi,
      ∑ k, a k * a l * (m l : ℝ) *
        Real.cos (((m k : ℝ) - (m l : ℝ)) * t)) =
      ∑ l, ∑ k, ∫ t in (0 : ℝ)..2 * Real.pi,
        a k * a l * (m l : ℝ) *
          Real.cos (((m k : ℝ) - (m l : ℝ)) * t) by
    exact Finset.sum_congr rfl (fun l _ ↦ hinner l)]
  simp_rw [intervalIntegral.integral_const_mul,
    integral_cos_natCast_sub_mul]
  have hdiag :
      (∑ l, ∑ k,
        a k * a l * (m l : ℝ) *
          if m k = m l then 2 * Real.pi else 0) =
        ∑ l, a l * a l * (m l : ℝ) * (2 * Real.pi) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hkl
      have hne : m k ≠ m l := fun h ↦ hkl (hm h)
      simp [hne]
    · simp
  rw [hdiag]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma oddMode_injective : Function.Injective oddMode := by
  intro k l h
  unfold oddMode at h
  omega

/-- The Green integral of a mixed boundary row is exactly the algebraic
quantity used by the finite universal certificate. -/
theorem givensBoundaryGreenArea_eq_mixedBoundaryArea {N : ℕ} (j : Fin N) :
    fourierGreenArea
        (fun k : Fin N ↦ oddMode k)
        (fun k : Fin N ↦ boundaryRadius (oddMode k) * givensMatrix N j k) =
      mixedBoundaryArea (givensMatrix N) j := by
  have harea := fourierGreenArea_eq
    (fun k : Fin N ↦ oddMode (k : ℕ))
    (fun k : Fin N ↦ boundaryRadius (oddMode k) * givensMatrix N j k)
    (oddMode_injective.comp Fin.val_injective)
  rw [harea]
  unfold mixedBoundaryArea
  apply congrArg (fun x : ℝ ↦ Real.pi * x)
  apply Finset.sum_congr rfl
  intro k _
  ring

end

end GromovFilling
