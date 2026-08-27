import GromovFilling.JordanBoundary
import GromovFilling.PolynomialDiskArea

/-!
# Exact area of the mixed Givens disks

This file identifies the coefficient expression `mixedBoundaryArea` with
the actual Lebesgue area of the polynomial disk, and hence with the area of
the Jordan region containing the origin.  This is the planar area input used
in the careful formalization of Lemma 5.4.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace GromovFilling

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem givensBoundaryPolynomial_energy_eq_mixedBoundaryArea
    {N : ℕ} (j : Fin N) :
    Real.pi *
        (Complex.normSq
            (((boundaryRadius (oddMode 0) *
              givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)) +
          ∑ k : Fin (N - 1),
            (oddMode (k + 1) : ℝ) *
              Complex.normSq
                (((boundaryRadius (oddMode (k + 1)) *
                  givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))) =
      mixedBoundaryArea (givensMatrix N) j := by
  cases N with
  | zero => exact Fin.elim0 j
  | succ N =>
      have hindex (k : Fin N) :
          higherFinIndex (N := N + 1) k = k.succ := by
        apply Fin.ext
        simp only [higherFinIndex, Fin.val_succ]
      have hzero :
          (⟨0, Nat.zero_lt_of_lt j.isLt⟩ : Fin (N + 1)) = 0 := by
        apply Fin.ext
        rfl
      unfold mixedBoundaryArea
      rw [Fin.sum_univ_succ]
      simp_rw [hindex, hzero]
      simp only [Nat.succ_sub_one, Complex.normSq_ofReal,
        higherFinIndex, Fin.val_zero, Fin.val_succ]
      simp only [oddMode, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.add_comm]
      ring_nf

/-- The coefficient expression assigned to a Givens boundary is exactly the
Lebesgue area of its injective polynomial disk. -/
theorem volume_givensBoundaryPolynomial_image_ball
    {N : ℕ} (j : Fin N) :
    volume (givensBoundaryPolynomial j '' Metric.ball 0 1) =
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) := by
  unfold givensBoundaryPolynomial
  rw [volume_dominantHarmonicPolynomial_image_ball
    _ _ _ (by
      intro k
      unfold oddMode
      omega)]
  · rw [givensBoundaryPolynomial_energy_eq_mixedBoundaryArea j]
  · intro k l hkl
    apply Fin.ext
    change 2 * ((k : ℕ) + 1) + 1 =
      2 * ((l : ℕ) + 1) + 1 at hkl
    omega
  · exact givensBoundaryCurve_dominance j

/-- In any Jordan partition of a mixed Givens curve, the region containing
the origin has exactly the area specified by `mixedBoundaryArea`. -/
theorem volume_givensBoundaryCurve_jordan_region
    {N : ℕ} (j : Fin N) {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    volume region₁ =
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) := by
  rw [givensBoundaryCurve_jordan_region_eq_polynomial_image_ball
    j hpartition hzero]
  exact volume_givensBoundaryPolynomial_image_ball j

end

end GromovFilling
