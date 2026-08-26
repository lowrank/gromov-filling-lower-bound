import GromovFilling.Constants

/-!
# The orientation-free finite Fourier certificate

This file verifies the finite-dimensional algebra in Proposition 6.1 of the
note and the limiting argument giving `14 ζ(3) / π`.  The geometric input to
the proposition is isolated as the inequality saying that the sum of the
areas enclosed by the mixed boundary curves is at most the filling area.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The `k`th positive odd Fourier mode, with zero-based indexing. -/
def oddMode (k : ℕ) : ℕ := 2 * k + 1

/-- Radius of the boundary circle in Fourier mode `n`. -/
def boundaryRadius (n : ℕ) : ℝ := 4 / (Real.pi * (n : ℝ) ^ 2)

/-- The `N`-mode lower bound occurring before passage to the limit. -/
def finiteUniversalConstant (N : ℕ) : ℝ :=
  (16 / Real.pi) * ∑ k ∈ Finset.range N, oddCubicTerm k

/-- The finite certificates converge to the claimed universal constant. -/
theorem tendsto_finiteUniversalConstant :
    Filter.Tendsto finiteUniversalConstant Filter.atTop (nhds universalConstant) := by
  rw [universalConstant_eq_odd_tsum]
  exact tendsto_const_nhds.mul summable_oddCubicTerm.hasSum.tendsto_sum_nat

/-- Passing to the limit in the finite orientation-free certificates. -/
theorem universal_bound_of_finite_certificates {area : ℝ}
    (hfinite : ∀ N, finiteUniversalConstant N ≤ area) :
    universalConstant ≤ area :=
  le_of_tendsto' tendsto_finiteUniversalConstant hfinite

/-- Area enclosed by the boundary curve associated to one row of a mixing
matrix.  This is the expression obtained from Green's formula. -/
def mixedBoundaryArea {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) : ℝ :=
  Real.pi * ∑ k : Fin N,
    (oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2 * U j k ^ 2

private lemma boundary_area_weight (k : ℕ) :
    Real.pi * ((oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2) =
      (16 / Real.pi) * oddCubicTerm k := by
  have hk : (oddMode k : ℝ) ≠ 0 := by
    unfold oddMode
    push_cast
    positivity
  unfold oddMode boundaryRadius oddCubicTerm
  push_cast
  field_simp [Real.pi_ne_zero, hk]
  ring

/-- Orthogonality of the mixing matrix makes the total enclosed boundary
area independent of the mixing. -/
theorem sum_mixedBoundaryArea {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ)
    (hcol : ∀ k : Fin N, ∑ j : Fin N, U j k ^ 2 = 1) :
    (∑ j : Fin N, mixedBoundaryArea U j) = finiteUniversalConstant N := by
  calc
    (∑ j : Fin N, mixedBoundaryArea U j) =
        ∑ j : Fin N, ∑ k : Fin N,
          (Real.pi * ((oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2)) * U j k ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            unfold mixedBoundaryArea
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ k : Fin N, ∑ j : Fin N,
          (Real.pi * ((oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2)) * U j k ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin N,
          (Real.pi * ((oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2)) *
            (∑ j : Fin N, U j k ^ 2) := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.mul_sum]
    _ = ∑ k : Fin N,
          Real.pi * ((oddMode k : ℝ) * boundaryRadius (oddMode k) ^ 2) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hcol k, mul_one]
    _ = ∑ k : Fin N, (16 / Real.pi) * oddCubicTerm k := by
          apply Finset.sum_congr rfl
          intro k _
          exact boundary_area_weight k
    _ = finiteUniversalConstant N := by
          unfold finiteUniversalConstant
          rw [Finset.mul_sum]
          exact Fin.sum_univ_eq_sum_range (fun k ↦ (16 / Real.pi) * oddCubicTerm k) N

/-- Algebraic conclusion of the finite universal certificate.  The two
hypotheses are exactly the column norm identity for an orthogonal mixing and
the geometric budget/coverage inequality. -/
theorem finite_universal_certificate {N : ℕ} (U : Matrix (Fin N) (Fin N) ℝ)
    (area : ℝ)
    (hcol : ∀ k : Fin N, ∑ j : Fin N, U j k ^ 2 = 1)
    (hgeometry : (∑ j : Fin N, mixedBoundaryArea U j) ≤ area) :
    finiteUniversalConstant N ≤ area := by
  rw [← sum_mixedBoundaryArea U hcol]
  exact hgeometry

end

end GromovFilling
