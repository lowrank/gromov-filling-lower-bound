import GromovFilling.BoundaryActionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The scalar trace series for one-high-leg resonances

This file verifies the nonnegative double-series computation underlying
Lemma 14.3 of the note.  It proves summability, the Tonelli/antidiagonal
reindexing, and the exact scalar value.

It does not construct the infinite matrix as an operator on `ℓ²`, prove that
operator positive or trace class, or identify this scalar series with an
operator trace.  Those operator-theoretic steps remain separate obligations.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The `(j, k)` summand in the manuscript's diagonal trace series, with the
positive odd mode written as `2k+1` and the denominator as `2(j+k)+1`. -/
def resonanceTraceTerm (j k : ℕ) : ℝ :=
  (16 / Real.pi) * (oddMode k : ℝ) / (oddMode (j + k) : ℝ) ^ 4

/-- The trace summand is exactly the manuscript expression
`(16/π) (2k+1) / (2k+1+2j)⁴`. -/
theorem resonanceTraceTerm_eq_manuscript (j k : ℕ) :
    resonanceTraceTerm j k =
      (16 / Real.pi) * (oddMode k : ℝ) /
        (((oddMode k + 2 * j : ℕ) : ℝ) ^ 4) := by
  have hden : oddMode (j + k) = oddMode k + 2 * j := by
    unfold oddMode
    omega
  unfold resonanceTraceTerm
  rw [hden]

lemma resonanceTraceTerm_nonneg (j k : ℕ) :
    0 ≤ resonanceTraceTerm j k := by
  unfold resonanceTraceTerm oddMode
  positivity

/-- The same summand as a function on the product index type. -/
def resonanceTracePairTerm (p : ℕ × ℕ) : ℝ :=
  resonanceTraceTerm p.1 p.2

lemma resonanceTracePairTerm_nonneg (p : ℕ × ℕ) :
    0 ≤ resonanceTracePairTerm p :=
  resonanceTraceTerm_nonneg p.1 p.2

/-- The finite contribution from all pairs with `j+k=r`. -/
def resonanceTraceGroupedTerm (r : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal r, resonanceTracePairTerm p

private lemma sum_range_oddMode (N : ℕ) :
    (∑ k ∈ Finset.range N, (oddMode k : ℝ)) = (N : ℝ) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold oddMode
      push_cast
      ring

private lemma sum_antidiagonal_oddMode_snd (r : ℕ) :
    (∑ p ∈ Finset.antidiagonal r, (oddMode p.2 : ℝ)) =
      (((r + 1 : ℕ) : ℝ) ^ 2) := by
  calc
    (∑ p ∈ Finset.antidiagonal r, (oddMode p.2 : ℝ)) =
        ∑ p ∈ Finset.antidiagonal r, (oddMode p.1 : ℝ) := by
          simpa using
            (Finset.Nat.sum_antidiagonal_swap
              (n := r) (f := fun p : ℕ × ℕ ↦ (oddMode p.1 : ℝ)))
    _ = ∑ k ∈ Finset.range r.succ, (oddMode k : ℝ) := by
      simpa using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun k _ : ℕ ↦ (oddMode k : ℝ)) r)
    _ = (((r + 1 : ℕ) : ℝ) ^ 2) := by
      simpa [Nat.succ_eq_add_one] using sum_range_oddMode r.succ

/-- Grouping by `r=j+k` turns the double series into the three odd p-series
appearing in the manuscript trace computation. -/
theorem resonanceTraceGroupedTerm_eq (r : ℕ) :
    resonanceTraceGroupedTerm r =
      (4 / Real.pi) *
        (oddSquareTerm r + (2 * oddCubicTerm r + oddFourthTerm r)) := by
  unfold resonanceTraceGroupedTerm
  calc
    (∑ p ∈ Finset.antidiagonal r, resonanceTracePairTerm p) =
        ∑ p ∈ Finset.antidiagonal r,
          ((16 / Real.pi) / (oddMode r : ℝ) ^ 4) * (oddMode p.2 : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hsum : p.1 + p.2 = r := Finset.mem_antidiagonal.mp hp
            unfold resonanceTracePairTerm resonanceTraceTerm
            rw [hsum]
            ring
    _ = ((16 / Real.pi) / (oddMode r : ℝ) ^ 4) *
        ∑ p ∈ Finset.antidiagonal r, (oddMode p.2 : ℝ) := by
          rw [Finset.mul_sum]
    _ = ((16 / Real.pi) / (oddMode r : ℝ) ^ 4) *
        (((r + 1 : ℕ) : ℝ) ^ 2) := by
          rw [sum_antidiagonal_oddMode_snd]
    _ = (4 / Real.pi) *
        (oddSquareTerm r + (2 * oddCubicTerm r + oddFourthTerm r)) := by
          unfold oddSquareTerm oddCubicTerm oddFourthTerm oddMode
          push_cast
          have hm : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
          field_simp [Real.pi_ne_zero, hm]
          ring

lemma summable_resonanceTraceGroupedTerm :
    Summable resonanceTraceGroupedTerm := by
  have hparts : Summable (fun r : ℕ ↦
      oddSquareTerm r + (2 * oddCubicTerm r + oddFourthTerm r)) :=
    summable_oddSquareTerm.add
      ((summable_oddCubicTerm.mul_left 2).add summable_oddFourthTerm)
  have hscaled := hparts.mul_left (4 / Real.pi)
  exact hscaled.congr (fun r ↦ (resonanceTraceGroupedTerm_eq r).symm)

/-- Exact value of the antidiagonally grouped trace series. -/
theorem tsum_resonanceTraceGroupedTerm :
    (∑' r : ℕ, resonanceTraceGroupedTerm r) =
      Real.pi / 2 + 7 * zetaThree / Real.pi + Real.pi ^ 3 / 24 := by
  calc
    (∑' r : ℕ, resonanceTraceGroupedTerm r) =
        ∑' r : ℕ, (4 / Real.pi) *
          (oddSquareTerm r + (2 * oddCubicTerm r + oddFourthTerm r)) :=
      tsum_congr resonanceTraceGroupedTerm_eq
    _ = (4 / Real.pi) * ∑' r : ℕ,
        (oddSquareTerm r + (2 * oddCubicTerm r + oddFourthTerm r)) :=
      tsum_mul_left
    _ = Real.pi / 2 + 7 * zetaThree / Real.pi + Real.pi ^ 3 / 24 := by
      rw [summable_oddSquareTerm.tsum_add
          ((summable_oddCubicTerm.mul_left 2).add summable_oddFourthTerm),
        (summable_oddCubicTerm.mul_left 2).tsum_add summable_oddFourthTerm,
        tsum_mul_left, tsum_oddSquareTerm, tsum_oddCubicTerm,
        tsum_oddFourthTerm]
      field_simp [Real.pi_ne_zero]
      ring

private theorem summable_pair_of_summable_antidiagonal
    {f : ℕ × ℕ → ℝ} (hf_nonneg : ∀ p, 0 ≤ f p)
    (hgrouped : Summable (fun r : ℕ ↦
      ∑ p ∈ Finset.antidiagonal r, f p)) :
    Summable f := by
  let e : (Σ r : ℕ, Finset.antidiagonal r) ≃ ℕ × ℕ :=
    Finset.sigmaAntidiagonalEquivProd
  refine e.summable_iff.mp ?_
  refine (summable_sigma_of_nonneg ?_).2 ⟨?_, ?_⟩
  · intro q
    exact hf_nonneg (e q)
  · intro r
    exact (hasSum_fintype _).summable
  · refine hgrouped.congr (fun r ↦ ?_)
    change (∑ p ∈ Finset.antidiagonal r, f p) =
      ∑' p : Finset.antidiagonal r, f p
    rw [← Finset.sum_finset_coe,
      ← tsum_fintype (L := .unconditional _)]
    rfl

/-- Absolute summability of the manuscript's nonnegative trace summand on
`ℕ × ℕ`. -/
theorem summable_resonanceTracePairTerm :
    Summable resonanceTracePairTerm := by
  apply summable_pair_of_summable_antidiagonal
  · exact resonanceTracePairTerm_nonneg
  · simpa [resonanceTraceGroupedTerm] using
      summable_resonanceTraceGroupedTerm

private theorem tsum_prod_eq_tsum_antidiagonal
    (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    (∑' p : ℕ × ℕ, f p) =
      ∑' r : ℕ, ∑ p ∈ Finset.antidiagonal r, f p := by
  conv_rhs =>
    congr
    ext r
    rw [← Finset.sum_finset_coe,
      ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.sigmaAntidiagonalEquivProd.tsum_eq f]
  exact
    (Finset.sigmaAntidiagonalEquivProd.summable_iff.mpr hf).tsum_sigma'
      (fun _ ↦ (hasSum_fintype _).summable)

/-- Tonelli's regrouping of the nonnegative trace series by `r=j+k`. -/
theorem tsum_resonanceTracePairTerm_eq_grouped :
    (∑' p : ℕ × ℕ, resonanceTracePairTerm p) =
      ∑' r : ℕ, resonanceTraceGroupedTerm r := by
  simpa [resonanceTraceGroupedTerm] using
    tsum_prod_eq_tsum_antidiagonal resonanceTracePairTerm
      summable_resonanceTracePairTerm

/-- The diagonal entry series for the scalar matrix formula. -/
def resonanceTraceDiagonal (j : ℕ) : ℝ :=
  ∑' k : ℕ, resonanceTraceTerm j k

/-- The iterated nonnegative scalar series written as a trace in the
manuscript. -/
def resonanceTraceSeries : ℝ :=
  ∑' j : ℕ, resonanceTraceDiagonal j

lemma summable_resonanceTraceDiagonal (j : ℕ) :
    Summable (fun k : ℕ ↦ resonanceTraceTerm j k) := by
  simpa [resonanceTracePairTerm] using
    summable_resonanceTracePairTerm.prod_factor j

lemma summable_resonanceTraceDiagonalSeries :
    Summable resonanceTraceDiagonal := by
  simpa [resonanceTraceDiagonal, resonanceTracePairTerm] using
    summable_resonanceTracePairTerm.prod

/-- The product-indexed and manuscript-ordered iterated sums agree. -/
theorem tsum_resonanceTracePairTerm_eq_series :
    (∑' p : ℕ × ℕ, resonanceTracePairTerm p) =
      resonanceTraceSeries := by
  unfold resonanceTraceSeries resonanceTraceDiagonal
  simpa [resonanceTracePairTerm] using
    summable_resonanceTracePairTerm.tsum_prod

/-- Exact scalar double-series identity underlying Lemma 14.3.  The separate
operator construction and trace-class identification are deliberately not
part of this theorem. -/
theorem resonanceTraceSeries_eq :
    resonanceTraceSeries =
      Real.pi / 2 + 7 * zetaThree / Real.pi + Real.pi ^ 3 / 24 := by
  calc
    resonanceTraceSeries =
        ∑' p : ℕ × ℕ, resonanceTracePairTerm p :=
      tsum_resonanceTracePairTerm_eq_series.symm
    _ = ∑' r : ℕ, resonanceTraceGroupedTerm r :=
      tsum_resonanceTracePairTerm_eq_grouped
    _ = Real.pi / 2 + 7 * zetaThree / Real.pi + Real.pi ^ 3 / 24 :=
      tsum_resonanceTraceGroupedTerm

end

end GromovFilling
