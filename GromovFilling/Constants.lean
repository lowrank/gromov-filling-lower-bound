import Mathlib

/-!
# Constants in the Fourier filling-area certificates

The note writes `ζ(3)` for the real p-series.  Defining it directly as a
real `tsum` keeps the geometric formalization independent of the complex
analytic continuation of the Riemann zeta function.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The real number `ζ(3) = ∑ n ≥ 1, n⁻³`.  The term at `n = 0` is zero. -/
noncomputable def zetaThree : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ 3

/-- The summand in the odd positive cubic p-series. -/
def oddCubicTerm (k : ℕ) : ℝ :=
  1 / ((2 * k + 1 : ℕ) : ℝ) ^ 3

lemma summable_zetaThree : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 3) := by
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

lemma summable_oddCubicTerm : Summable oddCubicTerm := by
  apply summable_zetaThree.comp_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (Nat.add_right_cancel hab)

lemma even_cubic_term (k : ℕ) :
    1 / ((2 * k : ℕ) : ℝ) ^ 3 = (1 / 8 : ℝ) * (1 / (k : ℝ) ^ 3) := by
  push_cast
  ring

/-- Splitting the cubic p-series into its even and odd terms gives `7/8 ζ(3)`. -/
theorem tsum_oddCubicTerm :
    (∑' k : ℕ, oddCubicTerm k) = (7 / 8 : ℝ) * zetaThree := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 3
  have hf : Summable f := summable_zetaThree
  have he : Summable (fun k : ℕ ↦ f (2 * k)) := by
    apply hf.comp_injective
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hab
  have ho : Summable (fun k : ℕ ↦ f (2 * k + 1)) := by
    simpa only [f, oddCubicTerm] using summable_oddCubicTerm
  have hsplit := tsum_even_add_odd he ho
  have heval : (∑' k : ℕ, f (2 * k)) = (1 / 8 : ℝ) * zetaThree := by
    calc
      (∑' k : ℕ, f (2 * k)) = ∑' k : ℕ, (1 / 8 : ℝ) * f k := by
        apply tsum_congr
        intro k
        exact even_cubic_term k
      _ = (1 / 8 : ℝ) * ∑' k : ℕ, f k := tsum_mul_left
      _ = (1 / 8 : ℝ) * zetaThree := rfl
  rw [heval] at hsplit
  change (∑' k : ℕ, oddCubicTerm k) = _
  change (1 / 8 : ℝ) * zetaThree + (∑' k : ℕ, oddCubicTerm k) = zetaThree at hsplit
  linarith

/-- The constant in the orientation-free Fourier theorem. -/
noncomputable def universalConstant : ℝ :=
  14 * zetaThree / Real.pi

lemma universalConstant_eq_odd_tsum :
    universalConstant = (16 / Real.pi) * ∑' k : ℕ, oddCubicTerm k := by
  rw [tsum_oddCubicTerm]
  unfold universalConstant
  ring

end

end GromovFilling
