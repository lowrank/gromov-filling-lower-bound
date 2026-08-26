import GromovFilling.Oriented
import GromovFilling.Universal
import Mathlib.NumberTheory.ZetaValues

/-!
# Series in the nonlinear boundary action

This file verifies the exact odd-mode series evaluations used to obtain the
linear and quadratic coefficients of Proposition 9.1 in the note.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

def oddSquareTerm (k : ℕ) : ℝ := 1 / (oddMode k : ℝ) ^ 2

def oddFourthTerm (k : ℕ) : ℝ := 1 / (oddMode k : ℝ) ^ 4

lemma summable_oddSquareTerm : Summable oddSquareTerm := by
  apply hasSum_zeta_two.summable.comp_injective
  intro a b hab
  unfold oddMode at hab
  omega

lemma summable_oddFourthTerm : Summable oddFourthTerm := by
  apply hasSum_zeta_four.summable.comp_injective
  intro a b hab
  unfold oddMode at hab
  omega

private lemma even_square_term (k : ℕ) :
    1 / ((2 * k : ℕ) : ℝ) ^ 2 =
      (1 / 4 : ℝ) * (1 / (k : ℝ) ^ 2) := by
  push_cast
  ring

private lemma even_fourth_term (k : ℕ) :
    1 / ((2 * k : ℕ) : ℝ) ^ 4 =
      (1 / 16 : ℝ) * (1 / (k : ℝ) ^ 4) := by
  push_cast
  ring

theorem tsum_oddSquareTerm :
    (∑' k : ℕ, oddSquareTerm k) = Real.pi ^ 2 / 8 := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 2
  have hf : Summable f := hasSum_zeta_two.summable
  have he : Summable (fun k : ℕ ↦ f (2 * k)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun k : ℕ ↦ f (2 * k + 1)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  have hsplit := tsum_even_add_odd he ho
  have heval : (∑' k : ℕ, f (2 * k)) = Real.pi ^ 2 / 24 := by
    calc
      (∑' k : ℕ, f (2 * k)) = ∑' k : ℕ, (1 / 4 : ℝ) * f k := by
        apply tsum_congr
        exact fun k ↦ even_square_term k
      _ = (1 / 4 : ℝ) * ∑' k : ℕ, f k := tsum_mul_left
      _ = Real.pi ^ 2 / 24 := by rw [hasSum_zeta_two.tsum_eq]; ring
  rw [heval, hasSum_zeta_two.tsum_eq] at hsplit
  change (∑' k : ℕ, oddSquareTerm k) = _
  change Real.pi ^ 2 / 24 + (∑' k : ℕ, oddSquareTerm k) =
    Real.pi ^ 2 / 6 at hsplit
  linarith

theorem tsum_oddFourthTerm :
    (∑' k : ℕ, oddFourthTerm k) = Real.pi ^ 4 / 96 := by
  let f : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ 4
  have hf : Summable f := hasSum_zeta_four.summable
  have he : Summable (fun k : ℕ ↦ f (2 * k)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun k : ℕ ↦ f (2 * k + 1)) :=
    hf.comp_injective (fun _ _ h ↦ by omega)
  have hsplit := tsum_even_add_odd he ho
  have heval : (∑' k : ℕ, f (2 * k)) = Real.pi ^ 4 / 1440 := by
    calc
      (∑' k : ℕ, f (2 * k)) = ∑' k : ℕ, (1 / 16 : ℝ) * f k := by
        apply tsum_congr
        exact fun k ↦ even_fourth_term k
      _ = (1 / 16 : ℝ) * ∑' k : ℕ, f k := tsum_mul_left
      _ = Real.pi ^ 4 / 1440 := by rw [hasSum_zeta_four.tsum_eq]; ring
  rw [heval, hasSum_zeta_four.tsum_eq] at hsplit
  change (∑' k : ℕ, oddFourthTerm k) = _
  change Real.pi ^ 4 / 1440 + (∑' k : ℕ, oddFourthTerm k) =
    Real.pi ^ 4 / 90 at hsplit
  linarith

lemma tendsto_one_div_oddMode :
    Filter.Tendsto (fun k : ℕ ↦ 1 / (oddMode k : ℝ))
      Filter.atTop (nhds 0) := by
  have htail : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
  refine squeeze_zero (g := fun k : ℕ ↦ 1 / ((k + 1 : ℕ) : ℝ)) ?_ ?_ htail
  · intro k
    positivity
  · intro k
    change 1 / (oddMode k : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ)
    have horder : (((k + 1 : ℕ) : ℝ)) ≤ (oddMode k : ℝ) := by
      exact_mod_cast (show k + 1 ≤ oddMode k by unfold oddMode; omega)
    exact one_div_le_one_div_of_le
      (a := (((k + 1 : ℕ) : ℝ))) (b := (oddMode k : ℝ)) (by positivity) horder

private lemma linear_partial_fraction (k : ℕ) :
    1 / ((oddMode k : ℝ) * ((oddMode k + 2 : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) *
          (1 / (oddMode k : ℝ) - 1 / (oddMode (k + 1) : ℝ)) -
        (1 / 2 : ℝ) * oddSquareTerm (k + 1) := by
  unfold oddSquareTerm oddMode
  push_cast
  field_simp
  ring

private lemma telescoping_odd_reciprocal (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 / (oddMode k : ℝ) - 1 / (oddMode (k + 1) : ℝ))) =
        1 - 1 / (oddMode N : ℝ) := by
  induction N with
  | zero => simp [oddMode]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Linear boundary-resonance series. -/
theorem hasSum_boundaryLinearCore :
    HasSum (fun k : ℕ ↦
      1 / ((oddMode k : ℝ) * ((oddMode k + 2 : ℕ) : ℝ) ^ 2))
      (3 / 4 - Real.pi ^ 2 / 16) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ by positivity)]
  have hsquareShift :
      HasSum (fun k : ℕ ↦ oddSquareTerm (k + 1))
        (Real.pi ^ 2 / 8 - 1) := by
    have hsplit := summable_oddSquareTerm.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hsplit
    change oddSquareTerm 0 + (∑' i : ℕ, oddSquareTerm (i + 1)) =
      ∑' i : ℕ, oddSquareTerm i at hsplit
    rw [tsum_oddSquareTerm] at hsplit
    have hzero : oddSquareTerm 0 = 1 := by norm_num [oddSquareTerm, oddMode]
    rw [hzero] at hsplit
    have hvalue : (∑' i : ℕ, oddSquareTerm (i + 1)) =
        Real.pi ^ 2 / 8 - 1 := by linarith
    have hsummable : Summable (fun i : ℕ ↦ oddSquareTerm (i + 1)) :=
      (summable_nat_add_iff 1).2 summable_oddSquareTerm
    simpa [hvalue] using hsummable.hasSum
  have hshiftTendsto := hsquareShift.tendsto_sum_nat
  have hformula (N : ℕ) :
      (∑ k ∈ Finset.range N,
        1 / ((oddMode k : ℝ) * ((oddMode k + 2 : ℕ) : ℝ) ^ 2)) =
        (1 / 4 : ℝ) * (1 - 1 / (oddMode N : ℝ)) -
          (1 / 2 : ℝ) * ∑ k ∈ Finset.range N, oddSquareTerm (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range N,
          ((1 / 4 : ℝ) *
              (1 / (oddMode k : ℝ) - 1 / (oddMode (k + 1) : ℝ)) -
            (1 / 2 : ℝ) * oddSquareTerm (k + 1)) := by
              apply Finset.sum_congr rfl
              intro k _
              exact linear_partial_fraction k
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          telescoping_odd_reciprocal]
  simp_rw [hformula]
  convert (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub tendsto_one_div_oddMode)).sub
        (tendsto_const_nhds.mul hshiftTendsto) using 1
  all_goals ring

/-- Quadratic boundary-resonance series. -/
private lemma boundaryQuadraticCore_eq (k : ℕ) :
    (oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4 =
      oddCubicTerm (k + 1) - 2 * oddFourthTerm (k + 1) := by
  have hshift : (oddMode k + 2 : ℕ) = oddMode (k + 1) := by
    unfold oddMode
    omega
  rw [hshift]
  unfold oddCubicTerm oddFourthTerm oddMode
  push_cast
  have hk : (0 : ℝ) < 2 * k + 3 := by positivity
  field_simp [ne_of_gt hk]
  ring

lemma summable_boundaryQuadraticCore : Summable (fun k : ℕ ↦
    (oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4) := by
  have hcubic : Summable (fun k : ℕ ↦ oddCubicTerm (k + 1)) :=
    (summable_nat_add_iff 1).2 summable_oddCubicTerm
  have hfourth : Summable (fun k : ℕ ↦ 2 * oddFourthTerm (k + 1)) :=
    ((summable_nat_add_iff 1).2 summable_oddFourthTerm).mul_left 2
  exact (hcubic.sub hfourth).congr (fun k ↦ (boundaryQuadraticCore_eq k).symm)

theorem tsum_boundaryQuadraticCore :
    (∑' k : ℕ, (oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4) =
      (7 / 8 : ℝ) * zetaThree + 1 - Real.pi ^ 4 / 48 := by
  have hcubicShift := summable_oddCubicTerm.sum_add_tsum_nat_add 1
  have hfourthShift := summable_oddFourthTerm.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hcubicShift hfourthShift
  change oddCubicTerm 0 + (∑' i : ℕ, oddCubicTerm (i + 1)) =
    ∑' i : ℕ, oddCubicTerm i at hcubicShift
  change oddFourthTerm 0 + (∑' i : ℕ, oddFourthTerm (i + 1)) =
    ∑' i : ℕ, oddFourthTerm i at hfourthShift
  rw [tsum_oddCubicTerm] at hcubicShift
  rw [tsum_oddFourthTerm] at hfourthShift
  have hcubicZero : oddCubicTerm 0 = 1 := by norm_num [oddCubicTerm]
  have hfourthZero : oddFourthTerm 0 = 1 := by
    norm_num [oddFourthTerm, oddMode]
  rw [hcubicZero] at hcubicShift
  rw [hfourthZero] at hfourthShift
  calc
    (∑' k : ℕ, (oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4) =
        ∑' k : ℕ, (oddCubicTerm (k + 1) -
          2 * oddFourthTerm (k + 1)) := tsum_congr boundaryQuadraticCore_eq
    _ = (∑' k : ℕ, oddCubicTerm (k + 1)) -
        2 * ∑' k : ℕ, oddFourthTerm (k + 1) := by
          rw [((summable_nat_add_iff 1).2 summable_oddCubicTerm).tsum_sub
            (((summable_nat_add_iff 1).2 summable_oddFourthTerm).mul_left 2),
            tsum_mul_left]
    _ = (7 / 8 : ℝ) * zetaThree + 1 - Real.pi ^ 4 / 48 := by
      linarith

/-- The boundary action before evaluating its three odd-mode series. -/
def boundaryActionSeries (lam : ℝ) : ℝ :=
  ∑' k : ℕ, Real.pi * (oddMode k : ℝ) *
    (boundaryRadius (oddMode k) +
      lam * boundaryRadius (oddMode 0) ^ 2 *
        boundaryRadius (oddMode k + 2)) ^ 2

private lemma boundaryActionTerm_eq (lam : ℝ) (k : ℕ) :
    Real.pi * (oddMode k : ℝ) *
        (boundaryRadius (oddMode k) +
          lam * boundaryRadius (oddMode 0) ^ 2 *
            boundaryRadius (oddMode k + 2)) ^ 2 =
      (16 / Real.pi) * oddCubicTerm k +
        ((512 / Real.pi ^ 3) * lam) *
          (1 / ((oddMode k : ℝ) * ((oddMode k + 2 : ℕ) : ℝ) ^ 2)) +
        ((4096 / Real.pi ^ 5) * lam ^ 2) *
          ((oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4) := by
  have hk : (oddMode k : ℝ) ≠ 0 := by unfold oddMode; push_cast; positivity
  have hk2 : ((oddMode k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold boundaryRadius oddCubicTerm oddMode
  push_cast
  field_simp [Real.pi_ne_zero, hk, hk2]
  ring

/-- Proposition 9.1: the infinite boundary series is exactly the closed
quadratic polynomial used by the oriented certificate. -/
theorem boundaryActionSeries_eq (lam : ℝ) :
    boundaryActionSeries lam = boundaryAction lam := by
  have hcubic := summable_oddCubicTerm.hasSum
  rw [tsum_oddCubicTerm] at hcubic
  have hconst : HasSum (fun k : ℕ ↦ (16 / Real.pi) * oddCubicTerm k)
      universalConstant := by
    convert hcubic.mul_left (16 / Real.pi) using 1
    unfold universalConstant
    ring
  have hlinear : HasSum (fun k : ℕ ↦
      ((512 / Real.pi ^ 3) * lam) *
        (1 / ((oddMode k : ℝ) * ((oddMode k + 2 : ℕ) : ℝ) ^ 2)))
      (boundaryLinear * lam) := by
    convert hasSum_boundaryLinearCore.mul_left
      ((512 / Real.pi ^ 3) * lam) using 1
    unfold boundaryLinear
    ring
  have hquadratic : HasSum (fun k : ℕ ↦
      ((4096 / Real.pi ^ 5) * lam ^ 2) *
        ((oddMode k : ℝ) / ((oddMode k + 2 : ℕ) : ℝ) ^ 4))
      (boundaryQuadratic * lam ^ 2) := by
    have hcore := summable_boundaryQuadraticCore.hasSum
    rw [tsum_boundaryQuadraticCore] at hcore
    convert hcore.mul_left ((4096 / Real.pi ^ 5) * lam ^ 2) using 1
    unfold boundaryQuadratic
    ring
  have hall := hconst.add (hlinear.add hquadratic)
  have hseries : HasSum (fun k : ℕ ↦ Real.pi * (oddMode k : ℝ) *
      (boundaryRadius (oddMode k) +
        lam * boundaryRadius (oddMode 0) ^ 2 *
          boundaryRadius (oddMode k + 2)) ^ 2)
      (universalConstant + boundaryLinear * lam +
        boundaryQuadratic * lam ^ 2) := by
    simpa only [boundaryActionTerm_eq, add_assoc] using hall
  unfold boundaryActionSeries boundaryAction
  exact hseries.tsum_eq

end

end GromovFilling
