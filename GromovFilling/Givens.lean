import GromovFilling.JacobianBudget

/-!
# Quantitative Givens coefficients

The finite orientation-free argument uses rotations coupling the first odd
mode to every higher odd mode.  This file records their exact normalization
and the elementary telescoping estimates for the odd reciprocal-square
tails used in Lemma 5.2.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Reciprocal of the `k`th positive odd mode. -/
def oddWeight (k : ℕ) : ℝ := 1 / oddMode k

/-- Cosine coefficient of the Givens rotation for a higher mode. -/
def givensC (k : ℕ) : ℝ := 1 / Real.sqrt (1 + 4 * oddWeight k ^ 2)

/-- Sine coefficient of the Givens rotation for a higher mode. -/
def givensS (k : ℕ) : ℝ := 2 * oddWeight k * givensC k

lemma oddWeight_pos (k : ℕ) : 0 < oddWeight k := by
  unfold oddWeight oddMode
  positivity

lemma givensC_pos (k : ℕ) : 0 < givensC k := by
  unfold givensC
  positivity

lemma givensC_le_one (k : ℕ) : givensC k ≤ 1 := by
  unfold givensC
  rw [div_le_one (by positivity)]
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg (oddWeight k)])

/-- The elementary lower estimate `cₖ ≥ 1 - 2wₖ²`. -/
lemma one_sub_two_mul_oddWeight_sq_le_givensC (k : ℕ) :
    1 - 2 * oddWeight k ^ 2 ≤ givensC k := by
  let t := oddWeight k ^ 2
  have ht : 0 ≤ t := sq_nonneg _
  have hsqrtpos : 0 < Real.sqrt (1 + 4 * t) := by positivity
  have hsqrtupper : Real.sqrt (1 + 4 * t) ≤ 1 + 2 * t := by
    simpa only [show (4 * t) / 2 = 2 * t by ring] using
      Real.sqrt_one_add_le (x := 4 * t) (by nlinarith)
  have hinv : 1 / (1 + 2 * t) ≤ 1 / Real.sqrt (1 + 4 * t) :=
    one_div_le_one_div_of_le hsqrtpos hsqrtupper
  have hlinear : 1 - 2 * t ≤ 1 / (1 + 2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg t]
  exact hlinear.trans hinv

private lemma one_sub_prod_le_sum_one_sub
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∏ i ∈ s, x i ≤ ∑ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hprod1 : ∏ i ∈ s, x i ≤ 1 :=
        Finset.prod_le_one
          (fun i hi ↦ hx0 i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hx1 i (Finset.mem_insert_of_mem hi))
      have ih' := ih
        (fun i hi ↦ hx0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hx1 i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        1 - x a * ∏ i ∈ s, x i =
            (1 - x a) + x a * (1 - ∏ i ∈ s, x i) := by ring
        _ ≤ (1 - x a) + (1 - ∏ i ∈ s, x i) := by
          gcongr
          exact mul_le_of_le_one_left (sub_nonneg.mpr hprod1) hxa1
        _ ≤ (1 - x a) + ∑ i ∈ s, (1 - x i) := by
          gcongr

/-- Product form of the coefficient lower estimate. -/
theorem one_sub_two_mul_sum_oddWeight_sq_le_prod_givensC (s : Finset ℕ) :
    1 - 2 * ∑ k ∈ s, oddWeight k ^ 2 ≤ ∏ k ∈ s, givensC k := by
  have hprod := one_sub_prod_le_sum_one_sub s givensC
    (fun k _ ↦ givensC_pos k |>.le) (fun k _ ↦ givensC_le_one k)
  have hsum :
      (∑ k ∈ s, (1 - givensC k)) ≤ ∑ k ∈ s, 2 * oddWeight k ^ 2 := by
    exact Finset.sum_le_sum fun k _ ↦ by
      linarith [one_sub_two_mul_oddWeight_sq_le_givensC k]
  rw [← Finset.mul_sum] at hsum
  linarith

/-- Each pair `(cₖ,sₖ)` lies exactly on the unit circle. -/
theorem givensC_sq_add_givensS_sq (k : ℕ) :
    givensC k ^ 2 + givensS k ^ 2 = 1 := by
  have hrad : 0 ≤ 1 + 4 * oddWeight k ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + 4 * oddWeight k ^ 2) ≠ 0 := by positivity
  unfold givensS givensC
  rw [div_pow]
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt hrad]

/-- A telescoping potential for reciprocal-square tails. -/
private def oddTailPotential (k : ℕ) : ℝ := 1 / (4 * k)

private lemma oddWeight_sq_le_potential_drop (k : ℕ) (hk : 0 < k) :
    oddWeight k ^ 2 ≤ oddTailPotential k - oddTailPotential (k + 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1R : (0 : ℝ) < k + 1 := by positivity
  have hdrop :
      oddTailPotential k - oddTailPotential (k + 1) =
        1 / (4 * (k : ℝ) * (k + 1 : ℝ)) := by
    unfold oddTailPotential
    push_cast
    field_simp [ne_of_gt hkR, ne_of_gt hk1R]
    ring
  rw [hdrop]
  unfold oddWeight oddMode
  push_cast
  rw [div_pow]
  simp only [one_pow]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma sum_potential_drop (start N : ℕ) (hstartN : start ≤ N) :
    (∑ k ∈ Finset.Ico start N,
      (oddTailPotential k - oddTailPotential (k + 1))) =
        oddTailPotential start - oddTailPotential N := by
  induction N with
  | zero =>
      have : start = 0 := by omega
      subst start
      simp
  | succ N ih =>
      by_cases hs : start ≤ N
      · rw [Finset.sum_Ico_succ_top hs, ih hs]
        ring
      · have heq : start = N + 1 := by omega
        subst start
        simp

/-- Finite odd reciprocal-square tails are strictly below the elementary
integral bound `1/(4 start)`. -/
theorem oddWeight_sq_sum_Ico_lt (start N : ℕ) (hstart : 0 < start) :
    (∑ k ∈ Finset.Ico start N, oddWeight k ^ 2) < 1 / (4 * start : ℝ) := by
  by_cases hstartN : start ≤ N
  · have hsum :
        (∑ k ∈ Finset.Ico start N, oddWeight k ^ 2) ≤
          ∑ k ∈ Finset.Ico start N,
            (oddTailPotential k - oddTailPotential (k + 1)) := by
        exact Finset.sum_le_sum fun k hk ↦
          oddWeight_sq_le_potential_drop k (by
            have := (Finset.mem_Ico.mp hk).1
            omega)
    rw [sum_potential_drop start N hstartN] at hsum
    have hpotentialStart : oddTailPotential start = 1 / (4 * start : ℝ) := by
      simp [oddTailPotential]
    have hpotentialN : 0 < oddTailPotential N := by
      unfold oddTailPotential
      have : 0 < N := lt_of_lt_of_le hstart hstartN
      positivity
    rw [hpotentialStart] at hsum
    linarith
  · have hempty : Finset.Ico start N = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

/-- The first-row tail estimate in Lemma 5.2. -/
theorem oddWeight_sq_sum_from_one_lt (N : ℕ) :
    (∑ k ∈ Finset.Ico 1 N, oddWeight k ^ 2) < 1 / 4 := by
  simpa using oddWeight_sq_sum_Ico_lt 1 N (by norm_num)

/-- The tail estimate used for every later row in Lemma 5.2. -/
theorem oddWeight_sq_sum_from_two_lt (N : ℕ) :
    (∑ k ∈ Finset.Ico 2 N, oddWeight k ^ 2) < 1 / 8 := by
  convert oddWeight_sq_sum_Ico_lt 2 N (by norm_num) using 1
  all_goals norm_num

lemma givensS_pos (k : ℕ) : 0 < givensS k := by
  unfold givensS
  exact mul_pos (mul_pos (by norm_num) (oddWeight_pos k)) (givensC_pos k)

lemma givensS_le_two_mul_oddWeight (k : ℕ) :
    givensS k ≤ 2 * oddWeight k := by
  unfold givensS
  have hw := oddWeight_pos k
  have hc := givensC_le_one k
  nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * oddWeight k)]

/-- Dominance inequality for the first row in the explicit Givens product. -/
theorem givens_first_row_dominance (N : ℕ) :
    |∏ k ∈ Finset.Ico 1 N, givensC k| >
      ∑ k ∈ Finset.Ico 1 N,
        oddWeight k * |-(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l)| := by
  let S : ℝ := ∑ k ∈ Finset.Ico 1 N, oddWeight k ^ 2
  have hS : S < 1 / 4 := oddWeight_sq_sum_from_one_lt N
  have hmain0 : 0 ≤ ∏ k ∈ Finset.Ico 1 N, givensC k :=
    Finset.prod_nonneg fun k _ ↦ givensC_pos k |>.le
  have hmain : 1 - 2 * S ≤ |∏ k ∈ Finset.Ico 1 N, givensC k| := by
    rw [abs_of_nonneg hmain0]
    exact one_sub_two_mul_sum_oddWeight_sq_le_prod_givensC (Finset.Ico 1 N)
  have htail :
      (∑ k ∈ Finset.Ico 1 N,
        oddWeight k * |-(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l)|) ≤ 2 * S := by
    calc
      (∑ k ∈ Finset.Ico 1 N,
          oddWeight k * |-(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l)|) ≤
          ∑ k ∈ Finset.Ico 1 N, 2 * oddWeight k ^ 2 := by
            exact Finset.sum_le_sum fun k _ ↦ by
              have hprod0 : 0 ≤ ∏ l ∈ Finset.Ico 1 k, givensC l :=
                Finset.prod_nonneg fun l _ ↦ givensC_pos l |>.le
              have hprod1 : ∏ l ∈ Finset.Ico 1 k, givensC l ≤ 1 :=
                Finset.prod_le_one
                  (fun l _ ↦ givensC_pos l |>.le) (fun l _ ↦ givensC_le_one l)
              rw [abs_neg, abs_mul, abs_of_pos (givensS_pos k), abs_of_nonneg hprod0]
              have hs := givensS_le_two_mul_oddWeight k
              have hw := oddWeight_pos k
              nlinarith [mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_right (givensS_pos k).le hprod1) hw.le]
      _ = 2 * S := by
        change (∑ k ∈ Finset.Ico 1 N, 2 * oddWeight k ^ 2) =
          2 * ∑ k ∈ Finset.Ico 1 N, oddWeight k ^ 2
        rw [Finset.mul_sum]
  nlinarith

/-- Dominance inequality for every later row in the explicit Givens
product.  Coefficients with indices strictly between `0` and `j` are zero,
so only the displayed diagonal and upper-tail terms occur. -/
theorem givens_later_row_dominance (N j : ℕ) (hj : 1 ≤ j) :
    |givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l| >
      oddWeight j * |givensC j| +
        ∑ k ∈ Finset.Ico (j + 1) N,
          oddWeight k *
            |-(givensS j * givensS k *
              ∏ l ∈ Finset.Ico (j + 1) k, givensC l)| := by
  let S : ℝ := ∑ k ∈ Finset.Ico (j + 1) N, oddWeight k ^ 2
  have hSraw := oddWeight_sq_sum_Ico_lt (j + 1) N (by omega)
  have hden : (8 : ℝ) ≤ 4 * (j + 1 : ℕ) := by
    exact_mod_cast (show 8 ≤ 4 * (j + 1) by omega)
  have hfrac : (1 / (4 * ((j + 1 : ℕ) : ℝ))) ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hS : S < 1 / 8 := hSraw.trans_le hfrac
  have hprod0 : 0 ≤ ∏ l ∈ Finset.Ico (j + 1) N, givensC l :=
    Finset.prod_nonneg fun l _ ↦ givensC_pos l |>.le
  have hmain :
      givensS j * (1 - 2 * S) ≤
        |givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l| := by
    rw [abs_mul, abs_of_pos (givensS_pos j), abs_of_nonneg hprod0]
    exact mul_le_mul_of_nonneg_left
      (one_sub_two_mul_sum_oddWeight_sq_le_prod_givensC
        (Finset.Ico (j + 1) N)) (givensS_pos j).le
  have htail :
      oddWeight j * |givensC j| +
          (∑ k ∈ Finset.Ico (j + 1) N,
            oddWeight k *
              |-(givensS j * givensS k *
                ∏ l ∈ Finset.Ico (j + 1) k, givensC l)|) ≤
        oddWeight j * givensC j + 4 * oddWeight j * givensC j * S := by
    rw [abs_of_pos (givensC_pos j)]
    gcongr
    calc
      (∑ k ∈ Finset.Ico (j + 1) N,
          oddWeight k *
            |-(givensS j * givensS k *
              ∏ l ∈ Finset.Ico (j + 1) k, givensC l)|) ≤
          ∑ k ∈ Finset.Ico (j + 1) N,
            4 * oddWeight j * givensC j * oddWeight k ^ 2 := by
              exact Finset.sum_le_sum fun k _ ↦ by
                have hp0 : 0 ≤ ∏ l ∈ Finset.Ico (j + 1) k, givensC l :=
                  Finset.prod_nonneg fun l _ ↦ givensC_pos l |>.le
                have hp1 : ∏ l ∈ Finset.Ico (j + 1) k, givensC l ≤ 1 :=
                  Finset.prod_le_one
                    (fun l _ ↦ givensC_pos l |>.le) (fun l _ ↦ givensC_le_one l)
                rw [abs_neg, abs_mul, abs_mul, abs_of_pos (givensS_pos j),
                  abs_of_pos (givensS_pos k), abs_of_nonneg hp0]
                calc
                  oddWeight k * (givensS j * givensS k *
                      ∏ l ∈ Finset.Ico (j + 1) k, givensC l) ≤
                      oddWeight k * (givensS j * givensS k * 1) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_left hp1
                            (mul_nonneg (givensS_pos j).le (givensS_pos k).le))
                          (oddWeight_pos k).le
                  _ ≤ oddWeight k * (givensS j * (2 * oddWeight k) * 1) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right
                            (mul_le_mul_of_nonneg_left
                              (givensS_le_two_mul_oddWeight k) (givensS_pos j).le)
                            (by norm_num))
                          (oddWeight_pos k).le
                  _ = 4 * oddWeight j * givensC j * oddWeight k ^ 2 := by
                    unfold givensS
                    ring
      _ = 4 * oddWeight j * givensC j * S := by
        change (∑ k ∈ Finset.Ico (j + 1) N,
          4 * oddWeight j * givensC j * oddWeight k ^ 2) =
            4 * oddWeight j * givensC j *
              ∑ k ∈ Finset.Ico (j + 1) N, oddWeight k ^ 2
        rw [Finset.mul_sum]
  have hfactor : 0 < oddWeight j * givensC j :=
    mul_pos (oddWeight_pos j) (givensC_pos j)
  have hgap : 0 < 1 - 8 * S := by nlinarith [hS]
  have hsformula : givensS j = 2 * oddWeight j * givensC j := rfl
  have hstrict :
      oddWeight j * givensC j + 4 * oddWeight j * givensC j * S <
        |givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l| := by
    calc
      oddWeight j * givensC j + 4 * oddWeight j * givensC j * S <
          givensS j * (1 - 2 * S) := by
            rw [hsformula]
            nlinarith [mul_pos hfactor hgap]
      _ ≤ |givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l| := hmain
  exact htail.trans_lt hstrict

/-- Action of the `k`th Givens rotation on a real coordinate vector. -/
def givensRotate (k : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun i ↦
  if i = 0 then givensC k * x 0 - givensS k * x k
  else if i = k then givensS k * x 0 + givensC k * x k
  else x i

/-- One Givens rotation preserves the finite coordinate energy whenever both
rotated coordinates lie in the summation range. -/
theorem givensRotate_energy (N k : ℕ) (hk0 : k ≠ 0) (hkN : k < N)
    (x : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, givensRotate k x i ^ 2) =
      ∑ i ∈ Finset.range N, x i ^ 2 := by
  have h0N : 0 ∈ Finset.range N := by simp [Nat.zero_lt_of_lt hkN]
  have hkMem : k ∈ (Finset.range N \ {0}) := by simp [hkN, hk0]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem h0N,
    Finset.sum_eq_add_sum_diff_singleton_of_mem h0N,
    Finset.sum_eq_add_sum_diff_singleton_of_mem hkMem,
    Finset.sum_eq_add_sum_diff_singleton_of_mem hkMem]
  have hrest :
      (∑ i ∈ ((Finset.range N \ {0}) \ {k}), givensRotate k x i ^ 2) =
        ∑ i ∈ ((Finset.range N \ {0}) \ {k}), x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_sdiff.mp hi
    have hi'' := Finset.mem_sdiff.mp hi'.1
    have hi0 : i ≠ 0 := by simpa using hi''.2
    have hik : i ≠ k := by simpa using hi'.2
    simp [givensRotate, hi0, hik]
  rw [hrest]
  simp [givensRotate, hk0]
  have hcs := givensC_sq_add_givensS_sq k
  ring_nf at hcs ⊢
  nlinarith

/-- Apply consecutive rotations with indices `start, …, start+count-1`, in
the order appropriate to the matrix product `R_start ⋯ R_last`. -/
def givensMixRange : ℕ → ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | _, 0, x => x
  | start, count + 1, x =>
      givensRotate start (givensMixRange (start + 1) count x)

/-- Rotations starting above a nonzero coordinate leave that coordinate
fixed. -/
theorem givensMixRange_apply_lt (start count i : ℕ) (hi0 : i ≠ 0)
    (hi : i < start) (x : ℕ → ℝ) :
    givensMixRange start count x i = x i := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [givensMixRange]
      simp [givensRotate, hi0, ne_of_lt hi]
      exact ih (start + 1) (by omega)

/-- Explicit zeroth-coordinate formula for a consecutive Givens product. -/
theorem givensMixRange_apply_zero (start count : ℕ) (hstart : 0 < start)
    (x : ℕ → ℝ) :
    givensMixRange start count x 0 =
      (∏ k ∈ Finset.Ico start (start + count), givensC k) * x 0 -
        ∑ k ∈ Finset.Ico start (start + count),
          givensS k * (∏ l ∈ Finset.Ico start k, givensC l) * x k := by
  induction count generalizing start with
  | zero => simp [givensMixRange]
  | succ count ih =>
      have hfixed :
          givensMixRange (start + 1) count x start = x start :=
        givensMixRange_apply_lt (start + 1) count start (by omega) (by omega) x
      rw [givensMixRange]
      simp only [givensRotate, if_pos]
      rw [ih (start + 1) (by omega), hfixed]
      have hend : start < start + (count + 1) := by omega
      rw [Finset.prod_eq_prod_Ico_succ_bot hend,
        Finset.sum_eq_sum_Ico_succ_bot hend]
      simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
      have hsum :
          (∑ k ∈ Finset.Ico (start + 1) (start + (count + 1)),
              givensS k * (∏ l ∈ Finset.Ico start k, givensC l) * x k) =
            givensC start *
              ∑ k ∈ Finset.Ico (start + 1) (start + (count + 1)),
                givensS k *
                  (∏ l ∈ Finset.Ico (start + 1) k, givensC l) * x k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hsk : start < k := (Finset.mem_Ico.mp hk).1
        rw [Finset.prod_eq_prod_Ico_succ_bot hsk]
        ring
      rw [hsum]
      simp only [sub_eq_add_neg, mul_add, mul_neg, neg_add_rev, mul_assoc,
        neg_smul, one_smul, neg_one_zsmul, neg_one_smul ℝ]
      simp only [add_assoc]
      have hcount : 1 + count = count + 1 := by omega
      rw [hcount]

/-- Explicit formula for a coordinate which is actually rotated.  This is
the later-row formula in the Givens product, before specializing the input
to a standard basis vector. -/
theorem givensMixRange_apply_mem (start count j : ℕ) (hstart : 0 < start)
    (hj : j ∈ Finset.Ico start (start + count)) (x : ℕ → ℝ) :
    givensMixRange start count x j =
      givensS j *
          ((∏ k ∈ Finset.Ico (j + 1) (start + count), givensC k) * x 0 -
            ∑ k ∈ Finset.Ico (j + 1) (start + count),
              givensS k * (∏ l ∈ Finset.Ico (j + 1) k, givensC l) * x k) +
        givensC j * x j := by
  induction count generalizing start with
  | zero => simp at hj
  | succ count ih =>
      have hjbounds := Finset.mem_Ico.mp hj
      rw [givensMixRange]
      by_cases hjs : j = start
      · subst j
        have hfixed :
            givensMixRange (start + 1) count x start = x start :=
          givensMixRange_apply_lt (start + 1) count start (by omega) (by omega) x
        simp only [givensRotate, if_neg (by omega : start ≠ 0), if_pos]
        rw [givensMixRange_apply_zero (start + 1) count (by omega), hfixed]
        have hend : start + 1 + count = start + (count + 1) := by omega
        rw [hend]
      · have hj0 : j ≠ 0 := by omega
        have hjinner : j ∈ Finset.Ico (start + 1) ((start + 1) + count) := by
          exact Finset.mem_Ico.mpr (by omega)
        simp only [givensRotate, if_neg hj0, if_neg hjs]
        rw [ih (start + 1) (by omega) hjinner]
        have hend : start + 1 + count = start + (count + 1) := by omega
        rw [hend]

/-- Consecutive Givens mixing preserves energy on every containing finite
coordinate range. -/
theorem givensMixRange_energy (N start count : ℕ)
    (hstart : 0 < start) (hend : start + count ≤ N) (x : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, givensMixRange start count x i ^ 2) =
      ∑ i ∈ Finset.range N, x i ^ 2 := by
  induction count generalizing start with
  | zero => simp [givensMixRange]
  | succ count ih =>
      have hstartN : start < N := by omega
      calc
        (∑ i ∈ Finset.range N, givensMixRange start (count + 1) x i ^ 2) =
            ∑ i ∈ Finset.range N,
              givensRotate start (givensMixRange (start + 1) count x) i ^ 2 := by
                rfl
        _ = ∑ i ∈ Finset.range N, givensMixRange (start + 1) count x i ^ 2 :=
          givensRotate_energy N start (by omega) hstartN _
        _ = ∑ i ∈ Finset.range N, x i ^ 2 :=
          ih (start + 1) (by omega) (by omega)

/-- The finite `N`-mode mixing used in the orientation-free certificate. -/
def givensMix (N : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  givensMixRange 1 (N - 1) x

theorem givensMix_energy (N : ℕ) (hN : 0 < N) (x : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, givensMix N x i ^ 2) =
      ∑ i ∈ Finset.range N, x i ^ 2 := by
  apply givensMixRange_energy N 1 (N - 1) (by norm_num)
  omega

/-- Standard coordinate vector in the ambient sequence space. -/
def natBasis (k : ℕ) : ℕ → ℝ := fun i ↦ if i = k then 1 else 0

/-- Matrix coefficients of the finite Givens mixing. -/
def givensMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun j k ↦
  givensMix N (natBasis k) j

/-- The `(0,0)` entry of the concrete Givens matrix. -/
theorem givensMatrix_zero_zero (N : ℕ) (hN : 0 < N) :
    givensMatrix N ⟨0, hN⟩ ⟨0, hN⟩ =
      ∏ l ∈ Finset.Ico 1 N, givensC l := by
  unfold givensMatrix givensMix
  rw [givensMixRange_apply_zero 1 (N - 1) (by norm_num)]
  have hend : 1 + (N - 1) = N := by omega
  rw [hend]
  simp [natBasis]

/-- Every higher entry in the first row of the concrete Givens matrix. -/
theorem givensMatrix_zero_high (N k : ℕ) (hk : 0 < k) (hkN : k < N) :
    givensMatrix N ⟨0, by omega⟩ ⟨k, hkN⟩ =
      -(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l) := by
  unfold givensMatrix givensMix
  rw [givensMixRange_apply_zero 1 (N - 1) (by norm_num)]
  have hend : 1 + (N - 1) = N := by omega
  have hk0 : 0 ≠ k := by omega
  have hk1 : 1 ≤ k := by omega
  rw [hend]
  simp [natBasis, Finset.mem_Ico, hk0, hk1, hkN]

/-- First-column entry in every later row. -/
theorem givensMatrix_later_zero (N j : ℕ) (hj : 0 < j) (hjN : j < N) :
    givensMatrix N ⟨j, hjN⟩ ⟨0, by omega⟩ =
      givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l := by
  unfold givensMatrix givensMix
  have hend : 1 + (N - 1) = N := by omega
  have hjmem : j ∈ Finset.Ico 1 (1 + (N - 1)) := by
    exact Finset.mem_Ico.mpr (by omega)
  rw [givensMixRange_apply_mem 1 (N - 1) j (by norm_num) hjmem]
  rw [hend]
  have hj0 : j ≠ 0 := by omega
  simp [natBasis, Finset.mem_Ico, hj0]

/-- Entries strictly below the diagonal, apart from the first column, vanish. -/
theorem givensMatrix_later_lower (N j k : ℕ)
    (hk : 0 < k) (hkj : k < j) (hjN : j < N) :
    givensMatrix N ⟨j, hjN⟩ ⟨k, by omega⟩ = 0 := by
  unfold givensMatrix givensMix
  have hend : 1 + (N - 1) = N := by omega
  have hjmem : j ∈ Finset.Ico 1 (1 + (N - 1)) := by
    exact Finset.mem_Ico.mpr (by omega)
  rw [givensMixRange_apply_mem 1 (N - 1) j (by norm_num) hjmem]
  rw [hend]
  have hk0 : 0 ≠ k := by omega
  have hjk : j ≠ k := by omega
  have hnot : ¬j + 1 ≤ k := by omega
  simp [natBasis, Finset.mem_Ico, hk0, hjk, hnot]

/-- Diagonal entry in every later row. -/
theorem givensMatrix_later_diag (N j : ℕ) (hj : 0 < j) (hjN : j < N) :
    givensMatrix N ⟨j, hjN⟩ ⟨j, hjN⟩ = givensC j := by
  unfold givensMatrix givensMix
  have hend : 1 + (N - 1) = N := by omega
  have hjmem : j ∈ Finset.Ico 1 (1 + (N - 1)) := by
    exact Finset.mem_Ico.mpr (by omega)
  rw [givensMixRange_apply_mem 1 (N - 1) j (by norm_num) hjmem]
  rw [hend]
  have hj0 : 0 ≠ j := by omega
  simp [natBasis, Finset.mem_Ico, hj0]

/-- Entries above the diagonal in every later row. -/
theorem givensMatrix_later_upper (N j k : ℕ)
    (hj : 0 < j) (hjk : j < k) (hkN : k < N) :
    givensMatrix N ⟨j, by omega⟩ ⟨k, hkN⟩ =
      -(givensS j * givensS k *
        ∏ l ∈ Finset.Ico (j + 1) k, givensC l) := by
  unfold givensMatrix givensMix
  have hend : 1 + (N - 1) = N := by omega
  have hjmem : j ∈ Finset.Ico 1 (1 + (N - 1)) := by
    exact Finset.mem_Ico.mpr (by omega)
  rw [givensMixRange_apply_mem 1 (N - 1) j (by norm_num) hjmem]
  rw [hend]
  have hk0 : 0 ≠ k := by omega
  have hjk : j ≠ k := by omega
  have hj1k : j + 1 ≤ k := by omega
  simp [natBasis, Finset.mem_Ico, hk0, hjk, hj1k, hkN]
  ring

/-- Every row of the concrete Givens product has a derivative-weighted
dominant first harmonic.  This is Lemma 5.2 in the zero-based indexing used
by the formalization. -/
theorem givensMix_row_dominance (N j : ℕ) (hjN : j < N) :
    (∑ k ∈ Finset.Ico 1 N,
        oddWeight k * |givensMix N (natBasis k) j|) <
      |givensMix N (natBasis 0) j| := by
  by_cases hj0 : j = 0
  · subst j
    have hentry00 :
        givensMix N (natBasis 0) 0 =
          ∏ l ∈ Finset.Ico 1 N, givensC l := by
      exact givensMatrix_zero_zero N (by omega)
    have hsum :
        (∑ k ∈ Finset.Ico 1 N,
            oddWeight k * |givensMix N (natBasis k) 0|) =
          ∑ k ∈ Finset.Ico 1 N,
            oddWeight k *
              |-(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l)| := by
      apply Finset.sum_congr rfl
      intro k hk
      have hbounds := Finset.mem_Ico.mp hk
      rw [show givensMix N (natBasis k) 0 =
          -(givensS k * ∏ l ∈ Finset.Ico 1 k, givensC l) by
        exact givensMatrix_zero_high N k (by omega) hbounds.2]
    rw [hentry00, hsum]
    exact givens_first_row_dominance N
  · have hj : 0 < j := by omega
    have hentry0 :
        givensMix N (natBasis 0) j =
          givensS j * ∏ l ∈ Finset.Ico (j + 1) N, givensC l := by
      exact givensMatrix_later_zero N j hj hjN
    have hlower :
        (∑ k ∈ Finset.Ico 1 j,
            oddWeight k * |givensMix N (natBasis k) j|) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hbounds := Finset.mem_Ico.mp hk
      rw [show givensMix N (natBasis k) j = 0 by
        exact givensMatrix_later_lower N j k (by omega) hbounds.2 hjN]
      simp
    have hdiag :
        givensMix N (natBasis j) j = givensC j := by
      exact givensMatrix_later_diag N j hj hjN
    have hupper :
        (∑ k ∈ Finset.Ico (j + 1) N,
            oddWeight k * |givensMix N (natBasis k) j|) =
          ∑ k ∈ Finset.Ico (j + 1) N,
            oddWeight k *
              |-(givensS j * givensS k *
                ∏ l ∈ Finset.Ico (j + 1) k, givensC l)| := by
      apply Finset.sum_congr rfl
      intro k hk
      have hbounds := Finset.mem_Ico.mp hk
      rw [show givensMix N (natBasis k) j =
          -(givensS j * givensS k *
            ∏ l ∈ Finset.Ico (j + 1) k, givensC l) by
        exact givensMatrix_later_upper N j k hj (by omega) hbounds.2]
    rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ j) hjN.le,
      Finset.sum_eq_sum_Ico_succ_bot hjN, hlower, zero_add, hdiag, hupper,
      hentry0]
    exact givens_later_row_dominance N j (by omega)

/-- The concrete Givens matrix has unit column energies. -/
theorem givensMatrix_column_energy (N : ℕ) (k : Fin N) :
    (∑ j : Fin N, givensMatrix N j k ^ 2) = 1 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (by
    intro h
    subst N
    exact Fin.elim0 k)
  change (∑ j : Fin N, givensMix N (natBasis (k : ℕ)) (j : ℕ) ^ 2) = 1
  calc
    (∑ j : Fin N, givensMix N (natBasis (k : ℕ)) (j : ℕ) ^ 2) =
        ∑ j ∈ Finset.range N, givensMix N (natBasis (k : ℕ)) j ^ 2 :=
      Fin.sum_univ_eq_sum_range
        (fun j ↦ givensMix N (natBasis (k : ℕ)) j ^ 2) N
    _ = ∑ j ∈ Finset.range N, natBasis (k : ℕ) j ^ 2 :=
      givensMix_energy N hN _
    _ = 1 := by simp [natBasis, k.isLt]

end

end GromovFilling
