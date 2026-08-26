import GromovFilling.Oriented

/-!
# Rigorous numerical enclosures

All decimal conclusions in this file are proved from rational arithmetic.
For `ζ(3)` we use a four-term Euler--Maclaurin tail written as an elementary
telescoping lower certificate; no floating-point evaluation is trusted.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

open Filter Real

/-- A rational lower certificate for the tail `∑_{k ≥ x} k⁻³`. -/
def zetaTailLower (x : ℝ) : ℝ :=
  1 / (2 * x ^ 2) + 1 / (2 * x ^ 3) + 1 / (4 * x ^ 4) - 1 / (12 * x ^ 6)

/-- The telescoping increment of `zetaTailLower` is no larger than `x⁻³`.
The exact nonnegative remainder is `(1 + 2x)^3 / (12 x^6 (1+x)^6)`. -/
lemma zetaTailLower_step {x : ℝ} (hx : 0 < x) :
    zetaTailLower x - zetaTailLower (x + 1) ≤ 1 / x ^ 3 := by
  have hx1 : 0 < x + 1 := by positivity
  have hidentity :
      1 / x ^ 3 - (zetaTailLower x - zetaTailLower (x + 1)) =
        (1 + 2 * x) ^ 3 / (12 * x ^ 6 * (1 + x) ^ 6) := by
    unfold zetaTailLower
    field_simp [hx.ne', hx1.ne']
    ring
  have hrem : 0 ≤ (1 + 2 * x) ^ 3 / (12 * x ^ 6 * (1 + x) ^ 6) := by positivity
  linarith

lemma summable_one_div_nat_add_pow (offset p : ℕ) (hp : 1 < p) :
    Summable (fun k : ℕ ↦ 1 / ((offset + k : ℕ) : ℝ) ^ p) := by
  have h := (summable_nat_add_iff offset).2 (Real.summable_one_div_nat_pow.mpr hp)
  simpa only [Nat.add_comm] using h

lemma summable_zetaTailLower_add (offset : ℕ) :
    Summable (fun k : ℕ ↦ zetaTailLower ((offset + k : ℕ) : ℝ)) := by
  have h2 := summable_one_div_nat_add_pow offset 2 (by norm_num)
  have h3 := summable_one_div_nat_add_pow offset 3 (by norm_num)
  have h4 := summable_one_div_nat_add_pow offset 4 (by norm_num)
  have h6 := summable_one_div_nat_add_pow offset 6 (by norm_num)
  apply (((h2.mul_left (1 / 2)).add (h3.mul_left (1 / 2))).add
    (h4.mul_left (1 / 4))).sub (h6.mul_left (1 / 12)) |>.congr
  intro k
  unfold zetaTailLower
  ring

/-- The telescoping lower certificate really sums to its initial value. -/
lemma hasSum_zetaTailLower_diff (offset : ℕ) :
    HasSum
      (fun k : ℕ ↦
        zetaTailLower ((offset + k : ℕ) : ℝ) -
          zetaTailLower ((offset + k + 1 : ℕ) : ℝ))
      (zetaTailLower offset) := by
  let h : ℕ → ℝ := fun k ↦ zetaTailLower ((offset + k : ℕ) : ℝ)
  have hh : Summable h := summable_zetaTailLower_add offset
  have hhshift : Summable (fun k : ℕ ↦ h (k + 1)) := (summable_nat_add_iff 1).2 hh
  have hdiff : Summable (fun k : ℕ ↦ h k - h (k + 1)) := hh.sub hhshift
  have hseries : HasSum (fun k : ℕ ↦ h k - h (k + 1)) (h 0) := by
    rw [hdiff.hasSum_iff_tendsto_nat]
    have ht : Tendsto (fun n ↦ h 0 - h n) atTop (nhds (h 0)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hh.tendsto_atTop_zero
    convert ht using 1
    funext n
    exact Finset.sum_range_sub' h n
  simpa [h, Nat.cast_add, Nat.add_assoc] using hseries

/-- A finite prefix plus `zetaTailLower` is a lower bound for `ζ(3)`. -/
theorem zetaThree_lower_from_prefix {offset : ℕ} (hoffset : 0 < offset) :
    (∑ k ∈ Finset.range offset, 1 / (k : ℝ) ^ 3) + zetaTailLower offset ≤ zetaThree := by
  let f : ℕ → ℝ := fun k ↦ 1 / (k : ℝ) ^ 3
  have htail : zetaTailLower offset ≤ ∑' k : ℕ, f (k + offset) := by
    have hlower := hasSum_zetaTailLower_diff offset
    have hupper : HasSum (fun k : ℕ ↦ f (k + offset)) (∑' k : ℕ, f (k + offset)) :=
      ((summable_nat_add_iff offset).2 summable_zetaThree).hasSum
    apply hasSum_le (hf := hlower) (hg := hupper)
    intro k
    simpa only [f, Nat.cast_add, Nat.cast_one, add_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
        (zetaTailLower_step (x := ((offset + k : ℕ) : ℝ)) (by positivity))
  calc
    (∑ k ∈ Finset.range offset, 1 / (k : ℝ) ^ 3) + zetaTailLower offset ≤
        (∑ k ∈ Finset.range offset, f k) + ∑' k : ℕ, f (k + offset) := by
          simpa only [f] using
            add_le_add_right htail (∑ k ∈ Finset.range offset, f k)
    _ = zetaThree := by
      simpa only [f, zetaThree] using
        summable_zetaThree.sum_add_tsum_nat_add offset

/-- A nine-decimal rational lower enclosure, sufficient for the strict
`5.38982446` theorem. -/
theorem zetaThree_gt_1202056903 :
    (1202056903 / 1000000000 : ℝ) < zetaThree := by
  have hprefix := zetaThree_lower_from_prefix (offset := 15) (by norm_num)
  have hrational :
      (1202056903 / 1000000000 : ℝ) <
        (∑ k ∈ Finset.range 15, 1 / (k : ℝ) ^ 3) + zetaTailLower 15 := by
    norm_num [zetaTailLower, Finset.sum_range_succ]
  exact hrational.trans_le hprefix

/-- Constructive ten-decimal lower bound for `π`.  The list consists of
directed rational upper approximants to the iterated half-angle radicals. -/
theorem pi_gt_31415926535 : (31415926535 / 10000000000 : ℝ) < Real.pi := by
  pi_lower_bound
    [886731088897 / 627013566048,
     58134718954 / 31462283181,
     1117366430572 / 569628466545,
     1476437478537 / 741790664068,
     1708099254494 / 855079608083,
     891379325607 / 445823936638,
     916988763991 / 458528908379,
     1649688052738 / 824859554117,
     657730383517 / 328866739468,
     1935453329465 / 967727803311,
     1866363696871 / 933182122919,
     1077442953935 / 538721516582,
     512794819753 / 256397414590,
     1549862116503 / 774931061813,
     1878198768508 / 939099385333,
     1249811600331 / 624905800345,
     487391710523 / 243695855279,
     1782461112850 / 891230556441]

/-- Constructive ten-decimal upper bound for `π`.  The list consists of
directed rational lower approximants to the iterated half-angle radicals. -/
theorem pi_lt_31415926536 : Real.pi < (31415926536 / 10000000000 : ℝ) := by
  pi_upper_bound
    [1254027132096 / 886731088897,
     1808735806595 / 978880764724,
     261639693095 / 133382758858,
     1250352044049 / 628200981455,
     1912213103119 / 957259612686,
     765001192955 / 382615833213,
     1428024742376 / 714066139055,
     1191070146631 / 595546284306,
     1911920437514 / 955964717709,
     1912498072747 / 956250161448,
     299540482172 / 149770285139,
     973736230807 / 486868151205,
     1734320275611 / 867160153747,
     1112079921023 / 556039963067,
     63534990779 / 31767495426,
     1277662555213 / 638831277790,
     1030485330820 / 515242665447,
     1726759203073 / 863379601552]

private def piLower : ℝ := 31415926535 / 10000000000
private def piUpper : ℝ := 31415926536 / 10000000000
private def zetaLower : ℝ := 1202056903 / 1000000000

/-- Rational lower endpoint for the boundary action at `λ = 0.03`. -/
private def boundaryActionLower : ℝ :=
  14 * zetaLower / piUpper +
    (384 / piUpper ^ 3 - 32 / piLower) * (3 / 100) +
    (3584 * zetaLower / piUpper ^ 5 + 4096 / piUpper ^ 5 -
      (256 / 3) / piLower) * (3 / 100) ^ 2

/-- Rational upper endpoint for the comass at `λ = 0.03`. -/
private def comassBoundUpper : ℝ :=
  1 + (3 / 100) ^ 2 *
    (128 / (9 * piLower ^ 2) + 1280 / (9 * piLower ^ 4) +
      (32 / 9) / (1 - (24 / 25) / piLower ^ 2))

lemma Cstar_sq : Cstar ^ 2 = 128 / 9 := by
  unfold Cstar
  rw [div_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma boundaryLinear_expanded :
    boundaryLinear = 384 / Real.pi ^ 3 - 32 / Real.pi := by
  unfold boundaryLinear
  field_simp [Real.pi_ne_zero]
  ring

private lemma boundaryQuadratic_expanded :
    boundaryQuadratic =
      3584 * zetaThree / Real.pi ^ 5 + 4096 / Real.pi ^ 5 -
        (256 / 3) / Real.pi := by
  unfold boundaryQuadratic
  field_simp [Real.pi_ne_zero]
  ring

private lemma boundaryActionLower_le :
    boundaryActionLower ≤ boundaryAction (3 / 100) := by
  have hpL : piLower < Real.pi := pi_gt_31415926535
  have hpU : Real.pi < piUpper := pi_lt_31415926536
  have hz : zetaLower < zetaThree := zetaThree_gt_1202056903
  have hpL0 : 0 < piLower := by norm_num [piLower]
  have hzL0 : 0 ≤ zetaLower := by norm_num [zetaLower]
  have hC0 : 14 * zetaLower / piUpper ≤ 14 * zetaThree / Real.pi := by
    calc
      14 * zetaLower / piUpper ≤ 14 * zetaLower / Real.pi := by gcongr
      _ ≤ 14 * zetaThree / Real.pi := by gcongr
  have hbpos : 384 / piUpper ^ 3 ≤ 384 / Real.pi ^ 3 := by gcongr
  have hbneg : -(32 / piLower) ≤ -(32 / Real.pi) := by
    have : 32 / Real.pi ≤ 32 / piLower := by gcongr
    linarith
  have hdpos1 : 3584 * zetaLower / piUpper ^ 5 ≤
      3584 * zetaThree / Real.pi ^ 5 := by
    calc
      3584 * zetaLower / piUpper ^ 5 ≤ 3584 * zetaLower / Real.pi ^ 5 := by gcongr
      _ ≤ 3584 * zetaThree / Real.pi ^ 5 := by gcongr
  have hdpos2 : 4096 / piUpper ^ 5 ≤ 4096 / Real.pi ^ 5 := by gcongr
  have hdneg : -((256 / 3) / piLower) ≤ -((256 / 3) / Real.pi) := by
    have : (256 / 3) / Real.pi ≤ (256 / 3) / piLower := by gcongr
    linarith
  rw [boundaryActionLower, boundaryAction, universalConstant, boundaryLinear_expanded,
    boundaryQuadratic_expanded]
  nlinarith

private lemma comassBound_le_upper :
    comassBound (3 / 100) ≤ comassBoundUpper := by
  have hpL : piLower < Real.pi := pi_gt_31415926535
  have hpL0 : 0 < piLower := by norm_num [piLower]
  have hq1 : 128 / (9 * Real.pi ^ 2) ≤ 128 / (9 * piLower ^ 2) := by gcongr
  have hq2 : 1280 / (9 * Real.pi ^ 4) ≤ 1280 / (9 * piLower ^ 4) := by gcongr
  have hdenLower : 0 < 1 - (24 / 25) / piLower ^ 2 := by
    norm_num [piLower]
  have hdenRewrite : 1 - Dstar * (3 / 100) = 1 - (24 / 25) / Real.pi ^ 2 := by
    unfold Dstar
    ring
  have hdenMono : 1 - (24 / 25) / piLower ^ 2 ≤
      1 - (24 / 25) / Real.pi ^ 2 := by
    have : (24 / 25) / Real.pi ^ 2 ≤ (24 / 25) / piLower ^ 2 := by gcongr
    linarith
  have hres : Cstar ^ 2 / (4 * (1 - Dstar * (3 / 100))) ≤
      (32 / 9) / (1 - (24 / 25) / piLower ^ 2) := by
    rw [Cstar_sq, hdenRewrite]
    have hscale (d : ℝ) : (128 / 9) / (4 * d) = (32 / 9) * (1 / d) := by
      by_cases hd : d = 0
      · simp [hd]
      · field_simp [hd]
        ring
    have hone : 1 / (1 - (24 / 25) / Real.pi ^ 2) ≤
        1 / (1 - (24 / 25) / piLower ^ 2) :=
      one_div_le_one_div_of_le hdenLower hdenMono
    calc
      (128 / 9) / (4 * (1 - (24 / 25) / Real.pi ^ 2)) =
          (32 / 9) * (1 / (1 - (24 / 25) / Real.pi ^ 2)) := hscale _
      _ ≤ (32 / 9) * (1 / (1 - (24 / 25) / piLower ^ 2)) := by gcongr
      _ = (32 / 9) / (1 - (24 / 25) / piLower ^ 2) := by ring
  rw [comassBound, comassBoundUpper, Qstar]
  nlinarith

private lemma comassBound_point_zero_three_pos : 0 < comassBound (3 / 100) := by
  have hden : 0 < 1 - Dstar * (3 / 100) :=
    comass_denominator_pos_of_admissible lambda_point_zero_three_admissible
  have hq : 0 ≤ Qstar := by
    unfold Qstar
    positivity
  have hc : 0 ≤ Cstar ^ 2 / (4 * (1 - Dstar * (3 / 100))) := by positivity
  unfold comassBound
  nlinarith [sq_nonneg (3 / 100 : ℝ)]

/-- The exact strict decimal claimed in the oriented headline theorem. -/
theorem nonlinearCertificate_point_zero_three_gt :
    (538982446 / 100000000 : ℝ) < nonlinearCertificate (3 / 100) := by
  have hB := boundaryActionLower_le
  have hC := comassBound_le_upper
  have hCpos := comassBound_point_zero_three_pos
  have hrational :
      (538982446 / 100000000 : ℝ) * comassBoundUpper < boundaryActionLower := by
    norm_num [comassBoundUpper, boundaryActionLower, piLower, piUpper, zetaLower]
  unfold nonlinearCertificate
  rw [lt_div_iff₀ hCpos]
  calc
    (538982446 / 100000000 : ℝ) * comassBound (3 / 100) ≤
        (538982446 / 100000000 : ℝ) * comassBoundUpper := by gcongr
    _ < boundaryActionLower := hrational
    _ ≤ boundaryAction (3 / 100) := hB

end

end GromovFilling
