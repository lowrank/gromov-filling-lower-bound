import GromovFilling.Numerics
import GromovFilling.SharpenedOriented

/-!
# Rational enclosure of the revised oriented certificate

The square-root and quotient bounds below use rational arithmetic and the
existing kernel proofs of the pi and zeta enclosures. No floating-point
calculation enters the proof.
-/

namespace GromovFilling

noncomputable section

private def piLower : ℝ := 31415926535 / 10000000000
private def piUpper : ℝ := 31415926536 / 10000000000
private def zetaLower : ℝ := 1202056903 / 1000000000
private def radicalUpper : ℝ := 6155169062 / 10000000000
private def bracketUpper : ℝ := 16 / piLower ^ 2 + 8 / (5 * piLower) * radicalUpper

private def boundaryActionLower : ℝ :=
  14 * zetaLower / piUpper +
    (384 / piUpper ^ 3 - 32 / piLower) * (1 / 25) +
    (3584 * zetaLower / piUpper ^ 5 + 4096 / piUpper ^ 5 -
      (256 / 3) / piLower) * (1 / 25) ^ 2

private def comassBoundUpper : ℝ :=
  1 + (1 / 25) ^ 2 *
    (128 / (9 * piLower ^ 2) + 1280 / (9 * piLower ^ 4) +
      (2 * bracketUpper ^ 2) / (4 * (1 - (32 / 25) / piLower ^ 2)))

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
    boundaryActionLower ≤ boundaryAction (1 / 25) := by
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

private lemma sharpenedCstar_sq_le : sharpenedCstar ^ 2 ≤ 2 * bracketUpper ^ 2 := by
  have hpL : piLower < Real.pi := pi_gt_31415926535
  have hpU : Real.pi < piUpper := pi_lt_31415926536
  have hpL0 : 0 < piLower := by norm_num [piLower]
  have hrecip : 16 / piUpper ^ 2 ≤ 16 / Real.pi ^ 2 := by gcongr
  have harg : 0 ≤ 2 - 16 / Real.pi ^ 2 := by
    have h : 16 / Real.pi ^ 2 ≤ (16 / 9 : ℝ) := by
      have hp : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      exact (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by nlinarith)
    linarith
  have hrad : Real.sqrt (2 - 16 / Real.pi ^ 2) ≤ radicalUpper := by
    have hs := Real.sq_sqrt harg
    have hu : 0 ≤ radicalUpper := by norm_num [radicalUpper]
    have hrational : 2 - 16 / piUpper ^ 2 ≤ radicalUpper ^ 2 := by
      norm_num [piUpper, radicalUpper]
    nlinarith [Real.sqrt_nonneg (2 - 16 / Real.pi ^ 2)]
  have hbracket : 16 / Real.pi ^ 2 +
      8 / (5 * Real.pi) * Real.sqrt (2 - 16 / Real.pi ^ 2) ≤ bracketUpper := by
    unfold bracketUpper
    gcongr
  have hnonneg : 0 ≤ 16 / Real.pi ^ 2 +
      8 / (5 * Real.pi) * Real.sqrt (2 - 16 / Real.pi ^ 2) := by positivity
  unfold sharpenedCstar
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

private lemma sharpenedComassBound_le_upper :
    sharpenedComassBound (1 / 25) ≤ comassBoundUpper := by
  have hpL : piLower < Real.pi := pi_gt_31415926535
  have hpL0 : 0 < piLower := by norm_num [piLower]
  have hq1 : 128 / (9 * Real.pi ^ 2) ≤ 128 / (9 * piLower ^ 2) := by gcongr
  have hq2 : 1280 / (9 * Real.pi ^ 4) ≤ 1280 / (9 * piLower ^ 4) := by gcongr
  have hdenLower : 0 < 1 - (32 / 25) / piLower ^ 2 := by norm_num [piLower]
  have hdenRewrite : 1 - Dstar * (1 / 25) = 1 - (32 / 25) / Real.pi ^ 2 := by
    unfold Dstar
    ring
  have hdenMono : 1 - (32 / 25) / piLower ^ 2 ≤
      1 - (32 / 25) / Real.pi ^ 2 := by
    have : (32 / 25) / Real.pi ^ 2 ≤ (32 / 25) / piLower ^ 2 := by gcongr
    linarith
  have hres : sharpenedCstar ^ 2 / (4 * (1 - Dstar * (1 / 25))) ≤
      (2 * bracketUpper ^ 2) / (4 * (1 - (32 / 25) / piLower ^ 2)) := by
    rw [hdenRewrite]
    gcongr
    exact sharpenedCstar_sq_le
  unfold sharpenedComassBound comassBoundUpper Qstar
  nlinarith

/-- The lower endpoint of the interval printed in Section 4. -/
theorem sharpenedNonlinearCertificate_one_div_twenty_five_gt :
    (5401544 / 1000000 : ℝ) < sharpenedNonlinearCertificate (1 / 25) := by
  have hB := boundaryActionLower_le
  have hC := sharpenedComassBound_le_upper
  have hCpos := sharpenedComassBound_pos lambda_one_div_twenty_five_admissible
  have hrational :
      (5401544 / 1000000 : ℝ) * comassBoundUpper < boundaryActionLower := by
    norm_num [comassBoundUpper, boundaryActionLower, bracketUpper, radicalUpper,
      piLower, piUpper, zetaLower]
  unfold sharpenedNonlinearCertificate
  rw [lt_div_iff₀ hCpos]
  calc
    (5401544 / 1000000 : ℝ) * sharpenedComassBound (1 / 25) ≤
        (5401544 / 1000000 : ℝ) * comassBoundUpper := by gcongr
    _ < boundaryActionLower := hrational
    _ ≤ boundaryAction (1 / 25) := hB

end

end GromovFilling

#print axioms GromovFilling.sharpenedNonlinearCertificate_one_div_twenty_five_gt
