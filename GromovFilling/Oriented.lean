import GromovFilling.Constants

/-!
# The oriented nonlinear certificate

This module verifies the scalar optimization which turns the first-variation
and quadratic estimates of the note into its global comass bound.  It also
records the exact constants and the one-parameter lower-bound function.
-/

namespace GromovFilling

noncomputable section

open Real

/-- The sharp coefficient of `√δ` in the first-variation estimate. -/
def Cstar : ℝ := 8 * sqrt 2 / 3

/-- The coefficient of `δ` in the first-variation estimate. -/
def Dstar : ℝ := 32 / Real.pi ^ 2

/-- The uniform quadratic estimate for the resonant perturbation. -/
def Qstar : ℝ := 128 / (9 * Real.pi ^ 2) + 1280 / (9 * Real.pi ^ 4)

/-- The linear coefficient in the resonant boundary action. -/
def boundaryLinear : ℝ :=
  512 / Real.pi ^ 3 * (3 / 4 - Real.pi ^ 2 / 16)

/-- The quadratic coefficient in the resonant boundary action. -/
def boundaryQuadratic : ℝ :=
  4096 / Real.pi ^ 5 * (7 / 8 * zetaThree + 1 - Real.pi ^ 4 / 48)

/-- Exact boundary action of the cubic resonant deformation. -/
def boundaryAction (lam : ℝ) : ℝ :=
  universalConstant + boundaryLinear * lam + boundaryQuadratic * lam ^ 2

/-- The global comass upper bound proved in Proposition 11.1 of the note. -/
def comassBound (lam : ℝ) : ℝ :=
  1 + lam ^ 2 * (Qstar + Cstar ^ 2 / (4 * (1 - Dstar * lam)))

/-- The explicit one-parameter oriented area certificate. -/
def nonlinearCertificate (lam : ℝ) : ℝ :=
  boundaryAction lam / comassBound lam

/-- Completing the square in the variable `√δ`. -/
lemma neg_mul_add_mul_sqrt_le (A B delta : ℝ) (hA : 0 < A) (hdelta : 0 ≤ delta) :
    -A * delta + B * sqrt delta ≤ B ^ 2 / (4 * A) := by
  have hsqrt : (sqrt delta) ^ 2 = delta := sq_sqrt hdelta
  have hsq : 0 ≤ 4 * A ^ 2 * delta - 4 * A * B * sqrt delta + B ^ 2 := by
    calc
      0 ≤ (2 * A * sqrt delta - B) ^ 2 := sq_nonneg _
      _ = 4 * A ^ 2 * (sqrt delta) ^ 2 - 4 * A * B * sqrt delta + B ^ 2 := by ring
      _ = 4 * A ^ 2 * delta - 4 * A * B * sqrt delta + B ^ 2 := by rw [hsqrt]
  rw [le_div_iff₀ (by positivity : 0 < 4 * A)]
  ring_nf at hsq ⊢
  nlinarith

/-- The pointwise deficit estimate implies the advertised global comass
bound.  This is the scalar core of Proposition 11.1. -/
theorem nonlinear_comass_optimization
    (lam C D Q omega delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hA : 0 < 1 - D * lam)
    (homega :
      |omega| ≤ 1 - delta + lam * (C * sqrt delta + D * delta) + Q * lam ^ 2) :
    |omega| ≤ 1 + lam ^ 2 * (Q + C ^ 2 / (4 * (1 - D * lam))) := by
  apply homega.trans
  have hsquare := neg_mul_add_mul_sqrt_le (1 - D * lam) (C * lam) delta hA hdelta
  calc
    1 - delta + lam * (C * sqrt delta + D * delta) + Q * lam ^ 2 =
        1 + Q * lam ^ 2 + (-(1 - D * lam) * delta + C * lam * sqrt delta) := by ring
    _ ≤ 1 + Q * lam ^ 2 + (C * lam) ^ 2 / (4 * (1 - D * lam)) := by
      gcongr
    _ = 1 + lam ^ 2 * (Q + C ^ 2 / (4 * (1 - D * lam))) := by ring

lemma pi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos

lemma Dstar_pos : 0 < Dstar := by
  unfold Dstar
  positivity

lemma lambda_point_zero_three_admissible :
    (3 / 100 : ℝ) < Real.pi ^ 2 / 32 := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hp2 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  nlinarith

lemma comass_denominator_pos_of_admissible {lam : ℝ}
    (hlam : lam < Real.pi ^ 2 / 32) : 0 < 1 - Dstar * lam := by
  unfold Dstar
  rw [sub_pos, div_mul_eq_mul_div, div_lt_one (pi_sq_pos)]
  nlinarith

end

end GromovFilling
