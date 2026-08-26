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

/-- The sharp elementary ellipse estimate behind the `Cstar` coefficient.
It follows from
`(4/3)(r²+9Y²) - (r²+4rY) = (r-6Y)²/3`. -/
lemma profile_cross_term_le (r Y : ℝ)
    (hprofile : r ^ 2 + 9 * Y ^ 2 ≤ 2) :
    r ^ 2 + 4 * r * Y ≤ 8 / 3 := by
  nlinarith [sq_nonneg (r - 6 * Y)]

lemma profile_Cstar_bound (r Y : ℝ)
    (hprofile : r ^ 2 + 9 * Y ^ 2 ≤ 2) :
    Real.sqrt 2 * (r ^ 2 + 4 * r * Y) ≤ Cstar := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hcross := profile_cross_term_le r Y hprofile
  unfold Cstar
  nlinarith

/-- The first-mode bound `r ≤ 4/π` gives the displayed `Dstar` coefficient. -/
lemma profile_Dstar_bound (r : ℝ) (hr : 0 ≤ r)
    (hrpi : r ≤ 4 / Real.pi) : 2 * r ^ 2 ≤ Dstar := by
  have hsq : r ^ 2 ≤ (4 / Real.pi) ^ 2 := by nlinarith
  calc
    2 * r ^ 2 ≤ 2 * (4 / Real.pi) ^ 2 := by nlinarith
    _ = Dstar := by
      unfold Dstar
      field_simp [Real.pi_ne_zero]
      ring

/-- The profile tail estimate yields the quadratic resonance coefficient
before inserting the first-mode bound. -/
lemma resonance_coefficient_profile_bound (r Y : ℝ)
    (hprofile : r ^ 2 + 9 * Y ^ 2 ≤ 2) :
    r ^ 4 + 4 * r ^ 2 * Y ^ 2 ≤
      (5 / 9 : ℝ) * r ^ 4 + (8 / 9 : ℝ) * r ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg r)
    (sub_nonneg.mpr hprofile)]

/-- Exact derivation of the constant `Qstar` from the profile and
first-mode estimates. -/
lemma resonance_coefficient_le_Qstar (r Y : ℝ) (hr : 0 ≤ r)
    (hprofile : r ^ 2 + 9 * Y ^ 2 ≤ 2)
    (hrpi : r ≤ 4 / Real.pi) :
    r ^ 4 + 4 * r ^ 2 * Y ^ 2 ≤ Qstar := by
  have hx : r ^ 2 ≤ (4 / Real.pi) ^ 2 := by nlinarith
  have hmono :
      (5 / 9 : ℝ) * r ^ 4 + (8 / 9 : ℝ) * r ^ 2 ≤
        (5 / 9 : ℝ) * (4 / Real.pi) ^ 4 +
          (8 / 9 : ℝ) * (4 / Real.pi) ^ 2 := by
    have hfactor : 0 ≤
        ((4 / Real.pi) ^ 2 - r ^ 2) *
          ((5 / 9 : ℝ) * ((4 / Real.pi) ^ 2 + r ^ 2) + 8 / 9) := by
      exact mul_nonneg (sub_nonneg.mpr hx) (by positivity)
    nlinarith
  calc
    r ^ 4 + 4 * r ^ 2 * Y ^ 2 ≤
        (5 / 9 : ℝ) * r ^ 4 + (8 / 9 : ℝ) * r ^ 2 :=
      resonance_coefficient_profile_bound r Y hprofile
    _ ≤ (5 / 9 : ℝ) * (4 / Real.pi) ^ 4 +
        (8 / 9 : ℝ) * (4 / Real.pi) ^ 2 := hmono
    _ = Qstar := by
      unfold Qstar
      field_simp [Real.pi_ne_zero]
      ring

/-- Assembly of the quantitative first-variation estimate once the exact
correlation estimate has reduced it to the two profile terms. -/
lemma firstVariation_le_Cstar_Dstar
    (r Y delta L : ℝ) (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (hprofile : r ^ 2 + 9 * Y ^ 2 ≤ 2)
    (hrpi : r ≤ 4 / Real.pi)
    (hL : |L| ≤ 2 * r ^ 2 * delta +
      Real.sqrt 2 * (r ^ 2 + 4 * r * Y) * Real.sqrt delta) :
    |L| ≤ Cstar * Real.sqrt delta + Dstar * delta := by
  have hC := profile_Cstar_bound r Y hprofile
  have hD := profile_Dstar_bound r hr hrpi
  calc
    |L| ≤ 2 * r ^ 2 * delta +
        Real.sqrt 2 * (r ^ 2 + 4 * r * Y) * Real.sqrt delta := hL
    _ ≤ Dstar * delta + Cstar * Real.sqrt delta := by
      gcongr
    _ = Cstar * Real.sqrt delta + Dstar * delta := by ring

end

end GromovFilling
