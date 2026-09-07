import GromovFilling.Oriented

/-!
# The sharper first-variation constant

Section 4 of the revised manuscript removes the first component of the mixed
correlation. Its remaining profile tail starts at frequency five. These
scalar estimates keep the earlier certificate available under its existing
names.
-/

namespace GromovFilling

noncomputable section

/-- The first-variation coefficient after the frequency-three cancellation. -/
def sharpenedCstar : ℝ :=
  Real.sqrt 2 * (16 / Real.pi ^ 2 +
    8 / (5 * Real.pi) * Real.sqrt (2 - 16 / Real.pi ^ 2))

/-- The revised all-parameter comass bound. -/
def sharpenedComassBound (lam : ℝ) : ℝ :=
  1 + lam ^ 2 * (Qstar + sharpenedCstar ^ 2 / (4 * (1 - Dstar * lam)))

/-- The revised oriented area certificate; the boundary action is unchanged. -/
def sharpenedNonlinearCertificate (lam : ℝ) : ℝ :=
  boundaryAction lam / sharpenedComassBound lam

/-- A supporting quadratic form bounds the ellipse with a cap on its first
coordinate. This avoids differentiating the equivalent one-variable formula. -/
lemma capped_profile_cross_term_le (r Z R s : ℝ)
    (hR : 0 < R) (hs : 0 < s)
    (hsq : s ^ 2 = 2 - R ^ 2)
    (hslope : 0 ≤ 5 * R * s + 2 - 2 * R ^ 2)
    (hcap : r ^ 2 ≤ R ^ 2)
    (hprofile : r ^ 2 + 25 * Z ^ 2 ≤ 2) :
    r ^ 2 + 2 * r * Z ≤ R ^ 2 + 2 * R * s / 5 := by
  have henergy := mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hprofile)
  have hsupport := mul_nonneg (sub_nonneg.mpr hcap) hslope
  have hyoung := sq_nonneg (s * r - 5 * R * Z)
  have hsq_r : s ^ 2 * r ^ 2 = (2 - R ^ 2) * r ^ 2 := by rw [hsq]
  have hsq_R : R ^ 2 * s ^ 2 = R ^ 2 * (2 - R ^ 2) := by rw [hsq]
  apply (mul_le_mul_right (by positivity : 0 < 5 * R * s)).mp
  nlinarith only [henergy, hsupport, hyoung, hsq_r, hsq_R]

/-- The capped weight-25 profile estimate gives the revised exact constant. -/
lemma profile_sharpenedCstar_bound (r Z : ℝ)
    (hr : 0 ≤ r) (hrpi : r ≤ 4 / Real.pi)
    (hprofile : r ^ 2 + 25 * Z ^ 2 ≤ 2) :
    Real.sqrt 2 * (r ^ 2 + 2 * r * Z) ≤ sharpenedCstar := by
  let R : ℝ := 4 / Real.pi
  let s : ℝ := Real.sqrt (2 - R ^ 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRlo : 1 ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have hRhi : R ≤ 4 / 3 := by
    dsimp [R]
    gcongr
    exact Real.pi_gt_three.le
  have hR2 : R ^ 2 ≤ 16 / 9 := by nlinarith
  have hsarg : 0 ≤ 2 - R ^ 2 := by linarith
  have hsq : s ^ 2 = 2 - R ^ 2 := Real.sq_sqrt hsarg
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hslo : 1 / 3 ≤ s := by nlinarith
  have hs : 0 < s := by linarith
  have hRs : 1 / 3 ≤ R * s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRlo) hs0]
  have hslope : 0 ≤ 5 * R * s + 2 - 2 * R ^ 2 := by linarith
  have hcap : r ^ 2 ≤ R ^ 2 := by change r ≤ R at hrpi; nlinarith
  have hcross := capped_profile_cross_term_le r Z R s hR hs hsq hslope hcap hprofile
  have hRrewrite : R ^ 2 = 16 / Real.pi ^ 2 := by dsimp [R]; ring
  calc
    Real.sqrt 2 * (r ^ 2 + 2 * r * Z) ≤
        Real.sqrt 2 * (R ^ 2 + 2 * R * s / 5) := by gcongr
    _ = sharpenedCstar := by
      unfold sharpenedCstar
      dsimp only [s]
      rw [hRrewrite]
      dsimp [R]
      ring

/-- Assembly of the revised first-variation estimate from the cancelled
mixed correlation and the original shift-correlation estimate. -/
lemma firstVariation_le_sharpenedCstar_Dstar
    (r Z delta L : ℝ) (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (hprofile : r ^ 2 + 25 * Z ^ 2 ≤ 2)
    (hrpi : r ≤ 4 / Real.pi)
    (hL : |L| ≤ 2 * r ^ 2 * delta +
      Real.sqrt 2 * (r ^ 2 + 2 * r * Z) * Real.sqrt delta) :
    |L| ≤ sharpenedCstar * Real.sqrt delta + Dstar * delta := by
  have hC := profile_sharpenedCstar_bound r Z hr hrpi hprofile
  have hD := profile_Dstar_bound r hr hrpi
  calc
    |L| ≤ 2 * r ^ 2 * delta +
        Real.sqrt 2 * (r ^ 2 + 2 * r * Z) * Real.sqrt delta := hL
    _ ≤ Dstar * delta + sharpenedCstar * Real.sqrt delta := by gcongr
    _ = sharpenedCstar * Real.sqrt delta + Dstar * delta := by ring

lemma sharpenedComassBound_pos {lam : ℝ}
    (hlam : lam < Real.pi ^ 2 / 32) : 0 < sharpenedComassBound lam := by
  have hden := comass_denominator_pos_of_admissible hlam
  have hQ : 0 ≤ Qstar := by unfold Qstar; positivity
  unfold sharpenedComassBound
  positivity

/-- The sharpened scalar area deduction, with its calibration input explicit. -/
theorem area_ge_sharpenedNonlinearCertificate {area lam : ℝ}
    (hlam : lam < Real.pi ^ 2 / 32)
    (hcalibration : boundaryAction lam ≤ sharpenedComassBound lam * area) :
    sharpenedNonlinearCertificate lam ≤ area := by
  rw [sharpenedNonlinearCertificate, div_le_iff₀ (sharpenedComassBound_pos hlam)]
  simpa only [mul_comm] using hcalibration

lemma lambda_one_div_twenty_five_admissible :
    (1 / 25 : ℝ) < Real.pi ^ 2 / 32 := by
  nlinarith [Real.pi_gt_three, Real.pi_pos]

end

end GromovFilling

#print axioms GromovFilling.profile_sharpenedCstar_bound
#print axioms GromovFilling.firstVariation_le_sharpenedCstar_Dstar
#print axioms GromovFilling.area_ge_sharpenedNonlinearCertificate
