import GromovFilling.FourierArea
import GromovFilling.Numerics
import GromovFilling.BoundaryActionSeries

/-!
# Concrete certificate conclusions

These theorems assemble the already formalized algebra at the end of the
two main arguments.  Their remaining hypotheses are stated at the precise
geometric interfaces: rowwise coverage plus a Jacobian budget in the
orientation-free case, and the calibrated Stokes/comass inequality in the
oriented case.
-/

open scoped BigOperators ENNReal

namespace GromovFilling

noncomputable section

/-- Rowwise coverage and the common Jacobian budget imply the concrete
finite universal certificate for the explicit Givens matrix. -/
theorem finite_universal_of_givens_coverage_budget
    (N : ℕ) (area : ℝ) (jacobianMass : Fin N → ℝ)
    (hcoverage : ∀ j : Fin N,
      mixedBoundaryArea (givensMatrix N) j ≤ jacobianMass j)
    (hbudget : (∑ j : Fin N, jacobianMass j) ≤ area) :
    finiteUniversalConstant N ≤ area := by
  apply finite_universal_certificate (givensMatrix N) area
  · exact givensMatrix_column_energy N
  · exact (Finset.sum_le_sum fun j _ ↦ hcoverage j).trans hbudget

/-- `ENNReal` form of the finite universal certificate, suited to
Lebesgue-area and Jacobian lintegrals. -/
theorem finite_universal_ennreal_of_givens_coverage_budget
    (N : ℕ) (area : ℝ≥0∞) (jacobianMass : Fin N → ℝ≥0∞)
    (hcoverage : ∀ j : Fin N,
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
        jacobianMass j)
    (hbudget : (∑ j : Fin N, jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  rw [← sum_mixedBoundaryArea (givensMatrix N)
    (givensMatrix_column_energy N)]
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun j _ ↦ mixedBoundaryArea_nonneg (givensMatrix N) j)]
  exact (Finset.sum_le_sum fun j _ ↦ hcoverage j).trans hbudget

/-- The same finite theorem with the boundary quantity presented as the
Green integral that occurs geometrically. -/
theorem finite_universal_of_green_coverage_budget
    (N : ℕ) (area : ℝ) (jacobianMass : Fin N → ℝ)
    (hcoverage : ∀ j : Fin N,
      fourierGreenArea
          (fun k : Fin N ↦ oddMode k)
          (fun k : Fin N ↦
            boundaryRadius (oddMode k) * givensMatrix N j k) ≤
        jacobianMass j)
    (hbudget : (∑ j : Fin N, jacobianMass j) ≤ area) :
    finiteUniversalConstant N ≤ area := by
  apply finite_universal_of_givens_coverage_budget N area jacobianMass
  · intro j
    rw [← givensBoundaryGreenArea_eq_mixedBoundaryArea]
    exact hcoverage j
  · exact hbudget

/-- Passing all concrete finite Givens certificates to the limit gives the
orientation-free constant `14 ζ(3) / π`. -/
theorem universal_of_givens_coverage_budget
    (area : ℝ)
    (hfinite : ∀ N : ℕ, ∃ jacobianMass : Fin N → ℝ,
      (∀ j : Fin N,
        mixedBoundaryArea (givensMatrix N) j ≤ jacobianMass j) ∧
      (∑ j : Fin N, jacobianMass j) ≤ area) :
    universalConstant ≤ area := by
  apply universal_bound_of_finite_certificates
  intro N
  obtain ⟨jacobianMass, hcoverage, hbudget⟩ := hfinite N
  exact finite_universal_of_givens_coverage_budget N area jacobianMass
    hcoverage hbudget

lemma Qstar_nonneg : 0 ≤ Qstar := by
  unfold Qstar
  positivity

lemma comassBound_pos_of_denominator {lam : ℝ}
    (hden : 0 < 1 - Dstar * lam) : 0 < comassBound lam := by
  unfold comassBound
  have hquot : 0 ≤ Cstar ^ 2 / (4 * (1 - Dstar * lam)) := by positivity
  nlinarith [Qstar_nonneg, sq_nonneg lam]

/-- The exact one-parameter oriented conclusion once Stokes and the global
comass estimate have supplied the calibration inequality. -/
theorem oriented_area_ge_nonlinearCertificate
    {area lam : ℝ} (_hlam_nonneg : 0 ≤ lam)
    (hlam : lam < Real.pi ^ 2 / 32)
    (hcalibration : boundaryAction lam ≤ comassBound lam * area) :
    nonlinearCertificate lam ≤ area := by
  have hden : 0 < 1 - Dstar * lam :=
    comass_denominator_pos_of_admissible hlam
  have hcomass : 0 < comassBound lam :=
    comassBound_pos_of_denominator hden
  unfold nonlinearCertificate
  rw [div_le_iff₀ hcomass]
  simpa [mul_comm] using hcalibration

/-- Once the oriented Stokes/comass estimate is available at `λ = 0.03`,
the exact rational numerical verification yields the advertised strict
decimal lower bound. -/
theorem oriented_area_gt_point_zero_three {area : ℝ}
    (hcalibration :
      boundaryAction (3 / 100) ≤ comassBound (3 / 100) * area) :
    (538982446 / 100000000 : ℝ) < area := by
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    exact oriented_area_ge_nonlinearCertificate (by norm_num)
      lambda_point_zero_three_admissible hcalibration
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

end

end GromovFilling
