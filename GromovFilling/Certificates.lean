import GromovFilling.FourierArea
import GromovFilling.Numerics

/-!
# Concrete certificate conclusions

These theorems assemble the already formalized algebra at the end of the
two main arguments.  Their remaining hypotheses are stated at the precise
geometric interfaces: rowwise coverage plus a Jacobian budget in the
orientation-free case, and the calibrated Stokes/comass inequality in the
oriented case.
-/

open scoped BigOperators

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

/-- Once the oriented Stokes/comass estimate is available at `λ = 0.03`,
the exact rational numerical verification yields the advertised strict
decimal lower bound. -/
theorem oriented_area_gt_point_zero_three {area : ℝ}
    (hcalibration :
      boundaryAction (3 / 100) ≤ comassBound (3 / 100) * area) :
    (538982446 / 100000000 : ℝ) < area := by
  have hden : 0 < 1 - Dstar * (3 / 100 : ℝ) :=
    comass_denominator_pos_of_admissible lambda_point_zero_three_admissible
  have hcomass : 0 < comassBound (3 / 100) :=
    comassBound_pos_of_denominator hden
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    unfold nonlinearCertificate
    rw [div_le_iff₀ hcomass]
    simpa [mul_comm] using hcalibration
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

end

end GromovFilling
