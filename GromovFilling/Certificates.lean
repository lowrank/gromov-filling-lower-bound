import GromovFilling.FourierArea
import GromovFilling.GeometricClosedOneForm
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

/-- Finite `ENNReal` certificate with an explicit additive defect term carried through unchanged. -/
theorem finite_universal_ennreal_of_givens_coverage_budget_add
    (N : ℕ) (area defect : ℝ≥0∞) (jacobianMass : Fin N → ℝ≥0∞)
    (hcoverage : ∀ j : Fin N,
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
        jacobianMass j)
    (hbudget : (∑ j : Fin N, jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area := by
  have hfinite : ENNReal.ofReal (finiteUniversalConstant N) ≤ ∑ j : Fin N, jacobianMass j := by
    rw [← sum_mixedBoundaryArea (givensMatrix N)
      (givensMatrix_column_energy N)]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun j _ ↦ mixedBoundaryArea_nonneg (givensMatrix N) j)]
    exact Finset.sum_le_sum fun j _ ↦ hcoverage j
  have hstep : ENNReal.ofReal (finiteUniversalConstant N) + defect ≤
      (∑ j : Fin N, jacobianMass j) + defect := by
    simpa [add_comm] using add_le_add_right hfinite defect
  exact hstep.trans hbudget

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

/-- The exact universal certificate also yields a rigorous decimal lower
bound for the area. -/
theorem universal_area_gt_53567723441 {area : ℝ}
    (hcertificate : universalConstant ≤ area) :
    (53567723441 / 10000000000 : ℝ) < area :=
  universalConstant_gt_53567723441.trans_le hcertificate

/-- `ENNReal` form of the infinite Givens certificate, suited to
measure-theoretic area budgets. -/
theorem universal_ennreal_of_givens_coverage_budget
    (area : ℝ≥0∞)
    (hfinite : ∀ N : ℕ, ∃ jacobianMass : Fin N → ℝ≥0∞,
      (∀ j : Fin N,
        ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
          jacobianMass j) ∧
      (∑ j : Fin N, jacobianMass j) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  obtain ⟨jacobianMass, hcoverage, hbudget⟩ := hfinite N
  exact finite_universal_ennreal_of_givens_coverage_budget
    N area jacobianMass hcoverage hbudget

/-- Infinite `ENNReal` Givens certificate with a common additive defect
carried through unchanged. -/
theorem universal_ennreal_of_givens_coverage_budget_add
    (area defect : ℝ≥0∞)
    (hfinite : ∀ N : ℕ, ∃ jacobianMass : Fin N → ℝ≥0∞,
      (∀ j : Fin N,
        ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
          jacobianMass j) ∧
      (∑ j : Fin N, jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  obtain ⟨jacobianMass, hcoverage, hbudget⟩ := hfinite N
  exact finite_universal_ennreal_of_givens_coverage_budget_add
    N area defect jacobianMass hcoverage hbudget

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

/-- Certificate-level oriented conclusion from the bundled square-homeomorphism
plus glued-strip calibrated Stokes bound. This packages every ingredient
except the final identification of `boundaryAction` with the chosen boundary
integral. -/
theorem oriented_area_ge_nonlinearCertificate_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_boundaryIntegral
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {lam area : ℝ} {J : ℝ × ℝ → ℝ}
    (_hlam_nonneg : 0 ≤ lam)
    (hlam : lam < Real.pi ^ 2 / 32)
    (hboundaryAction :
      boundaryAction lam ≤ ‖closedUnitSquareBoundaryIntegral
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω‖)
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand
          (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x‖ ≤
        comassBound lam * J x)
    (harea : ∫ x in Set.Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    nonlinearCertificate lam ≤ area := by
  have hden : 0 < 1 - Dstar * lam :=
    comass_denominator_pos_of_admissible hlam
  have hcomass : 0 < comassBound lam :=
    comassBound_pos_of_denominator hden
  have hcalibration : boundaryAction lam ≤ comassBound lam * area :=
    hboundaryAction.trans
      (norm_curveIntegral_le_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
        (D := D) (Fmap := Fmap) hω hcontdiff hcomass.le hintegrand hJ hbound harea)
  exact oriented_area_ge_nonlinearCertificate (lam := lam) (area := area)
    (by assumption) hlam hcalibration

/-- Certificate-level oriented conclusion from the direct square-homeomorphism
calibrated Stokes bound. This packages every ingredient except the final
identification of `boundaryAction` with the chosen boundary integral. -/
theorem oriented_area_ge_nonlinearCertificate_of_closedUnitSquare_homeomorph_cylinderStripGlued_boundaryIntegral
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {lam area : ℝ} {J : ℝ × ℝ → ℝ}
    (_hlam_nonneg : 0 ≤ lam)
    (hlam : lam < Real.pi ^ 2 / 32)
    (hboundaryAction :
      boundaryAction lam ≤ ‖closedUnitSquareBoundaryIntegral (Fmap.comp ⟨e, e.continuous_toFun⟩) ω‖)
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩))
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x‖ ≤
        comassBound lam * J x)
    (harea : ∫ x in Set.Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    nonlinearCertificate lam ≤ area := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitSquareBoundary }
  simpa [D] using
    (oriented_area_ge_nonlinearCertificate_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_boundaryIntegral
      (D := D) (Fmap := Fmap) (lam := lam) (J := J)
      (by assumption) hlam hboundaryAction hω hcontdiff hintegrand hJ hbound harea)

/-- The point-`0.03` oriented decimal lower bound from the bundled square-
homeomorphism-plus-glued-strip calibrated Stokes bound. -/
theorem oriented_area_gt_point_zero_three_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_boundaryIntegral
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {area : ℝ} {J : ℝ × ℝ → ℝ}
    (hboundaryAction :
      boundaryAction (3 / 100) ≤ ‖closedUnitSquareBoundaryIntegral
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω‖)
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand
          (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x‖ ≤
        comassBound (3 / 100) * J x)
    (harea : ∫ x in Set.Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    (538982446 / 100000000 : ℝ) < area := by
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    exact
      oriented_area_ge_nonlinearCertificate_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_boundaryIntegral
        (D := D) (Fmap := Fmap) (lam := 3 / 100) (J := J)
        (by norm_num) lambda_point_zero_three_admissible
        hboundaryAction hω hcontdiff hintegrand hJ hbound harea
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

/-- The point-`0.03` oriented decimal lower bound from the direct square-homeomorphism
calibrated Stokes bound. -/
theorem oriented_area_gt_point_zero_three_of_closedUnitSquare_homeomorph_cylinderStripGlued_boundaryIntegral
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {area : ℝ} {J : ℝ × ℝ → ℝ}
    (hboundaryAction :
      boundaryAction (3 / 100) ≤ ‖closedUnitSquareBoundaryIntegral (Fmap.comp ⟨e, e.continuous_toFun⟩) ω‖)
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩))
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x‖ ≤
        comassBound (3 / 100) * J x)
    (harea : ∫ x in Set.Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    (538982446 / 100000000 : ℝ) < area := by
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    exact oriented_area_ge_nonlinearCertificate_of_closedUnitSquare_homeomorph_cylinderStripGlued_boundaryIntegral
      (e := e) (hboundaryMap := hboundaryMap) (Fmap := Fmap)
      (lam := 3 / 100) (J := J) (by norm_num) lambda_point_zero_three_admissible
      hboundaryAction hω hcontdiff hintegrand hJ hbound harea
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

/-- Uniform calibration bounds on every finite resonant Green truncation imply
the full oriented certificate after passing to the limit. -/
theorem oriented_area_ge_nonlinearCertificate_of_resonantGreenArea_bounds
    {area lam : ℝ} (_hlam_nonneg : 0 ≤ lam)
    (hlam : lam < Real.pi ^ 2 / 32)
    (hfinite : ∀ N : ℕ,
      fourierGreenArea
        (fun k : Fin N ↦ oddMode k)
        (fun k : Fin N ↦ resonantBoundaryCoefficient lam k) ≤
          comassBound lam * area) :
    nonlinearCertificate lam ≤ area := by
  have hcalibration : boundaryAction lam ≤ comassBound lam * area := by
    have hlim : Filter.Tendsto
        (fun N : ℕ ↦
          fourierGreenArea
            (fun k : Fin N ↦ oddMode k)
            (fun k : Fin N ↦ resonantBoundaryCoefficient lam k))
        Filter.atTop (nhds (boundaryAction lam)) := by
      simpa [boundaryActionSeries_eq lam] using
        tendsto_fourierGreenArea_resonantBoundaryCoefficient lam
    have hconst : Filter.Tendsto
        (fun _ : ℕ ↦ comassBound lam * area)
        Filter.atTop (nhds (comassBound lam * area)) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hlim hconst hfinite
  exact oriented_area_ge_nonlinearCertificate
    (lam := lam) (area := area) (by assumption) hlam hcalibration

/-- The point-`0.03` oriented decimal lower bound also follows from uniform
bounds on all finite resonant Green truncations. -/
theorem oriented_area_gt_point_zero_three_of_resonantGreenArea_bounds
    {area : ℝ}
    (hfinite : ∀ N : ℕ,
      fourierGreenArea
        (fun k : Fin N ↦ oddMode k)
        (fun k : Fin N ↦ resonantBoundaryCoefficient (3 / 100) k) ≤
          comassBound (3 / 100) * area) :
    (538982446 / 100000000 : ℝ) < area := by
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    exact oriented_area_ge_nonlinearCertificate_of_resonantGreenArea_bounds
      (area := area) (lam := 3 / 100) (by norm_num)
      lambda_point_zero_three_admissible hfinite
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

/-- The exact oriented conclusion also accepts the unevaluated odd-mode boundary
series directly; Proposition 9.1 identifies it with `boundaryAction`. -/
theorem oriented_area_ge_nonlinearCertificate_of_boundaryActionSeries
    {area lam : ℝ} (_hlam_nonneg : 0 ≤ lam)
    (hlam : lam < Real.pi ^ 2 / 32)
    (hcalibration : boundaryActionSeries lam ≤ comassBound lam * area) :
    nonlinearCertificate lam ≤ area := by
  rw [boundaryActionSeries_eq] at hcalibration
  exact oriented_area_ge_nonlinearCertificate (lam := lam) (area := area)
    (by assumption) hlam hcalibration

/-- The point-`0.03` oriented decimal lower bound likewise follows directly
from the unevaluated odd-mode boundary series. -/
theorem oriented_area_gt_point_zero_three_of_boundaryActionSeries {area : ℝ}
    (hcalibration :
      boundaryActionSeries (3 / 100) ≤ comassBound (3 / 100) * area) :
    (538982446 / 100000000 : ℝ) < area := by
  rw [boundaryActionSeries_eq] at hcalibration
  have hcertificate : nonlinearCertificate (3 / 100) ≤ area := by
    exact oriented_area_ge_nonlinearCertificate (by norm_num)
      lambda_point_zero_three_admissible hcalibration
  exact nonlinearCertificate_point_zero_three_gt.trans_le hcertificate

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
