import GromovFilling.Certificates
import GromovFilling.ComplexAreaFormula
import GromovFilling.ProfileFourier

/-!
# A complete finite certificate for planar filling domains

For a domain modeled by the complex plane, the Jordan coverage theorem,
the exact enclosed-area calculation, and the Lipschitz area formula combine
without any remaining coverage hypothesis.  The only final input is the
common Jacobian budget for the finite family of mixed maps.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace GromovFilling

noncomputable section

/-- The finite orientation-free Fourier certificate for complex-plane
domains, with every rowwise area inequality discharged internally. -/
theorem finite_universal_ennreal_of_complex_planar_maps
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian
      j boundary hfine (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- Planar Lemma 5.4 for the genuine metric distance-profile map.  All
boundary, continuity, and Lipschitz inputs are discharged internally. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- The complete finite planar certificate for the actual metric Fourier
family.  Its sole analytic input is their common Jacobian budget. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
        j boundary hboundary hfine
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family.
The hypothesis is now exactly the common Jacobian budget, uniformly over
all finite truncations. -/
theorem universal_ennreal_of_metric_complex_planar_maps
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map
    N area boundary hboundary hfine (hbudget N)

/-- Once the Bessel estimate is known for the unmixed genuine Fourier
coordinates, full Givens orthogonality and Rademacher automatically give
the integrated unit Jacobian budget on every measurable planar set. -/
theorem sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (s : Set ℂ) (hs : MeasurableSet s)
    (henergy : ∀ᵐ x ∂volume.restrict s,
      (∑ k : Fin N, complexDerivativeEnergy
        (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2) :
    (∑ j : Fin N, ∫⁻ x in s, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        volume s := by
  have hmixed : ∀ᵐ x ∂volume.restrict s,
      (∑ j : Fin N, complexDerivativeEnergy
        (fderiv ℝ (givensMetricFourierMap boundary N j) x)) ≤ 2 := by
    have hsum : ∀ᵐ x ∂volume.restrict s,
        (∑ j : Fin N, complexDerivativeEnergy
          (fderiv ℝ (givensMetricFourierMap boundary N j) x)) =
          ∑ k : Fin N, complexDerivativeEnergy
            (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x) :=
      ae_restrict_of_ae
        (ae_sum_complexDerivativeEnergy_fderiv_givensMetricFourierMap
          hboundary N)
    filter_upwards [hsum, henergy] with x hsumx hex
    rw [hsumx]
    exact hex
  exact sum_lintegral_abs_det_fderiv_restrict_le_volume
    (fun j ↦ givensMetricFourierMap boundary N j) s hs hmixed

/-- The finite planar certificate for the actual metric Fourier family with
the Jacobian budget derived internally from the coordinate-energy bound. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map
    N (volume (Set.univ : Set ℂ)) boundary hboundary hfine ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar conclusion for the actual metric Fourier family,
with each finite Jacobian budget derived internally from the corresponding
coordinate-energy bound. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy
    N area boundary hboundary hfine (hbudget N) harea

end

end GromovFilling
