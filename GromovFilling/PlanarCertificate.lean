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

open unitInterval

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

/-- The finite orientation-free Fourier certificate for complex-plane
domains under the exact topological interface: an odd boundary-degree
obstruction and the global Jacobian budget. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
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
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
      j boundary hobstruction (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface.  This is the certificate-level handoff for future arbitrary
surface constructions. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    N area boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    G hG hboundary K hGLipschitz hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary extends continuously across the standard closed disk. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
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
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
      j boundary F hF hboundaryExtension (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism and explicit checkerboard cylinder-strip data. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
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
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    N area boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    G hG hboundary K hGLipschitz hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
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
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
      j boundary e hboundaryHomeomorph (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
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
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
      j boundary e hboundaryHomeomorph (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The same finite planar certificate follows directly from a nullhomotopy
of the boundary loop. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
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
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
      j boundary center F hF0 hF1 (G j) (hG j) (hboundary j) (hGLipschitz j)
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

/-- Planar Lemma 5.4 for the genuine metric distance-profile map under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map under the exact topological interface: an odd boundary-degree obstruction
on the planar boundary. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary') :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    (givensMetricFourierMap_lipschitzWith hboundary' N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary') :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    (givensMetricFourierMap_lipschitzWith hboundary' N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary extends continuously across the standard closed disk. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied by explicit
checkerboard cylinder-strip data. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by
a homeomorphism and the odd boundary-degree obstruction is supplied by
explicit checkerboard cylinder-strip data. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary loop is nullhomotopic in the source plane. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric
Fourier map.  It produces an open connected neighborhood of the origin whose
volume is controlled by the global complex Jacobian integral. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary extends continuously across the standard closed disk. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary loop is nullhomotopic in the source plane. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_nullhomotopy
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 (givensMetricFourierMap boundary N j)
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

/-- The sharp pointwise Jacobian defect bound integrates to an additive area budget on any measurable planar domain. -/
theorem sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (s : Set ℂ) (hs : MeasurableSet s) :
    (∑ j : Fin N, ∫⁻ x in s, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
        ∫⁻ x in s, ENNReal.ofReal
          (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤
        volume s := by
  refine sum_lintegral_abs_det_fderiv_add_lintegral_ofReal_defect_restrict_le_volume
    (fun j ↦ givensMetricFourierMap boundary N j) s hs
    (distanceSlackDerivativeEnergyDefect boundary)
    (measurable_distanceSlackDerivativeEnergyDefect hboundary)
    (distanceSlackDerivativeEnergyDefect_nonneg boundary) ?_
  exact ae_restrict_of_ae
    (ae_sum_abs_det_fderiv_givensMetricFourierMap_add_distanceSlackDerivativeEnergyDefect_le_one
      hboundary N)

/-- Finite slack-refined planar certificate derived internally from the sharp Jacobian defect budget. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_coordinateEnergy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
    j boundary hboundary hfine

/-- Infinite slack-refined planar certificate derived from the finite additive
slack-defect certificates. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_coordinateEnergy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_coordinateEnergy
      N area boundary hboundary hfine harea

/-- Finite slack-refined planar certificate under the exact topological
interface: an odd boundary-degree obstruction on the planar boundary. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction hboundary

/-- Infinite slack-refined planar certificate under the exact topological
interface: an odd boundary-degree obstruction on the planar boundary. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
      N area boundary hobstruction hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with a compact source carrying the quotient-friendly directed abstract
arbitrarily-fine polygonal-model interface. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary' hboundary' N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph hmodels hboundary'

/-- Infinite slack-refined planar certificate when the boundary is identified
with a compact source carrying the quotient-friendly directed abstract
arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      N area e hboundaryHomeomorph hmodels hboundary' harea

/-- Finite slack-refined planar certificate when the boundary extends across
the standard closed disk. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension hboundary

/-- Infinite slack-refined planar certificate when the boundary extends across
the standard closed disk. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_extension
      N area boundary F hF hboundaryExtension hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph hboundary

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph hboundary

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
      N area boundary e hboundaryHomeomorph hboundary harea

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary harea

/-- Finite slack-refined planar certificate when the boundary loop is
nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 hboundary

/-- Infinite slack-refined planar certificate when the boundary loop is
nullhomotopic in the source plane. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_nullhomotopy
      N area boundary center F hF0 hF1 hboundary harea

/-- The complete finite planar certificate for the actual metric Fourier
family under the exact topological interface: an odd boundary-degree
obstruction on the planar boundary. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
        j boundary hobstruction hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family
under the exact topological interface: an odd boundary-degree obstruction on
 the planar boundary. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    N area boundary hobstruction hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
        j e hboundaryHomeomorph hmodels hboundary'
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph hmodels hboundary' (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary extends continuously across the standard closed
 disk. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
        j boundary F hF hboundaryExtension hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary extends continuously across the standard closed disk. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    N area boundary F hF hboundaryExtension hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism and the odd boundary-degree obstruction is supplied by
explicit checkerboard cylinder-strip data. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
        j boundary e hboundaryHomeomorph hmodels hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with the standard closed-disk boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied by explicit
checkerboard cylinder-strip data. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_cylinderStrip_data
    N area boundary e hboundaryHomeomorph hmodels hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
        j boundary e hboundaryHomeomorph hboundary
  · exact hbudget

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
        j boundary e hboundaryHomeomorph hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary is identified with the standard closed-disk boundary by a
 homeomorphism. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary is identified with the standard closed-disk boundary by a
 homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary loop is nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
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
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
        j boundary center F hF0 hF1 hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary loop is nullhomotopic in the source plane. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    N area boundary center F hF0 hF1 hboundary (hbudget N)

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

/-- The finite planar certificate with coordinate-energy budget under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
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
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    N (volume (Set.univ : Set ℂ)) boundary hobstruction hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_odd_boundary_degree_obstruction
      N area boundary hobstruction hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N (volume (Set.univ : Set ℂ)) e hboundaryHomeomorph hmodels hboundary' ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary' hboundary' N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      N area e hboundaryHomeomorph hmodels hboundary' (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed disk. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    N (volume (Set.univ : Set ℂ)) boundary F hF hboundaryExtension hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed disk. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_extension
      N area boundary F hF hboundaryExtension hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    N (volume (Set.univ : Set ℂ)) boundary e hboundaryHomeomorph hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
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
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    N (volume (Set.univ : Set ℂ)) boundary e hboundaryHomeomorph hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary loop is nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
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
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    N (volume (Set.univ : Set ℂ)) boundary center F hF0 hF1 hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary loop is nullhomotopic in the source plane. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_nullhomotopy
      N area boundary center F hF0 hF1 hboundary (hbudget N) harea

end

end GromovFilling
