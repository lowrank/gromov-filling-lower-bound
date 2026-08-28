import GromovFilling.ProfileFourier
import GromovFilling.SurfaceCoverage

/-!
# Coverage for the metric Fourier maps

This removes the abstract boundary-extension inputs from the topological
half of Lemma 5.4: the maps here are the actual Givens mixtures constructed
from the filling's distance functions, and their Jordan boundary values
were proved in `ProfileFourier`.
-/

namespace GromovFilling

noncomputable section

open unitInterval

/-- The origin component of every mixed Jordan curve is covered by the
actual metric Fourier map. -/
theorem givensMetricFourierMap_origin_component_subset_range
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N) :
    connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 ⊆
      Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_origin_component_subset_range_of_fine_models
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- If the boundary loop is nullhomotopic in the source space, the genuine
metric Fourier map covers the Jordan region at the origin directly from that
nullhomotopy, with no polygonal-model hypothesis. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_nullhomotopy
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_nullhomotopy
    j center F hF0 hF1 (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- The separation-free metric coverage conclusion also follows directly from
nullhomotopy of the boundary loop. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_nullhomotopy
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_nullhomotopy
    j center F hF0 hF1 (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- The actual metric Fourier map covers the Jordan region containing the
origin. -/
theorem givensMetricFourierMap_jordan_region_subset_range
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_fine_models
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- Separation-free form: the bounded region and its coverage are produced
internally for the genuine metric Fourier map. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_fine_models
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- Compact-domain version in which a map-independent arbitrarily fine
polygonal structure supplies the fine model by uniform continuity. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_arbitrarily_fine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_arbitrarily_fine_models
    j boundary hmodels (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- The genuine metric Fourier map also inherits the same coverage conclusion
 directly from the variable-face-size directed interface. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_abstractVariableDirectedArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_abstractVariableDirectedArbitrarilyFine
    j boundary hmodels (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- Compact-domain coverage for the genuine metric Fourier map also follows
from a boundary-respecting homeomorphism to any compact source carrying the
weaker directed abstract arbitrarily-fine polygonal-model interface.  This is
the form directly usable once a disk or surface cell-decomposition theorem is
available on a model domain. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary' N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    hpartition hzero

/-- Compact-domain coverage for the genuine metric Fourier map also follows
from a boundary-respecting homeomorphism to any compact source carrying
arbitrarily fine polygonal models.  This is the form directly usable once a
disk or surface triangulation theorem is available on a model domain. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_homeomorph_arbitrarily_fine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary' N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_homeomorph_arbitrarily_fine_models
    j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    hpartition hzero

/-- If the boundary extends continuously across the standard closed disk, the
genuine metric Fourier map covers the Jordan region at the origin directly from
the closed-disk obstruction, with no polygonal-model hypothesis. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_closedUnitDisk_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (F : ClosedUnitDisk → Y) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_closedUnitDisk_extension
    j F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- If the boundary extends continuously across the standard closed disk, the
separation-free coverage conclusion for the genuine metric Fourier map follows
directly from the closed-disk obstruction. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_closedUnitDisk_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (F : ClosedUnitDisk → Y) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_closedUnitDisk_extension
    j F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- If the boundary is identified with the standard closed-disk boundary by a
homeomorphism, the explicit directed disk polygonal-model construction already
supplies the needed coverage interface for the genuine metric Fourier map. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_closedUnitDisk_homeomorph
    j e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- Separation-free disk-homeomorphic coverage for the genuine metric Fourier
map also follows from the explicit directed disk polygonal-model interface. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_closedUnitDisk_homeomorph
    j e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- If the boundary is identified with the standard closed-disk boundary by a
homeomorphism, explicit checkerboard cylinder-strip data already supplies the
needed odd-degree obstruction, so the genuine metric Fourier map covers the
Jordan region at the origin without any extra topological hypothesis. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
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
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_closedUnitDisk_homeomorph_cylinderStrip_data
    j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- Separation-free coverage for the genuine metric Fourier map also follows
from explicit checkerboard cylinder-strip data transported across a
boundary-respecting closed-disk homeomorphism. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
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
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_closedUnitDisk_homeomorph_cylinderStrip_data
    j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- If the boundary is identified with the standard closed-disk boundary by a
homeomorphism, the genuine metric Fourier map covers the Jordan region at the
origin directly from the closed-disk obstruction, with no polygonal-model
hypothesis. -/
theorem givensMetricFourierMap_jordan_region_subset_range_of_closedUnitDisk_homeomorph_direct
    {Y : Type*} [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact givensBoundaryCurve_jordan_region_subset_range_of_closedUnitDisk_homeomorph_direct
    j e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    hpartition hzero

/-- Separation-free closed-disk-homeomorphic coverage for the genuine metric
Fourier map, using the direct odd-degree obstruction on the disk model
rather than a polygonal-model hypothesis. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_closedUnitDisk_homeomorph_direct
    {Y : Type*} [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact exists_givensBoundaryCurve_bounded_region_subset_range_of_closedUnitDisk_homeomorph_direct
    j e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)

/-- Separation-free coverage for the genuine metric Fourier map also follows
 directly from the variable-face-size directed interface. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_abstractVariableDirectedArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary N j) := by
  exact
    exists_givensBoundaryCurve_bounded_region_subset_range_of_abstractVariableDirectedArbitrarilyFine
      j boundary hmodels (givensMetricFourierMap boundary N j)
      (continuous_givensMetricFourierMap hboundary N j)
      (givensMetricFourierMap_on_boundary hboundary j)

/-- Separation-free compact-domain coverage for the genuine metric Fourier map
also transfers from a boundary-respecting homeomorphism to any compact source
carrying the directed abstract arbitrarily-fine polygonal-model interface. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary' N j) := by
  exact
    exists_givensBoundaryCurve_bounded_region_subset_range_of_homeomorph_abstractVariableDirectedArbitrarilyFine
      j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary' N j)
      (continuous_givensMetricFourierMap hboundary' N j)
      (givensMetricFourierMap_on_boundary hboundary' j)

/-- Separation-free compact-domain coverage for the genuine metric Fourier map
also transfers from a boundary-respecting homeomorphism to any compact source
with arbitrarily fine polygonal models. -/
theorem exists_givensMetricFourierMap_bounded_region_subset_range_of_homeomorph_arbitrarily_fine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    {N : ℕ} (j : Fin N) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range (givensMetricFourierMap boundary' N j) := by
  exact
    exists_givensBoundaryCurve_bounded_region_subset_range_of_homeomorph_arbitrarily_fine_models
      j e hboundaryHomeomorph hmodels (givensMetricFourierMap boundary' N j)
      (continuous_givensMetricFourierMap hboundary' N j)
      (givensMetricFourierMap_on_boundary hboundary' j)

end

end GromovFilling
