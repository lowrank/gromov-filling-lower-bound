import GromovFilling.FinePolygonalModel
import GromovFilling.JordanBoundary

/-!
# Coverage from the odd boundary-degree obstruction

This file turns the topological obstruction in Lemma 5.4 into its planar
coverage conclusion.  It also specializes the conclusion to the bounded
nonzero-degree component of each mixed Givens boundary curve.
-/

namespace GromovFilling

noncomputable section

/-- If the radial projection of the boundary around `y` has odd degree,
the mod-two boundary obstruction forces `y` into the image of the planar
map.  This is the coverage implication in Lemma 5.4, separated from the
surface-triangulation theorem that supplies the obstruction. -/
theorem mem_range_of_odd_boundary_radial_degree
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G) (y : ℂ)
    (hboundaryAvoid : ∀ t, G (boundary t) ≠ y)
    (degree : ℤ)
    (hdegree : HasComplexCircleDegree
      (radialMap (G ∘ boundary) y hboundaryAvoid) degree)
    (hodd : Odd degree) : y ∈ Set.range G := by
  by_contra hy
  have havoid : ∀ x, G x ≠ y := by
    intro x hx
    exact hy ⟨x, hx⟩
  apply hobstruction (radialMapAddCircle G y havoid)
    (continuous_radialMapAddCircle G y havoid hG) degree
  · unfold HasComplexCircleDegree at hdegree
    convert hdegree using 1
  · exact hodd

/-- Coverage stated directly from the bundled fine-polygonal-model
property, with the abstract obstruction discharged internally. -/
theorem mem_range_of_fine_polygonal_models_odd_radial_degree
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X)
    (hfine : HasFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G) (y : ℂ)
    (hboundaryAvoid : ∀ t, G (boundary t) ≠ y)
    (degree : ℤ)
    (hdegree : HasComplexCircleDegree
      (radialMap (G ∘ boundary) y hboundaryAvoid) degree)
    (hodd : Odd degree) : y ∈ Set.range G :=
  mem_range_of_odd_boundary_radial_degree boundary
    (hasOddBoundaryDegreeObstruction_of_finePolygonalModels hfine)
    G hG y hboundaryAvoid degree hdegree hodd

/-- An odd radial degree at one point covers its entire connected
component in the boundary-curve complement.  Degree constancy propagates
the odd degree across the component, and the boundary obstruction then
forces each point into the extension image. -/
theorem complement_component_subset_range_of_odd_degree
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G)
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (hboundary : ∀ t, G (boundary t) = curve t)
    (y₀ : ℂ) (havoid₀ : ∀ t, curve t ≠ y₀)
    (degree : ℤ)
    (hdegree : HasComplexCircleDegree
      (radialMap curve y₀ havoid₀) degree)
    (hodd : Odd degree) :
    connectedComponentIn (Set.range curve)ᶜ y₀ ⊆ Set.range G := by
  intro y hy
  let hcurveAvoid : ∀ t, curve t ≠ y :=
    curve_ne_of_mem_complement_component curve y₀ y hy
  have hboundaryAvoid : ∀ t, G (boundary t) ≠ y := by
    intro t
    rw [hboundary t]
    exact hcurveAvoid t
  apply mem_range_of_odd_boundary_radial_degree boundary hobstruction
    G hG y hboundaryAvoid degree
  · have hyDegree := radialMap_degree_constant_on_complement_component
      curve hcurve y₀ havoid₀ hdegree y hy
    convert hyDegree using 1
    funext t
    apply Subtype.ext
    simp only [radialMap, radialProjection, Function.comp_apply,
      hboundary]
  · exact hodd

/-- For a mixed Givens boundary curve, every point in the origin
component of the complement lies in the image of any continuous extension
on a domain with the odd boundary-degree obstruction. -/
theorem givensBoundaryCurve_origin_component_subset_range
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t) :
    connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 ⊆
      Set.range G := by
  apply complement_component_subset_range_of_odd_degree boundary
    hobstruction G hG (givensBoundaryCurveAddCircle j)
    (continuous_givensBoundaryCurveAddCircle j) hboundary 0
    (givensBoundaryCurveAddCircle_ne_zero j) 1
  · simpa [givensBoundaryCurveAddCircle] using
      givensBoundaryCurve_degree_one j
  · exact odd_one

/-- Once Jordan separation supplies its two regions, the region containing
the origin is covered by every extension over a domain with the odd
boundary-degree obstruction. -/
theorem givensBoundaryCurve_jordan_region_subset_range_of_odd_boundary_degree_obstruction
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range G := by
  rw [givensBoundaryCurve_jordan_region_at_origin j hpartition hzero]
  exact givensBoundaryCurve_origin_component_subset_range
    j boundary hobstruction G hG hboundary

/-- The Jordan region needed in the coverage conclusion exists already from
the odd boundary-degree obstruction itself: no fine-model hypothesis is
required once the obstruction is available. -/
theorem exists_givensBoundaryCurve_bounded_region_subset_range_of_odd_boundary_degree_obstruction
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range G := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  exact ⟨region₁, hpartition.region₁_open,
    hpartition.region₁_connected,
    givensBoundaryCurve_jordan_region_at_origin_bounded
      j hpartition hzero,
    hzero,
    givensBoundaryCurve_jordan_region_subset_range_of_odd_boundary_degree_obstruction
      j boundary hobstruction G hG hboundary hpartition hzero⟩

/-- Mixed-boundary coverage with the odd-degree obstruction itself
discharged by compatible fine polygonal models. -/
theorem givensBoundaryCurve_origin_component_subset_range_of_fine_models
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hfine : HasFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t) :
    connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 ⊆
      Set.range G :=
  givensBoundaryCurve_origin_component_subset_range j boundary
    (hasOddBoundaryDegreeObstruction_of_finePolygonalModels hfine)
    G hG hboundary

/-- Once Jordan separation supplies its two regions, the region containing
the origin is covered by every extension over a domain with fine
polygonal models. -/
theorem givensBoundaryCurve_jordan_region_subset_range_of_fine_models
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hfine : HasFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range G := by
  rw [givensBoundaryCurve_jordan_region_at_origin j hpartition hzero]
  exact givensBoundaryCurve_origin_component_subset_range_of_fine_models
    j boundary hfine G hG hboundary

/-- The Jordan region needed in the coverage conclusion exists: no
separation hypothesis is required from callers. -/
theorem exists_givensBoundaryCurve_bounded_region_subset_range_of_fine_models
    {X : Type*} [TopologicalSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hfine : HasFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range G := by
  obtain ⟨region₁, region₂, hpartition, hzero⟩ :=
    exists_givensBoundaryCurve_jordanPartition_at_origin j
  exact ⟨region₁, hpartition.region₁_open,
    hpartition.region₁_connected,
    givensBoundaryCurve_jordan_region_at_origin_bounded
      j hpartition hzero,
    hzero,
    givensBoundaryCurve_jordan_region_subset_range_of_fine_models
      j boundary hfine G hG hboundary hpartition hzero⟩

/-- Surface-form coverage from the map-independent geometric input.  On a
compact metric domain, arbitrary geometric mesh refinement supplies the
map-dependent half-turn model automatically by uniform continuity. -/
theorem givensBoundaryCurve_jordan_region_subset_range_of_arbitrarily_fine_models
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range G :=
  givensBoundaryCurve_jordan_region_subset_range_of_fine_models
    j boundary (hasFinePolygonalModels_of_arbitrarilyFine hmodels)
    G hG hboundary hpartition hzero

/-- Coverage also transfers from any compact source with arbitrarily fine
polygonal models once a boundary-respecting homeomorphism identifies that
source with the target domain.  This packages the exact downstream use of a
future disk or surface triangulation theorem. -/
theorem givensBoundaryCurve_jordan_region_subset_range_of_homeomorph_arbitrarily_fine_models
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (G : Y → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary' t) = givensBoundaryCurveAddCircle j t)
    {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ ⊆ Set.range G :=
  givensBoundaryCurve_jordan_region_subset_range_of_fine_models
    j boundary'
    (hasFinePolygonalModels_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)
    G hG hboundary hpartition hzero

/-- The separation-free coverage conclusion from arbitrarily fine
geometric polygonal models. -/
theorem exists_givensBoundaryCurve_bounded_region_subset_range_of_arbitrarily_fine_models
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → X)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (G : X → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary t) = givensBoundaryCurveAddCircle j t) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range G :=
  exists_givensBoundaryCurve_bounded_region_subset_range_of_fine_models
    j boundary (hasFinePolygonalModels_of_arbitrarilyFine hmodels)
    G hG hboundary

/-- Separation-free coverage also transfers from a compact source with
arbitrarily fine polygonal models through a boundary-respecting
homeomorphism. -/
theorem exists_givensBoundaryCurve_bounded_region_subset_range_of_homeomorph_arbitrarily_fine_models
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (G : Y → ℂ) (hG : Continuous G)
    (hboundary : ∀ t,
      G (boundary' t) = givensBoundaryCurveAddCircle j t) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      region ⊆ Set.range G :=
  exists_givensBoundaryCurve_bounded_region_subset_range_of_fine_models
    j boundary'
    (hasFinePolygonalModels_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)
    G hG hboundary

end

end GromovFilling
