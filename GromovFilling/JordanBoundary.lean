import GromovFilling.BoundaryDegreeComponents
import Mathlib.Topology.Connected.Clopen

/-!
# Mixed boundary curves as topological Jordan curves

The mixed Givens curves are continuous injective images of the circle.
This file packages that fact as an actual homeomorphism with their range,
which is the standard topological definition of a Jordan curve.
-/

namespace GromovFilling

noncomputable section

/-- A continuous injective circle parametrization is a homeomorphism onto
its range, by compactness of the circle and the Hausdorff property of the
target. -/
theorem homeomorph_range_of_continuous_injective_circle
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    Nonempty (Set.range curve ≃ₜ UnitAddCircle) := by
  let toRange : UnitAddCircle → Set.range curve := fun x ↦
    ⟨curve x, ⟨x, rfl⟩⟩
  have hbijective : Function.Bijective toRange := by
    constructor
    · intro x y hxy
      exact hinjective (congrArg Subtype.val hxy)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e : UnitAddCircle ≃ Set.range curve :=
    Equiv.ofBijective toRange hbijective
  have heContinuous : Continuous e := by
    change Continuous toRange
    exact hcurve.subtype_mk (fun x ↦ ⟨x, rfl⟩)
  exact ⟨(Continuous.homeoOfEquivCompactToT2
    (f := e) heContinuous).symm⟩

/-- Every mixed Givens boundary curve is a Jordan curve in the precise
sense that its image is homeomorphic to the circle. -/
theorem givensBoundaryCurve_range_homeomorph_circle
    {N : ℕ} (j : Fin N) :
    Nonempty
      (Set.range (givensBoundaryCurveAddCircle j) ≃ₜ UnitAddCircle) := by
  apply homeomorph_range_of_continuous_injective_circle
    (givensBoundaryCurveAddCircle j)
    (continuous_givensBoundaryCurveAddCircle j)
  intro x y hxy
  unfold givensBoundaryCurveAddCircle at hxy
  exact unitAddCircleEquivComplexUnitCircle.injective
    (givensBoundaryCurve_injective j hxy)

/-- The image of every mixed Givens boundary curve is compact. -/
theorem givensBoundaryCurve_range_compact
    {N : ℕ} (j : Fin N) :
    IsCompact (Set.range (givensBoundaryCurveAddCircle j)) := by
  rw [← Set.image_univ]
  exact isCompact_univ.image (continuous_givensBoundaryCurveAddCircle j)

/-- The image of every mixed Givens boundary curve is closed in the
complex plane. -/
theorem givensBoundaryCurve_range_closed
    {N : ℕ} (j : Fin N) :
    IsClosed (Set.range (givensBoundaryCurveAddCircle j)) :=
  (givensBoundaryCurve_range_compact j).isClosed

/-- Data supplied by the Jordan separation theorem: two disjoint open
connected regions, disjoint from the curve, which together with the curve
partition the ambient space. -/
structure IsJordanPartition
    {Y : Type*} [TopologicalSpace Y]
    (curve region₁ region₂ : Set Y) : Prop where
  region₁_open : IsOpen region₁
  region₂_open : IsOpen region₂
  region₁_connected : IsConnected region₁
  region₂_connected : IsConnected region₂
  regions_disjoint : Disjoint region₁ region₂
  region₁_curve_disjoint : Disjoint region₁ curve
  region₂_curve_disjoint : Disjoint region₂ curve
  cover : region₁ ∪ region₂ ∪ curve = Set.univ

/-- In a Jordan partition, the region containing `y` is exactly the
connected component of `y` in the curve complement. -/
theorem IsJordanPartition.region₁_eq_connectedComponentIn
    {Y : Type*} [TopologicalSpace Y]
    {curve region₁ region₂ : Set Y}
    (h : IsJordanPartition curve region₁ region₂)
    {y : Y} (hy : y ∈ region₁) :
    region₁ = connectedComponentIn curveᶜ y := by
  have hregion₁Compl : region₁ ⊆ curveᶜ := by
    intro x hx hxc
    exact Set.disjoint_left.mp h.region₁_curve_disjoint hx hxc
  apply Set.Subset.antisymm
  · exact h.region₁_connected.isPreconnected.subset_connectedComponentIn
      hy hregion₁Compl
  · have hyComponent : y ∈ connectedComponentIn curveᶜ y :=
      mem_connectedComponentIn (hregion₁Compl hy)
    have hcomponentSubset :
        connectedComponentIn curveᶜ y ⊆ region₁ ∪ region₂ := by
      intro x hx
      have hxc : x ∈ curveᶜ := connectedComponentIn_subset curveᶜ y hx
      have hxu : x ∈ region₁ ∪ region₂ ∪ curve := by
        rw [h.cover]
        exact Set.mem_univ x
      rcases hxu with hxRegions | hxCurve
      · exact hxRegions
      · exact False.elim (hxc hxCurve)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      h.region₁_open h.region₂_open h.regions_disjoint hcomponentSubset
      ⟨y, hyComponent, hy⟩

/-- The region containing the origin in any Jordan partition of a mixed
Givens curve is the previously constructed degree-one component. -/
theorem givensBoundaryCurve_jordan_region_at_origin
    {N : ℕ} (j : Fin N) {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    region₁ = connectedComponentIn
      (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 :=
  hpartition.region₁_eq_connectedComponentIn hzero

/-- Consequently the Jordan region containing the origin is bounded. -/
theorem givensBoundaryCurve_jordan_region_at_origin_bounded
    {N : ℕ} (j : Fin N) {region₁ region₂ : Set ℂ}
    (hpartition : IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂)
    (hzero : 0 ∈ region₁) :
    Bornology.IsBounded region₁ := by
  rw [givensBoundaryCurve_jordan_region_at_origin j hpartition hzero]
  exact givensBoundaryCurve_origin_component_bounded j

end

end GromovFilling
