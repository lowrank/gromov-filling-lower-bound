import GromovFilling.BoundaryDegreeComponents
import Mathlib.Topology.Connected.Clopen
import JordanCurveTheorem.JordanCurveTheoremStatement

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

/-- The interval-parametrized simple-closed-curve predicate used by the
upstream Jordan theorem follows from the intrinsic homeomorphism-to-circle
form used in this project. -/
theorem upstream_simpleClosedCurve_of_homeomorph_circle
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (hC : Nonempty (C ≃ₜ UnitAddCircle)) :
    IsSimpleClosedCurve C := by
  obtain ⟨e⟩ := hC
  refine ⟨fun t ↦ ↑(e.symm (↑t : UnitAddCircle)), ?_, ?_, ?_, ?_⟩
  · ext c
    simp only [Set.mem_image]
    constructor
    · intro hc
      set q := e ⟨c, hc⟩
      have ht := (AddCircle.equivIco 1 0 q).2
      refine ⟨(AddCircle.equivIco 1 0 q).1,
        Set.Ico_subset_Icc_self (by simpa using ht), ?_⟩
      change (e.symm (↑(AddCircle.equivIco 1 0 q).1 : UnitAddCircle) :
        EuclideanSpace ℝ (Fin 2)) = c
      rw [(AddCircle.equivIco 1 0).injective
        ((AddCircle.equivIco_coe_eq ht).trans rfl)]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨c, hc⟩)
    · rintro ⟨t, _, rfl⟩
      exact (e.symm (↑t : UnitAddCircle)).2
  · exact continuous_subtype_val.comp
      (e.symm.continuous.comp (AddCircle.continuous_mk' 1))
  · intro a ha b hb hab
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      ⟨ha.1, by linarith [ha.2]⟩
      ⟨hb.1, by linarith [hb.2]⟩).mp
        (e.symm.injective (Subtype.val_injective hab))
  · change (e.symm (↑(0 : ℝ) : UnitAddCircle) :
      EuclideanSpace ℝ (Fin 2)) =
      (e.symm (↑(1 : ℝ) : UnitAddCircle) : EuclideanSpace ℝ (Fin 2))
    exact congrArg (fun x ↦ (e.symm x : EuclideanSpace ℝ (Fin 2)))
      (by simp [AddCircle.coe_period])

/-- The Jordan curve theorem transported from Euclidean two-space to the
complex plane.  This removes the previously explicit `IsJordanPartition`
hypothesis for every curve intrinsically homeomorphic to the circle. -/
theorem exists_jordanPartition_of_homeomorph_circle_complex
    (C : Set ℂ) (hC : Nonempty (C ≃ₜ UnitAddCircle)) :
    ∃ region₁ region₂ : Set ℂ, IsJordanPartition C region₁ region₂ := by
  let e : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph
  have hImageCircle : Nonempty ((e '' C) ≃ₜ UnitAddCircle) := by
    obtain ⟨h⟩ := hC
    exact ⟨(e.image C).symm.trans h⟩
  have hSimple : IsSimpleClosedCurve (e '' C) :=
    upstream_simpleClosedCurve_of_homeomorph_circle (e '' C) hImageCircle
  obtain ⟨A, B, hAOpen, hBOpen, hAConnected, hBConnected,
      hAB, hAC, hBC, hcover⟩ :=
    JordanCurveTheorem.jordan_curve_theorem hSimple
  refine ⟨e.symm '' A, e.symm '' B, ?_⟩
  have hcurve : e.symm '' (e '' C) = C := by
    simp only [Set.image_image, e.symm_apply_apply, Set.image_id']
  refine
    { region₁_open := e.symm.isOpenMap A hAOpen
      region₂_open := e.symm.isOpenMap B hBOpen
      region₁_connected := (e.symm.isConnected_image).2 hAConnected
      region₂_connected := (e.symm.isConnected_image).2 hBConnected
      regions_disjoint := Set.disjoint_image_of_injective e.symm.injective hAB
      region₁_curve_disjoint := ?_
      region₂_curve_disjoint := ?_
      cover := ?_ }
  · rw [← hcurve]
    exact Set.disjoint_image_of_injective e.symm.injective hAC
  · rw [← hcurve]
    exact Set.disjoint_image_of_injective e.symm.injective hBC
  · have himageCover := congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) ↦
        e.symm '' S) hcover
    simpa only [Set.image_union, hcurve, Set.image_univ,
      e.symm.surjective.range_eq] using himageCover

/-- Swap the two complementary regions of a Jordan partition. -/
theorem IsJordanPartition.swap
    {Y : Type*} [TopologicalSpace Y]
    {curve region₁ region₂ : Set Y}
    (h : IsJordanPartition curve region₁ region₂) :
    IsJordanPartition curve region₂ region₁ where
  region₁_open := h.region₂_open
  region₂_open := h.region₁_open
  region₁_connected := h.region₂_connected
  region₂_connected := h.region₁_connected
  regions_disjoint := h.regions_disjoint.symm
  region₁_curve_disjoint := h.region₂_curve_disjoint
  region₂_curve_disjoint := h.region₁_curve_disjoint
  cover := by
    simpa only [Set.union_comm region₂ region₁] using h.cover

/-- A point outside a complex Jordan curve can be placed in the first
region of a Jordan partition. -/
theorem exists_jordanPartition_at_point_complex
    (C : Set ℂ) (hC : Nonempty (C ≃ₜ UnitAddCircle))
    (y : ℂ) (hy : y ∉ C) :
    ∃ region₁ region₂ : Set ℂ,
      IsJordanPartition C region₁ region₂ ∧ y ∈ region₁ := by
  obtain ⟨A, B, hpartition⟩ :=
    exists_jordanPartition_of_homeomorph_circle_complex C hC
  have hyRegions : y ∈ A ∨ y ∈ B := by
    have hyCover : y ∈ A ∪ B ∪ C := by
      rw [hpartition.cover]
      exact Set.mem_univ y
    rcases hyCover with hyAB | hyC
    · exact hyAB
    · exact False.elim (hy hyC)
  rcases hyRegions with hyA | hyB
  · exact ⟨A, B, hpartition, hyA⟩
  · exact ⟨B, A, hpartition.swap, hyB⟩

/-- The mixed Givens boundary curve has an actual Jordan partition whose
first region contains the origin. -/
theorem exists_givensBoundaryCurve_jordanPartition_at_origin
    {N : ℕ} (j : Fin N) :
    ∃ region₁ region₂ : Set ℂ,
      IsJordanPartition
        (Set.range (givensBoundaryCurveAddCircle j)) region₁ region₂ ∧
      0 ∈ region₁ :=
  exists_jordanPartition_at_point_complex
    (Set.range (givensBoundaryCurveAddCircle j))
    (givensBoundaryCurve_range_homeomorph_circle j) 0
    (fun hzero ↦ by
      obtain ⟨t, ht⟩ := hzero
      exact givensBoundaryCurveAddCircle_ne_zero j t ht)

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
