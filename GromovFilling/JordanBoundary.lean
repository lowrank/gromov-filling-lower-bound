import GromovFilling.BoundaryDegreeComponents

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

end

end GromovFilling
