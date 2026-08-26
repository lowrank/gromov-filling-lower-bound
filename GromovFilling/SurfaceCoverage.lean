import GromovFilling.PolygonalSurfaceObstruction
import GromovFilling.BoundaryDegreeComponents

/-!
# Coverage from the odd boundary-degree obstruction

This file turns the topological obstruction in Lemma 5.4 into its planar
coverage conclusion.  It also specializes the conclusion to the bounded
nonzero-degree component of each mixed Givens boundary curve.
-/

namespace GromovFilling

noncomputable section

/-- A boundary parametrization has the mod-two extension obstruction when
no continuous circle-valued map on the whole domain can restrict to odd
degree on that boundary.  `no_odd_degree_of_fine_polygonal_circle_extension`
proves this property from a sufficiently fine polygonal model. -/
def HasOddBoundaryDegreeObstruction
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    ∀ d : ℤ, HasCircleDegree (H ∘ boundary) d → Odd d → False

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

end

end GromovFilling
