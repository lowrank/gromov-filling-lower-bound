import GromovFilling.JordanBoundary
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Jordan coverage through manifold interior points

The area half of Lemma 5.4 only needs charts around interior points.  Indeed,
the covered Jordan region is disjoint from its boundary curve, while every
manifold-boundary value lies on that curve.  Consequently no preimage used
to cover the region can lie on the manifold boundary.

This observation avoids any change-of-variables theorem for half-space
charts: the analytic globalization may be built entirely from ordinary
complex charts contained in the manifold interior.
-/

open Set
open scoped Manifold

namespace GromovFilling

noncomputable section

/-- If `omega` is covered by `G`, is disjoint from `curve`, and the manifold
boundary maps into `curve`, then `omega` is already covered by the image of
the manifold interior. -/
theorem subset_image_interior_of_subset_range_of_boundary_mapsTo
    {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (G : M → Y) (omega curve : Set Y)
    (hdisjoint : Disjoint omega curve)
    (hboundary : Set.MapsTo G (I.boundary M) curve)
    (hcoverage : omega ⊆ Set.range G) :
    omega ⊆ G '' I.interior M := by
  intro y hy
  rcases hcoverage hy with ⟨x, hx⟩
  refine ⟨x, ?_, hx⟩
  rw [← I.compl_boundary]
  intro hxBoundary
  have hyCurve : y ∈ curve := by
    rw [← hx]
    exact hboundary hxBoundary
  exact Set.disjoint_left.1 hdisjoint hy hyCurve

/-- Jordan-partition specialization of
`subset_image_interior_of_subset_range_of_boundary_mapsTo` for the first
complementary region. -/
theorem IsJordanPartition.region₁_subset_image_interior
    {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace Y]
    {curve region₁ region₂ : Set Y}
    (hpartition : IsJordanPartition curve region₁ region₂)
    (G : M → Y)
    (hboundary : Set.MapsTo G (I.boundary M) curve)
    (hcoverage : region₁ ⊆ Set.range G) :
    region₁ ⊆ G '' I.interior M :=
  subset_image_interior_of_subset_range_of_boundary_mapsTo
    I G region₁ curve hpartition.region₁_curve_disjoint hboundary hcoverage

/-- Direct manuscript interface: if `boundary` parametrizes the whole
manifold boundary, `G ∘ boundary` traces the Jordan curve, and the first
Jordan region is covered by `G`, then that region is covered using interior
preimages only. -/
theorem IsJordanPartition.region₁_subset_image_interior_of_boundary_parametrization
    {β E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace Y]
    (boundary : β → M) (G : M → Y) (curve : β → Y)
    {region₁ region₂ : Set Y}
    (hpartition : IsJordanPartition (Set.range curve) region₁ region₂)
    (hboundaryRange : Set.range boundary = I.boundary M)
    (htrace : ∀ t, G (boundary t) = curve t)
    (hcoverage : region₁ ⊆ Set.range G) :
    region₁ ⊆ G '' I.interior M := by
  apply hpartition.region₁_subset_image_interior I G
  · intro x hx
    rw [← hboundaryRange] at hx
    rcases hx with ⟨t, rfl⟩
    exact ⟨t, (htrace t).symm⟩
  · exact hcoverage

end

end GromovFilling
