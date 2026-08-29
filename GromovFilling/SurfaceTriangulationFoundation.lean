import ClassificationOfSurfaces.Triangulation

/-!
# Compact-surface triangulation foundation

This module exposes the boundary-capable Radó triangulation theorem at the
Gromov-filling namespace.  It supplies an unconditional finite geometric
triangulation under the exact compact connected topological-surface
hypotheses, and a strengthened output retaining the full-support Radó
invariant needed to identify the simplicial boundary.
-/

open scoped Manifold

namespace GromovFilling

open LeanEval.Topology.ClassificationOfSurfaces

/-- Every compact connected Hausdorff topological two-manifold with boundary
admits a full-support finite partial triangulation whose complete Radó
invariant is retained.  In particular, every triangle meets the ambient
manifold boundary in one exposed simplicial face of cardinality at most two. -/
theorem exists_full_support_boundary_facewise_regular_partial_triangulation
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    ∃ T : Moise.PartialTriangulation S,
      T.support = Set.univ ∧
      T.BoundaryFacewiseRegular ∧
      ∀ e ∈ T.edges, (T.faces.filter fun t => e ⊆ t).card ≤ 2 := by
  obtain ⟨T, hT⟩ := Moise.moise_radoInvariant_univ_of_boundaries S
  exact ⟨T, Set.eq_univ_of_univ_subset hT.coresCovered,
    hT.boundaryFacewiseRegular, hT.combSurface⟩

/-- Every compact connected Hausdorff topological two-manifold with boundary
admits a finite geometric triangulation.  This is the Radó foundation needed
by the finite mod-two obstruction in Lemma 5.4. -/
theorem exists_geometricTriangulation_compact_connected_surface
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (GeometricTriangulation S) :=
  moise_triangulation S

end GromovFilling
