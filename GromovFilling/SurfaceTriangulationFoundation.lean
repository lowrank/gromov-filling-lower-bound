import ClassificationOfSurfaces.Triangulation

/-!
# Compact-surface triangulation foundation

This module exposes the boundary-capable Radó triangulation theorem at the
Gromov-filling namespace.  It supplies an unconditional finite geometric
triangulation under the exact compact connected topological-surface
hypotheses.  The imported theorem does not retain its internal
boundary-facewise regularity in the returned structure; recovering that data
is the next topology obligation for Lemma 5.4.
-/

open scoped Manifold

namespace GromovFilling

open LeanEval.Topology.ClassificationOfSurfaces

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
