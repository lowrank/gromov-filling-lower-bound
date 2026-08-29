import ClassificationOfSurfaces.EvalStatement

/-!
# Compact-surface classification foundation

This module exposes the faithful classification-of-surfaces theorem at the
Gromov-filling namespace.  It classifies every compact connected Hausdorff
topological two-manifold with boundary by the sphere or an orientable or
nonorientable polygonal normal-form quotient.  The theorem does not identify a
chosen boundary parametrization with a particular free loop of that quotient;
that is the remaining relative-boundary obligation for Lemma 5.4.
-/

open scoped Manifold

namespace GromovFilling

open LeanEval.Topology.ClassificationOfSurfaces

/-- Faithful topological classification of compact connected surfaces, with
the exact normal-form indices and quotient spaces exposed in the conclusion. -/
theorem compact_connected_surface_classification
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S] :
    Nonempty (S ≃ₜ SphereRepresentative) ∨
      ∃ p n,
        ((1 ≤ p ∨ 1 ≤ n) ∧
            Nonempty (S ≃ₜ Quot (OrientableRel p n))) ∨
          (1 ≤ p ∧
            Nonempty (S ≃ₜ Quot (NonOrientableRel p n))) :=
  classification_of_surfaces S

end GromovFilling
