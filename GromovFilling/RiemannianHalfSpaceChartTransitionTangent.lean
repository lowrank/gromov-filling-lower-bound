import GromovFilling.RiemannianHalfSpaceChartTransition
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent coordinate changes for half-space chart transitions

The boundary-transition lemmas are stated for the derivative restricted to
the actual overlap source of two extended charts.  The tangent-bundle API
instead defines its coordinate change using the derivative within the model
range.  On an overlap these derivatives agree, because the overlap source is
a neighborhood relative to the model range.  This file records that exact
identification and contains no orientation or boundary-direction claim.
-/

open Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

/-- On an overlap of two extended half-space charts, the derivative used by
the boundary-transition layer is exactly the tangent-bundle coordinate
change. -/
theorem fderivWithin_extChartAt_transition_eq_tangentCoordChange
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source) :
    fderivWithin ℝ
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
        extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z =
      tangentCoordChange (modelWithCornersEuclideanHalfSpace 2) a b
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z) := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let s : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((extChartAt I a).symm ≫ extChartAt I b).source
  change fderivWithin ℝ T s z =
    tangentCoordChange I a b ((extChartAt I a).symm z)
  have hzChange : z ∈ (I.extendCoordChange
      (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source := by
    change z ∈ (I.extendCoordChange
      (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source at hz
    exact hz
  have hsNhds : s ∈ 𝓝[Set.range I] z := by
    change (I.extendCoordChange
      (chartAt (EuclideanHalfSpace 2) a)
      (chartAt (EuclideanHalfSpace 2) b)).source ∈ 𝓝[Set.range I] z
    exact I.extendCoordChange_source_mem_nhdsWithin hzChange
  have hzSplit : z ∈ (extChartAt I a).target ∧
      (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [s, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  have hzTarget : z ∈ (extChartAt I a).target := hzSplit.1
  have hzRange : z ∈ Set.range I :=
    extChartAt_target_subset_range a hzTarget
  have hunique : UniqueDiffWithinAt ℝ (Set.range I) z :=
    I.uniqueDiffOn.uniqueDiffWithinAt hzRange
  have hdiff : DifferentiableWithinAt ℝ T s z := by
    simpa only [I, T, s, Function.comp_apply] using
      (contDiffOn_ext_coord_change b a z hz).differentiableWithinAt one_ne_zero
  have hfderiv : fderivWithin ℝ T (Set.range I) z =
      fderivWithin ℝ T s z :=
    fderivWithin_of_mem_nhdsWithin hsNhds hunique hdiff
  calc
    fderivWithin ℝ T s z = fderivWithin ℝ T (Set.range I) z := hfderiv.symm
    _ = tangentCoordChange I a b ((extChartAt I a).symm z) := by
      rw [tangentCoordChange_def, (extChartAt I a).right_inv hzTarget]

#print axioms fderivWithin_extChartAt_transition_eq_tangentCoordChange

end

end GromovFilling
