import GromovFilling.RiemannianHalfSpaceChart

/-!
# Boundary axes under half-space chart transitions

An extended-chart transition between two charts of a manifold with boundary
preserves the model boundary face.  This elementary topological fact is the
first local ingredient for comparing induced boundary directions with surface
orientation signs; it contains no derivative or orientation assertion.
-/

open Manifold Set
open scoped Manifold

namespace GromovFilling

noncomputable section

/-- If a point on the model boundary axis belongs to the source of two
extended charts, then its coordinate in the second chart is again on the
model boundary axis. -/
theorem extChartAt_axis_maps_to_axis
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).target)
    (hy : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      (chartAt (EuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) b
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z)) 0 = 0 := by
  let I := modelWithCornersEuclideanHalfSpace 2
  have hsourceAExt : (extChartAt I a).symm z ∈ (extChartAt I a).source :=
    (extChartAt I a).map_target hz
  have hsourceA : (extChartAt I a).symm z ∈ (chartAt (EuclideanHalfSpace 2) a).source := by
    simpa only [extChartAt_source] using hsourceAExt
  have hboundary : (extChartAt I a).symm z ∈ I.boundary M := by
    change I.IsBoundaryPoint ((extChartAt I a).symm z)
    rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (I := I) _]
    intro hinterior
    have hcoord : extChartAt I a ((extChartAt I a).symm z) ∈
        interior (extChartAt I a).target :=
      (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
        (chart_mem_atlas (EuclideanHalfSpace 2) a) hsourceA).mp hinterior
    rw [(extChartAt I a).right_inv hz] at hcoord
    have hrange : z ∈ interior (Set.range I) :=
      interior_mono (extChartAt_target_subset_range a) hcoord
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at hrange
    have hpos : 0 < z 0 := by
      simpa only [mem_setOf_eq] using hrange
    rw [hzAxis] at hpos
    exact (lt_irrefl 0) hpos
  have hsourceBExt : (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [extChartAt_source] using hy
  have htargetB : extChartAt I b ((extChartAt I a).symm z) ∈
      (extChartAt I b).target :=
    (extChartAt I b).map_source hsourceBExt
  have hnonneg : 0 ≤ (extChartAt I b ((extChartAt I a).symm z)) 0 := by
    have hrange : extChartAt I b ((extChartAt I a).symm z) ∈ Set.range I :=
      extChartAt_target_subset_range b htargetB
    rw [range_modelWithCornersEuclideanHalfSpace] at hrange
    simpa only [mem_setOf_eq] using hrange
  apply le_antisymm ?_ hnonneg
  by_contra hnot
  have hpos : 0 < (extChartAt I b ((extChartAt I a).symm z)) 0 :=
    lt_of_not_ge hnot
  have hrangeInterior : extChartAt I b ((extChartAt I a).symm z) ∈
      interior (Set.range I) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa only [mem_setOf_eq] using hpos
  have htargetInterior : extChartAt I b ((extChartAt I a).symm z) ∈
      interior (extChartAt I b).target := by
    rw [interior_extChartAt_target_eq_inter_interior_range]
    exact ⟨htargetB, hrangeInterior⟩
  have hinterior : I.IsInteriorPoint ((extChartAt I a).symm z) :=
    (I.isInteriorPoint_iff_of_mem_atlas one_ne_zero
      (chart_mem_atlas (EuclideanHalfSpace 2) b) hy).mpr htargetInterior
  exact ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (I := I) _).mp
    hboundary) hinterior

#print axioms extChartAt_axis_maps_to_axis

end

end GromovFilling
