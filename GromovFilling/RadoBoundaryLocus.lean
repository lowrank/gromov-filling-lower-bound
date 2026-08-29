import GromovFilling.BoundaryLocusClassification
import GromovFilling.SurfaceTriangulationFoundation
import ClassificationOfSurfaces.GeometricTriangulationRealization

/-!
# The combinatorial boundary of a geometric surface triangulation

This file identifies the once-used sides of the finite-cyclic presentation
with the valence-one edges of the original geometric triangulation.  It is the
purely combinatorial half of the Radó boundary bridge needed by Lemma 5.4;
identification with the ambient manifold boundary is kept as a separate
topological theorem boundary.
-/

open scoped Manifold

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace GeometricTriangulation

open Set SurfaceCellComplex

noncomputable section

variable {S : Type*} [TopologicalSpace S]

/-- The complete barycentric locus carried by edges incident to exactly one
geometric triangle.  Endpoints are included. -/
def SimplicialBoundaryLocus (T : GeometricTriangulation S) : Set T.realization :=
  {x | ∃ e : T.Edge, T.IsBoundaryEdge e ∧
      x ∈ T.toIntrinsic.faceCarrier e.1}

theorem mem_simplicialBoundaryLocus_iff
    {T : GeometricTriangulation S} {x : T.realization} :
    x ∈ T.SimplicialBoundaryLocus ↔
      ∃ e : T.Edge, T.IsBoundaryEdge e ∧
        x ∈ T.toIntrinsic.faceCarrier e.1 :=
  Iff.rfl

private theorem finiteCyclicEdgeEquiv_cyclicOrientedEdge
    (T : GeometricTriangulation S)
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    T.toFiniteSurfaceTriangulation.finiteCyclicEdgeEquiv
        (T.cyclicOrientedEdge o).edge = o.edge := by
  calc
    T.toFiniteSurfaceTriangulation.finiteCyclicEdgeEquiv
        (T.cyclicOrientedEdge o).edge =
        FiniteCyclicPresentation.edgeOfDart
          (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv
            (T.cyclicOrientedEdge o)) :=
      (T.toFiniteSurfaceTriangulation
        |>.edgeOfDart_finiteCyclicDartEquiv_eq_edgeEquiv
          (T.cyclicOrientedEdge o)).symm
    _ = FiniteCyclicPresentation.edgeOfDart o.dart := by
      rw [T.finiteCyclicDartEquiv_cyclicOrientedEdge]
    _ = o.edge := rfl

private theorem polygonalRealizationMap_occurrenceSide_mem_faceCarrier
    (T : GeometricTriangulation S)
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence)
    (r : unitInterval) :
    T.polygonalRealizationMap valid
          (T.toFiniteCyclicPresentation.polygonalMk valid
            ((T.toFiniteCyclicPresentation.occurrenceSide o).point r)) ∈
      T.toIntrinsic.faceCarrier (T.cyclicOrientedEdge o).edge.1 := by
  change ∀ v ∉ (T.cyclicOrientedEdge o).edge.1,
    (T.polygonalPreMap
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r)).1 v = 0
  intro v hv
  change
    ((T.polygonFaceHomeomorph o.1)
      (PolygonCell.side o.2 r)).1.1 v = 0
  rw [T.polygonFaceHomeomorph_side_oriented,
    AffineMap.lineMap_apply_module]
  have hsource :
      T.orientedEdgeSource (T.cyclicOrientedEdge o) ∈
        (T.cyclicOrientedEdge o).edge.1 := by
    cases h : T.cyclicOrientedEdge o with
    | pos e =>
        simpa [GeometricTriangulation.orientedEdgeSource,
          OrientedEdge.edge] using T.edgeSource_mem e
    | neg e =>
        simpa [GeometricTriangulation.orientedEdgeSource,
          OrientedEdge.edge] using T.edgeTarget_mem e
  have htarget :
      T.orientedEdgeTarget (T.cyclicOrientedEdge o) ∈
        (T.cyclicOrientedEdge o).edge.1 := by
    cases h : T.cyclicOrientedEdge o with
    | pos e =>
        simpa [GeometricTriangulation.orientedEdgeTarget,
          OrientedEdge.edge] using T.edgeTarget_mem e
    | neg e =>
        simpa [GeometricTriangulation.orientedEdgeTarget,
          OrientedEdge.edge] using T.edgeSource_mem e
  have hvsource : v ≠ T.orientedEdgeSource (T.cyclicOrientedEdge o) :=
    fun h ↦ hv (h ▸ hsource)
  have hvtarget : v ≠ T.orientedEdgeTarget (T.cyclicOrientedEdge o) :=
    fun h ↦ hv (h ▸ htarget)
  simp [hvsource, hvtarget]

/-- The faithful polygonal-realization homeomorphism sends the complete
once-used-side locus exactly onto the complete valence-one edge locus of the
geometric triangulation. -/
theorem image_polygonalBoundaryLocus_polygonalRealizationHomeomorph
    (T : GeometricTriangulation S)
    (valid : T.toFiniteCyclicPresentation.IsSurfaceValid)
    (hstar : TriangleFamily.IsStrongVertexStarConnected T.faces) :
    (T.polygonalRealizationHomeomorph valid hstar) ''
        (T.toFiniteCyclicPresentation.PolygonalBoundaryLocus valid) =
      T.SimplicialBoundaryLocus := by
  ext x
  constructor
  · rintro ⟨q, ⟨o, r, ho, rfl⟩, rfl⟩
    let e : T.Edge := (T.cyclicOrientedEdge o).edge
    refine ⟨e, ?_, ?_⟩
    · apply (T.toFiniteCyclicPresentation_isBoundaryEdge_edgeEquiv_iff e).mp
      rw [T.finiteCyclicEdgeEquiv_cyclicOrientedEdge o]
      exact ho
    · exact T.polygonalRealizationMap_occurrenceSide_mem_faceCarrier
        valid o r
  · rintro ⟨e, he, hxe⟩
    let E : T.toFiniteCyclicPresentation.Edge :=
      T.toFiniteSurfaceTriangulation.finiteCyclicEdgeEquiv e
    have hE : T.toFiniteCyclicPresentation.IsBoundaryEdge E :=
      (T.toFiniteCyclicPresentation_isBoundaryEdge_edgeEquiv_iff e).mpr he
    have hcard :
        (T.toFiniteCyclicPresentation.edgeOccurrences E).card = 1 := by
      rw [T.toFiniteCyclicPresentation.card_edgeOccurrences]
      exact hE
    have hnonempty :
        (T.toFiniteCyclicPresentation.edgeOccurrences E).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨o, ho⟩ := hnonempty
    have hoedge : o.edge = E :=
      (T.toFiniteCyclicPresentation.mem_edgeOccurrences E o).mp ho
    have hdedge : (T.cyclicOrientedEdge o).edge = e := by
      apply T.toFiniteSurfaceTriangulation.finiteCyclicEdgeEquiv.injective
      rw [T.finiteCyclicEdgeEquiv_cyclicOrientedEdge o, hoedge]
    obtain ⟨r, hr⟩ := T.exists_orientedEdgeParameter
      (T.cyclicOrientedEdge o) x (hdedge ▸ hxe)
    let q := T.toFiniteCyclicPresentation.polygonalMk valid
      ((T.toFiniteCyclicPresentation.occurrenceSide o).point r)
    refine ⟨q, ?_, ?_⟩
    · refine ⟨o, r, ?_, rfl⟩
      rw [hoedge]
      exact hE
    · apply Subtype.ext
      change
        ((T.polygonFaceHomeomorph o.1)
          (PolygonCell.side o.2 r)).1.1 = x.1
      rw [T.polygonFaceHomeomorph_side_oriented]
      exact hr.symm

end

end GeometricTriangulation

end LeanEval.Topology.ClassificationOfSurfaces
