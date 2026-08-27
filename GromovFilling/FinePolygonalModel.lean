import GromovFilling.PolygonalSurfaceObstruction
import Mathlib.Topology.UniformSpace.Compact

/-!
# Bundled fine polygonal models

This packages the exact finite datum required by the no-odd-degree
argument.  The remaining surface-topology input to Lemma 5.4 is precisely
the construction of one such model for every continuous circle map.
-/

namespace GromovFilling

noncomputable section

/-- A boundary parametrization has the mod-two extension obstruction when
no continuous circle-valued map on the whole domain can restrict to odd
degree on that boundary. -/
def HasOddBoundaryDegreeObstruction
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    ∀ d : ℤ, HasCircleDegree (H ∘ boundary) d → Odd d → False

/-- The standard closed parameter interval for every polygonal edge. -/
abbrev ClosedUnitInterval := Set.Icc (0 : ℝ) 1

def closedUnitIntervalStart : ClosedUnitInterval := ⟨0, by norm_num⟩

def closedUnitIntervalFinish : ClosedUnitInterval := ⟨1, by norm_num⟩

/-- A finite polygonal model fine enough for the particular circle map
`H`.  All indexing types are explicit finite types, every face is a
cyclic polygon, every edge has one or two incident faces according as it
is a boundary or interior edge, and the incident edge images of each face
lie in one open half-turn ball. -/
structure FinePolygonalModel
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) (H : X → UnitAddCircle) where
  vertexCount : ℕ
  edgeCount : ℕ
  faceCount : ℕ
  faceSize : ℕ
  boundarySize : ℕ
  edgeEnds : Fin edgeCount → Fin vertexCount × Fin vertexCount
  faceEdges : Fin faceCount → Finset (Fin edgeCount)
  boundaryEdges : Finset (Fin edgeCount)
  edgeFaceCount : ∀ e : Fin edgeCount,
    (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
      if e ∈ boundaryEdges then 1 else 2
  faceVertex : Fin faceCount → Fin (faceSize + 1) → Fin vertexCount
  faceEdge : Fin faceCount → Fin (faceSize + 1) → Fin edgeCount
  faceVertex_injective : ∀ f, Function.Injective (faceVertex f)
  faceEdge_injective : ∀ f, Function.Injective (faceEdge f)
  faceEdges_eq : ∀ f, faceEdges f = Finset.univ.image (faceEdge f)
  faceEdge_ends : ∀ f k, edgeEnds (faceEdge f k) =
    (faceVertex f k, faceVertex f (cyclicSucc k))
  boundaryEdge : Fin (boundarySize + 1) → Fin edgeCount
  boundaryEdge_injective : Function.Injective boundaryEdge
  boundaryVertex : Fin (boundarySize + 1) → Fin vertexCount
  boundaryEdge_ends : ∀ k, edgeEnds (boundaryEdge k) =
    (boundaryVertex k, boundaryVertex (cyclicSucc k))
  boundaryEdges_eq : boundaryEdges = Finset.univ.image boundaryEdge
  vertexPoint : Fin vertexCount → X
  edgeToX : Fin edgeCount → ClosedUnitInterval → X
  edgeToX_continuous : ∀ e, Continuous (edgeToX e)
  edgeToX_start : ∀ e, edgeToX e closedUnitIntervalStart =
    vertexPoint (edgeEnds e).1
  edgeToX_finish : ∀ e, edgeToX e closedUnitIntervalFinish =
    vertexPoint (edgeEnds e).2
  faceCenter : Fin faceCount → X
  halfTurn_mesh : ∀ (f : Fin faceCount) (e : Fin edgeCount),
    e ∈ faceEdges f → ∀ x : ClosedUnitInterval,
      dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2
  boundaryParameter : ∀ _k,
    ClosedUnitInterval → ℝ
  boundaryParameter_continuous : ∀ k, Continuous (boundaryParameter k)
  boundaryParameter_start : ∀ k,
    boundaryParameter k closedUnitIntervalStart = cyclicVertexParameter k
  boundaryParameter_finish : ∀ k,
    boundaryParameter k closedUnitIntervalFinish =
      cyclicEdgeFinishParameter k
  boundaryPath : ∀ k x,
    edgeToX (boundaryEdge k) x =
      boundary ((boundaryParameter k x : ℝ) : UnitAddCircle)

/-- The exact fine-triangulation property needed of a surface boundary:
every continuous circle map on the domain has a compatible finite
polygonal model below its half-turn scale. -/
def HasFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    Nonempty (FinePolygonalModel boundary H)

/-- A purely geometric polygonal model at mesh scale `ε`.  We reuse a
`FinePolygonalModel` for the constant circle map to carry exactly the same
finite incidence, edge, and boundary data; the additional field says that
each face center is within `ε` of every point of every incident edge. -/
structure GeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (ε : ℝ) where
  model : FinePolygonalModel boundary (fun _ ↦ (0 : UnitAddCircle))
  mesh : ∀ (f : Fin model.faceCount) (e : Fin model.edgeCount),
    e ∈ model.faceEdges f → ∀ x : ClosedUnitInterval,
      dist (model.faceCenter f) (model.edgeToX e x) < ε

/-- Replace the vacuous constant-map half-turn estimate in a geometric
model by a supplied estimate for a particular circle-valued map. -/
def GeometricPolygonalModel.toFinePolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : GeometricPolygonalModel boundary ε)
    (H : X → UnitAddCircle)
    (hhalf : ∀ (f : Fin D.model.faceCount) (e : Fin D.model.edgeCount),
      e ∈ D.model.faceEdges f → ∀ x : ClosedUnitInterval,
        dist (H (D.model.faceCenter f)) (H (D.model.edgeToX e x)) < 1 / 2) :
    FinePolygonalModel boundary H :=
  { D.model with halfTurn_mesh := hhalf }

/-- Push a geometric polygonal model forward along a continuous map whose
restriction to the boundary agrees with a new parametrization.  The
combinatorics and edge parameters are unchanged; only the vertex, edge, and
face-center locations are transported. -/
def GeometricPolygonalModel.map
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {δ ε : ℝ} (D : GeometricPolygonalModel boundary δ)
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmesh : ∀ (face : Fin D.model.faceCount) (e : Fin D.model.edgeCount),
      e ∈ D.model.faceEdges face → ∀ x : ClosedUnitInterval,
        dist (f (D.model.faceCenter face)) (f (D.model.edgeToX e x)) < ε) :
    GeometricPolygonalModel boundary' ε :=
  { model :=
      { D.model with
        vertexPoint := fun v ↦ f (D.model.vertexPoint v)
        edgeToX := fun e x ↦ f (D.model.edgeToX e x)
        edgeToX_continuous := fun e ↦ hf.comp (D.model.edgeToX_continuous e)
        edgeToX_start := by
          intro e
          rw [D.model.edgeToX_start]
        edgeToX_finish := by
          intro e
          rw [D.model.edgeToX_finish]
        faceCenter := fun face ↦ f (D.model.faceCenter face)
        halfTurn_mesh := by
          intro face e he x
          simp only [D.model.halfTurn_mesh face e he x]
        boundaryPath := by
          intro k x
          rw [hboundary]
          simpa using congrArg f (D.model.boundaryPath k x) }
    mesh := hmesh }

/-- The map-independent surface input: compatible polygonal models exist
at every positive geometric mesh scale. -/
def HasArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (GeometricPolygonalModel boundary ε)

/-- Arbitrarily fine polygonal models transport across continuous maps from a
compact source: choose a sufficiently small source mesh using uniform
continuity, then push the model forward. -/
theorem hasArbitrarilyFinePolygonalModels_of_compact_continuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasArbitrarilyFinePolygonalModels boundary' := by
  intro ε hε
  have hUniform : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.map f hf hboundary ?_⟩
  intro face e he x
  exact hδf (D.mesh face e he x)

/-- Homeomorphic compact images inherit arbitrarily fine polygonal models by
transporting them along the homeomorphism. -/
theorem hasArbitrarilyFinePolygonalModels_of_homeomorph
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasArbitrarilyFinePolygonalModels boundary' :=
  hasArbitrarilyFinePolygonalModels_of_compact_continuous
    e e.continuous_toFun hboundary hmodels

/-- On a compact metric domain, arbitrarily fine geometric polygonal
models provide the map-dependent half-turn models needed by the mod-two
argument.  This discharges the compactness/uniform-continuity step in the
surface triangulation interface. -/
theorem hasFinePolygonalModels_of_arbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasFinePolygonalModels boundary := by
  intro H hH
  have hUniform : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hδH⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (1 / 2) (by norm_num)
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.toFinePolygonalModel H ?_⟩
  intro f e he x
  exact hδH (D.mesh f e he x)

/-- Homeomorphic compact images inherit the map-dependent fine polygonal-model
interface after transporting arbitrarily fine geometric models and then using
uniform continuity. -/
theorem hasFinePolygonalModels_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasFinePolygonalModels boundary' :=
  hasFinePolygonalModels_of_arbitrarilyFine
    (hasArbitrarilyFinePolygonalModels_of_homeomorph e hboundary hmodels)

/-- A bundled fine polygonal model rules out an odd degree on its actual
cyclic boundary.  All auxiliary cuts and lifts are constructed by the
underlying finite-mesh theorem. -/
theorem FinePolygonalModel.no_odd_boundary_degree
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : FinePolygonalModel boundary H) (hH : Continuous H)
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundary) degree)
    (hodd : Odd degree) : False := by
  exact no_odd_degree_of_fine_polygonal_circle_extension
    D.edgeEnds D.faceEdges D.boundaryEdges D.edgeFaceCount
    D.faceVertex D.faceEdge D.faceVertex_injective D.faceEdge_injective
    D.faceEdges_eq D.faceEdge_ends D.boundaryEdge
    D.boundaryEdge_injective D.boundaryVertex D.boundaryEdge_ends
    D.boundaryEdges_eq D.vertexPoint (fun _ ↦ ClosedUnitInterval)
    (fun _ ↦ closedUnitIntervalStart) (fun _ ↦ closedUnitIntervalFinish)
    D.edgeToX D.edgeToX_continuous D.edgeToX_start D.edgeToX_finish
    H hH D.faceCenter D.halfTurn_mesh boundary D.boundaryParameter
    D.boundaryParameter_continuous D.boundaryParameter_start
    D.boundaryParameter_finish D.boundaryPath degree hdegree hodd

/-- Fine polygonal models imply the abstract odd boundary-degree
obstruction used by the coverage theorems. -/
theorem hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  obtain ⟨D⟩ := hfine H hH
  exact D.no_odd_boundary_degree hH degree hdegree hodd

/-- A compact metric domain with arbitrarily fine compatible geometric
models has the odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    (hasFinePolygonalModels_of_arbitrarilyFine hmodels)

/-- A boundary-respecting homeomorphism from a compact source carrying
arbitrarily fine polygonal models transfers the odd boundary-degree
obstruction to the target boundary.  This is the exact topological input
needed by the coverage theorems once a source-space triangulation theorem is
available. -/
theorem hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary' :=
  hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    (hasFinePolygonalModels_of_homeomorph_arbitrarilyFine e hboundary hmodels)

end

end GromovFilling
