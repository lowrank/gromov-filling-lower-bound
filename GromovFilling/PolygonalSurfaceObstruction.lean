import GromovFilling.BoundarySubdivisionDegree

/-!
# Circle extensions over finite polygonal surfaces

This combines the continuous local-phase construction with the natural
incidence data of a finite polygonal surface and the cyclic boundary turn
formula.  It is the complete finite-complex form of the topological
contradiction in Lemma 5.4.
-/

namespace GromovFilling

noncomputable section

/-- An odd-degree circle map cannot extend across finite polygonal surface
data whose edge map admits facewise avoided cuts. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_face_cuts
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    {faceSize : ℕ} (faceVertex : F → Fin (faceSize + 1) → V)
    (faceEdge : F → Fin (faceSize + 1) → E)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      (faceVertex f k, faceVertex f (cyclicSucc k)))
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (hboundary : boundaryEdges = Finset.univ.image boundaryEdge)
    (vertexPoint : V → X)
    (EdgePoint : E → Type*)
    [∀ e, TopologicalSpace (EdgePoint e)]
    [∀ e, PreconnectedSpace (EdgePoint e)]
    (edgeStart edgeFinish : ∀ e, EdgePoint e)
    (edgeToX : ∀ e, EdgePoint e → X)
    (hedgeToX : ∀ e, Continuous (edgeToX e))
    (hedgeStart : ∀ e, edgeToX e (edgeStart e) =
      vertexPoint (edgeEnds e).1)
    (hedgeFinish : ∀ e, edgeToX e (edgeFinish e) =
      vertexPoint (edgeEnds e).2)
    (H : X → UnitAddCircle) (hH : Continuous H)
    (cut : F → ℝ)
    (hcut : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x, H (edgeToX e x) ≠ (cut f : UnitAddCircle))
    (vertexLift : V → ℝ)
    (hvertexLift : ∀ v,
      (vertexLift v : UnitAddCircle) = H (vertexPoint v))
    (edgeLift : ∀ e, EdgePoint e → ℝ)
    (hedgeLift : ∀ e, Continuous (edgeLift e))
    (hedgeLiftProjects : ∀ e x,
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x))
    (turn : E → ℤ)
    (hturn : ∀ e : E, (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2))
    (degree : ℤ)
    (hboundaryTurn : ∀ k,
      turn (boundaryEdge k) = cyclicDegreeTurn degree k)
    (hodd : Odd degree) : False := by
  apply no_odd_degree_of_triangulated_circle_map_with_face_cuts
    edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_cyclic_face_data edgeEnds faceEdges faceVertex faceEdge
      hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift
    edgeLift hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hboundaryTurn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

end

end GromovFilling
