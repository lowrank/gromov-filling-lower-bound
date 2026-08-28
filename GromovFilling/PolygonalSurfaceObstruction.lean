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

/-- The total turn of edge lifts along a cyclically parametrized boundary
is minus the degree of the boundary map.  The edge lifts may be chosen
independently and the vertex representatives are arbitrary: connectedness
of each boundary edge makes the lift discrepancy constant, while the
vertex discrepancies telescope around the cycle. -/
theorem boundary_edge_turn_sum_eq_neg_degree
    {X V E : Type*} [TopologicalSpace X]
    [Fintype E] [DecidableEq E]
    (edgeEnds : E → V × V)
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
    (EdgePoint : E → Type*)
    [∀ e, TopologicalSpace (EdgePoint e)]
    [∀ e, PreconnectedSpace (EdgePoint e)]
    (edgeStart edgeFinish : ∀ e, EdgePoint e)
    (edgeToX : ∀ e, EdgePoint e → X)
    (H : X → UnitAddCircle)
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (vertexLift : V → ℝ)
    (edgeLift : ∀ e, EdgePoint e → ℝ)
    (hedgeLift : ∀ e, Continuous (edgeLift e))
    (hedgeLiftProjects : ∀ e x,
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x))
    (turn : E → ℤ)
    (hturn : ∀ e : E, (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree) :
    ∑ e ∈ Finset.univ.image boundaryEdge, turn e = -degree := by
  obtain ⟨lift, hlift, hliftProjects, hperiod⟩ := hdegree
  have hedgeTurn (k : Fin (boundarySize + 1)) :
      (turn (boundaryEdge k) : ℝ) =
        (lift (cyclicVertexParameter k) - vertexLift (boundaryVertex k)) -
          (lift (cyclicEdgeFinishParameter k) -
            vertexLift (boundaryVertex (cyclicSucc k))) := by
    have hcompare := edge_turn_eq_face_transition
      (edgeLift (boundaryEdge k))
      (lift ∘ boundaryParameter k)
      (hedgeLift (boundaryEdge k))
      (hlift.comp (hboundaryParameter k))
      (fun x ↦ by
        rw [hedgeLiftProjects, Function.comp_apply, hliftProjects,
          Function.comp_apply, hboundaryPath])
      (edgeStart (boundaryEdge k)) (edgeFinish (boundaryEdge k))
      (vertexLift (edgeEnds (boundaryEdge k)).1)
      (vertexLift (edgeEnds (boundaryEdge k)).2)
      (turn (boundaryEdge k)) (hturn (boundaryEdge k))
    rw [Function.comp_apply, Function.comp_apply,
      hboundaryParameterStart, hboundaryParameterFinish,
      hboundaryEnds] at hcompare
    exact hcompare
  rw [Finset.sum_image (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
  have hreal :
      (∑ k : Fin (boundarySize + 1), (turn (boundaryEdge k) : ℝ)) =
        (-degree : ℝ) := by
    calc
      (∑ k : Fin (boundarySize + 1), (turn (boundaryEdge k) : ℝ)) =
          ∑ k : Fin (boundarySize + 1),
            ((lift (cyclicVertexParameter k) -
                vertexLift (boundaryVertex k)) -
              (lift (cyclicEdgeFinishParameter k) -
                vertexLift (boundaryVertex (cyclicSucc k)))) := by
            apply Finset.sum_congr rfl
            intro k _hk
            exact hedgeTurn k
      _ = (-degree : ℝ) := sum_cyclic_endpoint_turn lift degree hperiod
        (vertexLift ∘ boundaryVertex)
  exact_mod_cast hreal

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

/-- Degree-aware finite polygonal obstruction.  Unlike the preceding
turn-data theorem, this statement starts from the degree of the actual
circle map on a parametrized boundary.  The boundary turn sum, including
its sign, is derived internally by comparing lifts on every boundary
edge. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_boundary_degree
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
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  apply no_odd_degree_of_triangulated_circle_map_with_face_cuts
    edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_cyclic_face_data edgeEnds faceEdges faceVertex faceEdge
      hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift
    hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary]
    exact boundary_edge_turn_sum_eq_neg_degree edgeEnds boundaryEdge
      hboundaryEdge boundaryVertex hboundaryEnds EdgePoint edgeStart
      edgeFinish edgeToX H boundaryMap boundaryParameter
      hboundaryParameter hboundaryParameterStart hboundaryParameterFinish
      hboundaryPath vertexLift edgeLift hedgeLift hedgeLiftProjects turn
      hturn degree hdegree
  · exact hodd.neg

/-- Quantitative mesh form of the finite polygonal obstruction.  A face
center whose incident edges all map into an open half-turn ball supplies
the avoided cut required by
`no_odd_degree_of_polygonal_circle_extension_with_face_cuts`; the cut is
therefore no longer part of the input data. -/
theorem no_odd_degree_of_polygonal_circle_extension_of_small_mesh
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
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
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  exact no_odd_degree_of_polygonal_circle_extension_with_face_cuts
    edgeEnds faceEdges boundaryEdges hcount faceVertex faceEdge
    hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge hboundaryEdge
    hboundary vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift
    hedgeLift hedgeLiftProjects turn hturn degree hboundaryTurn hodd

/-- Fully assembled finite-mesh version of the topological contradiction.
The hypotheses now contain only the polygonal surface, its cyclic boundary
parametrization, the continuous circle extension, and the half-turn mesh
estimate.  Face cuts, vertex representatives, edge lifts, integer turns,
and the boundary turn sum are all constructed in the proof. -/
theorem no_odd_degree_of_fine_polygonal_circle_extension
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
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  classical
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  choose vertexLift _hvertexIco hvertexLift using fun v ↦
    AddCircle.eq_coe_Ico (H (vertexPoint v))
  have hedgeFaceExists (e : E) : ∃ f : F, e ∈ faceEdges f := by
    have hcard : 0 <
        (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card := by
      rw [hcount e]
      split <;> omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
    exact ⟨f, (Finset.mem_filter.mp hf).2⟩
  choose edgeFace hedgeFace using hedgeFaceExists
  let edgeLift : ∀ e, EdgePoint e → ℝ := fun e ↦
    circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
  have hedgeLift (e : E) : Continuous (edgeLift e) := by
    exact continuous_circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
      (hH.comp (hedgeToX e)) (hcut (edgeFace e) e (hedgeFace e))
  have hedgeLiftProjects (e : E) (x : EdgePoint e) :
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x) := by
    exact circlePhaseAway_projects (cut (edgeFace e))
      (H ∘ edgeToX e) x
  have hsameStart (e : E) :
      (edgeLift e (edgeStart e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).1 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeStart, hvertexLift]
  have hsameFinish (e : E) :
      (edgeLift e (edgeFinish e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).2 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeFinish, hvertexLift]
  choose startOffset hstartOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeStart e)) (vertexLift (edgeEnds e).1)
      (hsameStart e)
  choose finishOffset hfinishOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeFinish e)) (vertexLift (edgeEnds e).2)
      (hsameFinish e)
  let turn : E → ℤ := fun e ↦ startOffset e - finishOffset e
  have hturn (e : E) : (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2) := by
    change ((startOffset e - finishOffset e : ℤ) : ℝ) = _
    rw [Int.cast_sub, hstartOffset, hfinishOffset]
  exact no_odd_degree_of_polygonal_circle_extension_with_boundary_degree
    edgeEnds faceEdges boundaryEdges hcount faceVertex faceEdge
    hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge hboundaryEdge
    boundaryVertex hboundaryEnds hboundary vertexPoint EdgePoint edgeStart
    edgeFinish edgeToX hedgeToX hedgeStart hedgeFinish H hH cut hcut
    vertexLift hvertexLift edgeLift hedgeLift hedgeLiftProjects turn hturn
    boundaryMap boundaryParameter hboundaryParameter
    hboundaryParameterStart hboundaryParameterFinish hboundaryPath degree
    hdegree hodd

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_with_face_cuts`. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_face_cuts_variable
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
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
    (faceEven_of_variable_cyclic_face_data edgeEnds faceEdges faceSize
      faceVertex faceEdge hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift
    edgeLift hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hboundaryTurn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_with_boundary_degree`. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_boundary_degree_variable
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      (faceVertex f k, faceVertex f (cyclicSucc k)))
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  apply no_odd_degree_of_triangulated_circle_map_with_face_cuts
    edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_variable_cyclic_face_data edgeEnds faceEdges faceSize
      faceVertex faceEdge hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift
    hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary]
    exact boundary_edge_turn_sum_eq_neg_degree edgeEnds boundaryEdge
      hboundaryEdge boundaryVertex hboundaryEnds EdgePoint edgeStart
      edgeFinish edgeToX H boundaryMap boundaryParameter
      hboundaryParameter hboundaryParameterStart hboundaryParameterFinish
      hboundaryPath vertexLift edgeLift hedgeLift hedgeLiftProjects turn
      hturn degree hdegree
  · exact hodd.neg

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_of_small_mesh`. -/
theorem no_odd_degree_of_polygonal_circle_extension_of_small_mesh_variable
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
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
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  exact no_odd_degree_of_polygonal_circle_extension_with_face_cuts_variable
    edgeEnds faceEdges boundaryEdges hcount faceSize faceVertex faceEdge
    hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge hboundaryEdge
    hboundary vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift
    hedgeLift hedgeLiftProjects turn hturn degree hboundaryTurn hodd

/-- Variable-face-size version of
`no_odd_degree_of_fine_polygonal_circle_extension`. -/
theorem no_odd_degree_of_fine_polygonal_circle_extension_variable
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      (faceVertex f k, faceVertex f (cyclicSucc k)))
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  classical
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  choose vertexLift _hvertexIco hvertexLift using fun v ↦
    AddCircle.eq_coe_Ico (H (vertexPoint v))
  have hedgeFaceExists (e : E) : ∃ f : F, e ∈ faceEdges f := by
    have hcard : 0 <
        (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card := by
      rw [hcount e]
      split <;> omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
    exact ⟨f, (Finset.mem_filter.mp hf).2⟩
  choose edgeFace hedgeFace using hedgeFaceExists
  let edgeLift : ∀ e, EdgePoint e → ℝ := fun e ↦
    circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
  have hedgeLift (e : E) : Continuous (edgeLift e) := by
    exact continuous_circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
      (hH.comp (hedgeToX e)) (hcut (edgeFace e) e (hedgeFace e))
  have hedgeLiftProjects (e : E) (x : EdgePoint e) :
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x) := by
    exact circlePhaseAway_projects (cut (edgeFace e))
      (H ∘ edgeToX e) x
  have hsameStart (e : E) :
      (edgeLift e (edgeStart e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).1 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeStart, hvertexLift]
  have hsameFinish (e : E) :
      (edgeLift e (edgeFinish e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).2 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeFinish, hvertexLift]
  choose startOffset hstartOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeStart e)) (vertexLift (edgeEnds e).1)
      (hsameStart e)
  choose finishOffset hfinishOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeFinish e)) (vertexLift (edgeEnds e).2)
      (hsameFinish e)
  let turn : E → ℤ := fun e ↦ startOffset e - finishOffset e
  have hturn (e : E) : (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2) := by
    change ((startOffset e - finishOffset e : ℤ) : ℝ) = _
    rw [Int.cast_sub, hstartOffset, hfinishOffset]
  exact no_odd_degree_of_polygonal_circle_extension_with_boundary_degree_variable
    edgeEnds faceEdges boundaryEdges hcount faceSize faceVertex faceEdge
    hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge hboundaryEdge
    boundaryVertex hboundaryEnds hboundary vertexPoint EdgePoint edgeStart
    edgeFinish edgeToX hedgeToX hedgeStart hedgeFinish H hH cut hcut
    vertexLift hvertexLift edgeLift hedgeLift hedgeLiftProjects turn hturn
    boundaryMap boundaryParameter hboundaryParameter
    hboundaryParameterStart hboundaryParameterFinish hboundaryPath degree
    hdegree hodd

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_with_face_cuts`, allowing each
face-edge occurrence to traverse its global edge in either local direction. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_face_cuts_variable_with_edge_directions
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (faceEdgeForward : ∀ f, Fin (faceSize f + 1) → Bool)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      if faceEdgeForward f k then
        (faceVertex f k, faceVertex f (cyclicSucc k))
      else
        (faceVertex f (cyclicSucc k), faceVertex f k))
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
    (faceEven_of_variable_cyclic_face_data_with_edge_directions
      edgeEnds faceEdges faceSize faceVertex faceEdge faceEdgeForward
      hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift
    edgeLift hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hboundaryTurn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_with_boundary_degree`, allowing
face-local edge directions. -/
theorem no_odd_degree_of_polygonal_circle_extension_with_boundary_degree_variable_with_edge_directions
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (faceEdgeForward : ∀ f, Fin (faceSize f + 1) → Bool)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      if faceEdgeForward f k then
        (faceVertex f k, faceVertex f (cyclicSucc k))
      else
        (faceVertex f (cyclicSucc k), faceVertex f k))
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  apply no_odd_degree_of_triangulated_circle_map_with_face_cuts
    edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_variable_cyclic_face_data_with_edge_directions
      edgeEnds faceEdges faceSize faceVertex faceEdge faceEdgeForward
      hfaceVertex hfaceEdge hfaceEdges hends)
    vertexPoint EdgePoint edgeStart edgeFinish edgeToX hedgeToX
    hedgeStart hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift
    hedgeLift hedgeLiftProjects turn hturn (-degree)
  · rw [hboundary]
    exact boundary_edge_turn_sum_eq_neg_degree edgeEnds boundaryEdge
      hboundaryEdge boundaryVertex hboundaryEnds EdgePoint edgeStart
      edgeFinish edgeToX H boundaryMap boundaryParameter
      hboundaryParameter hboundaryParameterStart hboundaryParameterFinish
      hboundaryPath vertexLift edgeLift hedgeLift hedgeLiftProjects turn
      hturn degree hdegree
  · exact hodd.neg

/-- Variable-face-size version of
`no_odd_degree_of_polygonal_circle_extension_of_small_mesh`, allowing
face-local edge directions. -/
theorem no_odd_degree_of_polygonal_circle_extension_of_small_mesh_variable_with_edge_directions
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (faceEdgeForward : ∀ f, Fin (faceSize f + 1) → Bool)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      if faceEdgeForward f k then
        (faceVertex f k, faceVertex f (cyclicSucc k))
      else
        (faceVertex f (cyclicSucc k), faceVertex f k))
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
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
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  exact no_odd_degree_of_polygonal_circle_extension_with_face_cuts_variable_with_edge_directions
    edgeEnds faceEdges boundaryEdges hcount faceSize faceVertex faceEdge
    faceEdgeForward hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge
    hboundaryEdge hboundary vertexPoint EdgePoint edgeStart edgeFinish
    edgeToX hedgeToX hedgeStart hedgeFinish H hH cut hcut vertexLift
    hvertexLift edgeLift hedgeLift hedgeLiftProjects turn hturn degree
    hboundaryTurn hodd

/-- Variable-face-size version of
`no_odd_degree_of_fine_polygonal_circle_extension`, allowing face-local edge
 directions. -/
theorem no_odd_degree_of_fine_polygonal_circle_extension_variable_with_edge_directions
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (faceEdgeForward : ∀ f, Fin (faceSize f + 1) → Bool)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      if faceEdgeForward f k then
        (faceVertex f k, faceVertex f (cyclicSucc k))
      else
        (faceVertex f (cyclicSucc k), faceVertex f k))
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (boundaryVertex : Fin (boundarySize + 1) → V)
    (hboundaryEnds : ∀ k, edgeEnds (boundaryEdge k) =
      (boundaryVertex k, boundaryVertex (cyclicSucc k)))
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
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x : EdgePoint e,
        dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2)
    (boundaryMap : UnitAddCircle → X)
    (boundaryParameter : ∀ k,
      EdgePoint (boundaryEdge k) → ℝ)
    (hboundaryParameter : ∀ k, Continuous (boundaryParameter k))
    (hboundaryParameterStart : ∀ k,
      boundaryParameter k (edgeStart (boundaryEdge k)) =
        cyclicVertexParameter k)
    (hboundaryParameterFinish : ∀ k,
      boundaryParameter k (edgeFinish (boundaryEdge k)) =
        cyclicEdgeFinishParameter k)
    (hboundaryPath : ∀ k x,
      edgeToX (boundaryEdge k) x =
        boundaryMap ((boundaryParameter k x : ℝ) : UnitAddCircle))
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundaryMap) degree)
    (hodd : Odd degree) : False := by
  classical
  obtain ⟨cut, hcut⟩ := exists_face_cuts_of_small_edge_images
    faceEdges EdgePoint edgeToX H faceCenter hsmall
  choose vertexLift _hvertexIco hvertexLift using fun v ↦
    AddCircle.eq_coe_Ico (H (vertexPoint v))
  have hedgeFaceExists (e : E) : ∃ f : F, e ∈ faceEdges f := by
    have hcard : 0 <
        (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card := by
      rw [hcount e]
      split <;> omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
    exact ⟨f, (Finset.mem_filter.mp hf).2⟩
  choose edgeFace hedgeFace using hedgeFaceExists
  let edgeLift : ∀ e, EdgePoint e → ℝ := fun e ↦
    circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
  have hedgeLift (e : E) : Continuous (edgeLift e) := by
    exact continuous_circlePhaseAway (cut (edgeFace e)) (H ∘ edgeToX e)
      (hH.comp (hedgeToX e)) (hcut (edgeFace e) e (hedgeFace e))
  have hedgeLiftProjects (e : E) (x : EdgePoint e) :
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x) := by
    exact circlePhaseAway_projects (cut (edgeFace e))
      (H ∘ edgeToX e) x
  have hsameStart (e : E) :
      (edgeLift e (edgeStart e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).1 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeStart, hvertexLift]
  have hsameFinish (e : E) :
      (edgeLift e (edgeFinish e) : UnitAddCircle) =
        (vertexLift (edgeEnds e).2 : UnitAddCircle) := by
    rw [hedgeLiftProjects, hedgeFinish, hvertexLift]
  choose startOffset hstartOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeStart e)) (vertexLift (edgeEnds e).1)
      (hsameStart e)
  choose finishOffset hfinishOffset using fun e ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift e (edgeFinish e)) (vertexLift (edgeEnds e).2)
      (hsameFinish e)
  let turn : E → ℤ := fun e ↦ startOffset e - finishOffset e
  have hturn (e : E) : (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2) := by
    change ((startOffset e - finishOffset e : ℤ) : ℝ) = _
    rw [Int.cast_sub, hstartOffset, hfinishOffset]
  exact no_odd_degree_of_polygonal_circle_extension_with_boundary_degree_variable_with_edge_directions
    edgeEnds faceEdges boundaryEdges hcount faceSize faceVertex faceEdge
    faceEdgeForward hfaceVertex hfaceEdge hfaceEdges hends boundaryEdge
    hboundaryEdge boundaryVertex hboundaryEnds hboundary vertexPoint
    EdgePoint edgeStart edgeFinish edgeToX hedgeToX hedgeStart
    hedgeFinish H hH cut hcut vertexLift hvertexLift edgeLift hedgeLift
    hedgeLiftProjects turn hturn boundaryMap boundaryParameter
    hboundaryParameter hboundaryParameterStart hboundaryParameterFinish
    hboundaryPath degree hdegree hodd

end

end GromovFilling
