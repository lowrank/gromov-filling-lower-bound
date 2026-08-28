import GromovFilling.CircleDegree

/-!
# Degree on a cyclic boundary subdivision

This file connects the real-lift definition of circle degree with the
integer edge-turn sum used by the finite mod-2 surface obstruction.
-/

namespace GromovFilling

noncomputable section

/-- Cyclic successor on a nonempty finite set. -/
def cyclicSucc {n : ℕ} (k : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(k.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

@[simp]
theorem cyclicSucc_last {n : ℕ} :
    cyclicSucc (Fin.last n) = (0 : Fin (n + 1)) := by
  apply Fin.ext
  simp [cyclicSucc]

theorem cyclicSucc_val_of_ne_last {n : ℕ} (k : Fin (n + 1))
    (hk : k ≠ Fin.last n) : (cyclicSucc k).val = k.val + 1 := by
  unfold cyclicSucc
  simp only
  apply Nat.mod_eq_of_lt
  have hkval : k.val ≠ n := by
    intro hval
    apply hk
    apply Fin.ext
    simpa using hval
  omega

theorem cyclicSucc_injective {n : ℕ} :
    Function.Injective (cyclicSucc : Fin (n + 1) → Fin (n + 1)) := by
  intro k l hkl
  by_cases hk : k = Fin.last n
  · subst k
    by_cases hl : l = Fin.last n
    · exact hl.symm
    · have hval := congrArg Fin.val hkl
      rw [cyclicSucc_last, cyclicSucc_val_of_ne_last l hl] at hval
      simp at hval
  · by_cases hl : l = Fin.last n
    · subst l
      have hval := congrArg Fin.val hkl
      rw [cyclicSucc_last, cyclicSucc_val_of_ne_last k hk] at hval
      simp at hval
    · apply Fin.ext
      have hval := congrArg Fin.val hkl
      rw [cyclicSucc_val_of_ne_last k hk,
        cyclicSucc_val_of_ne_last l hl] at hval
      omega

/-- Cyclic predecessor on a nonempty finite set. -/
noncomputable def cyclicPred {n : ℕ} : Fin (n + 1) → Fin (n + 1) :=
  (Equiv.ofBijective (cyclicSucc : Fin (n + 1) → Fin (n + 1)) (Finite.injective_iff_bijective.mp cyclicSucc_injective)).symm

@[simp] theorem cyclicSucc_cyclicPred {n : ℕ} (k : Fin (n + 1)) :
    cyclicSucc (cyclicPred k) = k := by
  exact (Equiv.ofBijective (cyclicSucc : Fin (n + 1) → Fin (n + 1)) (Finite.injective_iff_bijective.mp cyclicSucc_injective)).apply_symm_apply k

@[simp] theorem cyclicPred_cyclicSucc {n : ℕ} (k : Fin (n + 1)) :
    cyclicPred (cyclicSucc k) = k := by
  exact (Equiv.ofBijective (cyclicSucc : Fin (n + 1) → Fin (n + 1)) (Finite.injective_iff_bijective.mp cyclicSucc_injective)).symm_apply_apply k

@[simp] theorem cyclicPred_zero {n : ℕ} :
    cyclicPred (0 : Fin (n + 1)) = Fin.last n := by
  apply cyclicSucc_injective
  simp [cyclicSucc_last]

theorem cyclicPred_injective {n : ℕ} :
    Function.Injective (cyclicPred : Fin (n + 1) → Fin (n + 1)) := by
  intro k l hkl
  have h := congrArg cyclicSucc hkl
  simpa using h

theorem cyclicSucc_bijective {n : ℕ} :
    Function.Bijective (cyclicSucc : Fin (n + 1) → Fin (n + 1)) :=
  Finite.injective_iff_bijective.mp cyclicSucc_injective

/-- Every vertex of a cyclic polygon occurs twice in its unoriented edge
boundary, hence has zero incidence over `ZMod 2`. -/
theorem cyclic_face_vertex_incidence_even {n : ℕ} (v : Fin (n + 1)) :
    (∑ k : Fin (n + 1),
      ((if v = k then (1 : ZMod 2) else 0) +
        if v = cyclicSucc k then (1 : ZMod 2) else 0)) = 0 := by
  rw [Finset.sum_add_distrib]
  have hstart :
      (∑ k : Fin (n + 1), if v = k then (1 : ZMod 2) else 0) = 1 := by
    simp
  have hfinish :
      (∑ k : Fin (n + 1),
        if v = cyclicSucc k then (1 : ZMod 2) else 0) = 1 := by
    calc
      (∑ k : Fin (n + 1),
          if v = cyclicSucc k then (1 : ZMod 2) else 0) =
          ∑ k : Fin (n + 1), if v = k then (1 : ZMod 2) else 0 :=
        (cyclicSucc_bijective.sum_comp
          (fun k : Fin (n + 1) ↦
            if v = k then (1 : ZMod 2) else 0))
      _ = 1 := hstart
  rw [hstart, hfinish]
  change (2 : ZMod 2) = 0
  exact ZMod.natCast_self 2

/-- The same even-incidence fact after injectively labelling the vertices
of the polygon by vertices of a global cell complex. -/
theorem mapped_cyclic_face_vertex_incidence_even
    {V : Type*} [DecidableEq V] {n : ℕ} (faceVertex : Fin (n + 1) → V)
    (hfaceVertex : Function.Injective faceVertex) (v : V) :
    (∑ k : Fin (n + 1),
      ((if v = faceVertex k then (1 : ZMod 2) else 0) +
        if v = faceVertex (cyclicSucc k) then (1 : ZMod 2) else 0)) = 0 := by
  by_cases hv : v ∈ Set.range faceVertex
  · obtain ⟨w, rfl⟩ := hv
    simpa [hfaceVertex.eq_iff] using cyclic_face_vertex_incidence_even w
  · have hne (k : Fin (n + 1)) : v ≠ faceVertex k := by
      intro hvk
      exact hv ⟨k, hvk.symm⟩
    simp [hne]

/-- Cyclic vertex/edge data for every face discharge the `hfaceEven`
hypothesis of the mod-2 obstruction.  Triangulations use `n = 2`, while
the statement also applies to polygonal cell decompositions. -/
theorem faceEven_of_cyclic_face_data
    {V E F : Type*} [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    {n : ℕ} (faceVertex : F → Fin (n + 1) → V)
    (faceEdge : F → Fin (n + 1) → E)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      (faceVertex f k, faceVertex f (cyclicSucc k))) :
    ∀ (f : F) (v : V),
      (∑ e ∈ faceEdges f,
        ((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
          if v = (edgeEnds e).2 then (1 : ZMod 2) else 0)) = 0 := by
  intro f v
  rw [hfaceEdges f, Finset.sum_image
    (fun x _hx y _hy hxy ↦ hfaceEdge f hxy)]
  simp_rw [hends]
  exact mapped_cyclic_face_vertex_incidence_even
    (faceVertex f) (hfaceVertex f) v

/-- The same cyclic-face incidence discharge, but allowing each face to
have its own cyclic size. -/
theorem faceEven_of_variable_cyclic_face_data
    {V E F : Type*} [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (faceSize : F → ℕ)
    (faceVertex : ∀ f, Fin (faceSize f + 1) → V)
    (faceEdge : ∀ f, Fin (faceSize f + 1) → E)
    (hfaceVertex : ∀ f, Function.Injective (faceVertex f))
    (hfaceEdge : ∀ f, Function.Injective (faceEdge f))
    (hfaceEdges : ∀ f, faceEdges f = Finset.univ.image (faceEdge f))
    (hends : ∀ f k, edgeEnds (faceEdge f k) =
      (faceVertex f k, faceVertex f (cyclicSucc k))) :
    ∀ (f : F) (v : V),
      (∑ e ∈ faceEdges f,
        ((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
          if v = (edgeEnds e).2 then (1 : ZMod 2) else 0)) = 0 := by
  intro f v
  rw [hfaceEdges f, Finset.sum_image
    (fun x _hx y _hy hxy ↦ hfaceEdge f hxy)]
  simp_rw [hends]
  exact mapped_cyclic_face_vertex_incidence_even
    (faceVertex f) (hfaceVertex f) v

/-- The usual surface incidence rule—one incident face for a boundary
edge and two for an interior edge—implies the mod-2 incidence identity
used by combinatorial Stokes. -/
theorem modTwo_incidence_of_face_count
    {E F : Type*} [Fintype F] [DecidableEq E]
    (faceEdges : F → Finset E) (boundaryEdges : Finset E)
    (hcount : ∀ e : E,
      (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
        if e ∈ boundaryEdges then 1 else 2) :
    ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0 := by
  classical
  intro e
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcount e]
  by_cases he : e ∈ boundaryEdges
  · simp [he]
  · simp only [he, ↓reduceIte]
    exact ZMod.natCast_self 2

/-- The real parameter assigned to a boundary vertex. -/
def cyclicVertexParameter {n : ℕ} (k : Fin (n + 1)) : ℝ :=
  k.val / (n + 1 : ℕ)

/-- The terminal parameter of the edge indexed by `k`; for the last edge
this is `1`, before identifying it with the vertex at `0`. -/
def cyclicEdgeFinishParameter {n : ℕ} (k : Fin (n + 1)) : ℝ :=
  (k.val + 1) / (n + 1 : ℕ)

/-- All cyclic edge turns vanish except the closing edge, whose turn is
the negative of the degree with the endpoint convention used in
`RadialProjection`. -/
def cyclicDegreeTurn {n : ℕ} (d : ℤ) (k : Fin (n + 1)) : ℤ :=
  if k = Fin.last n then -d else 0

theorem cyclicDegreeTurn_endpoint_identity
    {n : ℕ} (lift : ℝ → ℝ) (d : ℤ)
    (hperiod : ∀ t : ℝ, lift (t + 1) = lift t + (d : ℝ))
    (k : Fin (n + 1)) :
    (cyclicDegreeTurn d k : ℝ) =
      (lift (cyclicVertexParameter k) -
        lift (cyclicVertexParameter k)) -
      (lift (cyclicEdgeFinishParameter k) -
        lift (cyclicVertexParameter (cyclicSucc k))) := by
  by_cases hk : k = Fin.last n
  · subst k
    have hden : (n + 1 : ℝ) ≠ 0 := by positivity
    have hfinish : cyclicEdgeFinishParameter (Fin.last n) = 1 := by
      unfold cyclicEdgeFinishParameter
      simp only [Fin.val_last]
      push_cast
      field_simp
    have hstart : cyclicVertexParameter
        (cyclicSucc (Fin.last n)) = 0 := by
      rw [cyclicSucc_last]
      simp [cyclicVertexParameter]
    have hperiod0 : lift 1 = lift 0 + (d : ℝ) := by
      simpa using hperiod 0
    rw [hfinish, hstart]
    simp [cyclicDegreeTurn]
    linarith
  · have hsucc : cyclicVertexParameter (cyclicSucc k) =
        cyclicEdgeFinishParameter k := by
      unfold cyclicVertexParameter cyclicEdgeFinishParameter
      rw [cyclicSucc_val_of_ne_last k hk]
      push_cast
      rfl
    rw [hsucc]
    simp [cyclicDegreeTurn, hk]

/-- The edge-turn sum of a cyclic subdivision is exactly minus the
integer circle degree. -/
theorem sum_cyclicDegreeTurn {n : ℕ} (d : ℤ) :
    ∑ k : Fin (n + 1), cyclicDegreeTurn d k = -d := by
  classical
  simp [cyclicDegreeTurn]

/-- The cyclic endpoint-turn sum is independent of the chosen real
representatives at the vertices.  The representative corrections cancel
because cyclic successor is a permutation; the sole surviving term is
the period jump of the degree lift. -/
theorem sum_cyclic_endpoint_turn
    {n : ℕ} (lift : ℝ → ℝ) (d : ℤ)
    (hperiod : ∀ t : ℝ, lift (t + 1) = lift t + (d : ℝ))
    (vertexLift : Fin (n + 1) → ℝ) :
    (∑ k : Fin (n + 1),
      ((lift (cyclicVertexParameter k) - vertexLift k) -
        (lift (cyclicEdgeFinishParameter k) -
          vertexLift (cyclicSucc k)))) = (-d : ℝ) := by
  let correction : Fin (n + 1) → ℝ := fun k ↦
    lift (cyclicVertexParameter k) - vertexLift k
  calc
    (∑ k : Fin (n + 1),
        ((lift (cyclicVertexParameter k) - vertexLift k) -
          (lift (cyclicEdgeFinishParameter k) -
            vertexLift (cyclicSucc k)))) =
        ∑ k : Fin (n + 1),
          ((cyclicDegreeTurn d k : ℝ) +
            (correction k - correction (cyclicSucc k))) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [cyclicDegreeTurn_endpoint_identity lift d hperiod k]
      simp only [correction]
      ring
    _ = (∑ k : Fin (n + 1), (cyclicDegreeTurn d k : ℝ)) +
        ((∑ k : Fin (n + 1), correction k) -
          ∑ k : Fin (n + 1), correction (cyclicSucc k)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ k : Fin (n + 1), (cyclicDegreeTurn d k : ℝ) := by
      rw [cyclicSucc_bijective.sum_comp correction]
      ring
    _ = (-d : ℝ) := by
      rw [← Int.cast_sum, sum_cyclicDegreeTurn]
      norm_num

/-- A degree lift canonically supplies the boundary edge lifts and turn
sum required by the combinatorial mod-2 obstruction, for every nonempty
cyclic subdivision. -/
theorem HasCircleDegree.cyclicSubdivision
    {H : UnitAddCircle → UnitAddCircle} {d : ℤ}
    (hdegree : HasCircleDegree H d) (n : ℕ) :
    ∃ lift : ℝ → ℝ,
      Continuous lift ∧
      (∀ t : ℝ, (lift t : UnitAddCircle) = H (t : UnitAddCircle)) ∧
      (∀ k : Fin (n + 1),
        (cyclicDegreeTurn d k : ℝ) =
          (lift (cyclicVertexParameter k) -
            lift (cyclicVertexParameter k)) -
          (lift (cyclicEdgeFinishParameter k) -
            lift (cyclicVertexParameter (cyclicSucc k)))) ∧
      (∑ k : Fin (n + 1), cyclicDegreeTurn d k) = -d := by
  obtain ⟨lift, hlift, hprojects, hperiod⟩ := hdegree
  exact ⟨lift, hlift, hprojects,
    cyclicDegreeTurn_endpoint_identity lift d hperiod,
    sum_cyclicDegreeTurn d⟩

/-- Complex-circle version of `HasCircleDegree.cyclicSubdivision`. -/
theorem HasComplexCircleDegree.cyclicSubdivision
    {H : UnitAddCircle → ComplexUnitCircle} {d : ℤ}
    (hdegree : HasComplexCircleDegree H d) (n : ℕ) :
    ∃ lift : ℝ → ℝ,
      Continuous lift ∧
      (∀ t : ℝ, (lift t : UnitAddCircle) =
        unitAddCircleEquivComplexUnitCircle.symm (H (t : UnitAddCircle))) ∧
      (∀ k : Fin (n + 1),
        (cyclicDegreeTurn d k : ℝ) =
          (lift (cyclicVertexParameter k) -
            lift (cyclicVertexParameter k)) -
          (lift (cyclicEdgeFinishParameter k) -
            lift (cyclicVertexParameter (cyclicSucc k)))) ∧
      (∑ k : Fin (n + 1), cyclicDegreeTurn d k) = -d := by
  exact HasCircleDegree.cyclicSubdivision hdegree n

/-- Combinatorial Stokes specialized to a cyclically indexed boundary.
The boundary-degree equality is derived from the cyclic turn formula
rather than left as a separate hypothesis. -/
theorem no_odd_integer_degree_of_cyclic_boundary
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    (faceEdges : F → Finset E) (boundaryEdges : Finset E)
    (hincidence : ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0)
    (turn : E → ℤ)
    (hclosed : ∀ f : F,
      ∑ e ∈ faceEdges f, integerEdgeParity turn e = 0)
    {n : ℕ} (boundaryEdge : Fin (n + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (hboundary : boundaryEdges = Finset.univ.image boundaryEdge)
    (degree : ℤ)
    (hturn : ∀ k, turn (boundaryEdge k) = cyclicDegreeTurn degree k)
    (hodd : Odd degree) : False := by
  apply no_odd_integer_boundary_degree_extension faceEdges boundaryEdges
    hincidence turn hclosed (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hturn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

/-- End-to-end finite polygonal-surface obstruction from the ordinary
one-face/two-face incidence rule, cyclic face boundaries, local lift
transitions, and a cyclically indexed boundary component. -/
theorem no_odd_integer_degree_of_polygonal_surface_local_lifts
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
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
    (transition : F → V → ℤ) (turn : E → ℤ)
    (hlocal : ∀ (f : F) (e : E), e ∈ faceEdges f →
      turn e = transition f (edgeEnds e).1 -
        transition f (edgeEnds e).2)
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (hboundary : boundaryEdges = Finset.univ.image boundaryEdge)
    (degree : ℤ)
    (hturn : ∀ k, turn (boundaryEdge k) = cyclicDegreeTurn degree k)
    (hodd : Odd degree) : False := by
  apply no_odd_integer_degree_of_local_lifts edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_cyclic_face_data edgeEnds faceEdges faceVertex faceEdge
      hfaceVertex hfaceEdge hfaceEdges hends)
    transition turn hlocal (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hturn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

/-- Variable-face-size version of
`no_odd_integer_degree_of_polygonal_surface_local_lifts`. -/
theorem no_odd_integer_degree_of_polygonal_surface_local_lifts_variable
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
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
    (transition : F → V → ℤ) (turn : E → ℤ)
    (hlocal : ∀ (f : F) (e : E), e ∈ faceEdges f →
      turn e = transition f (edgeEnds e).1 -
        transition f (edgeEnds e).2)
    {boundarySize : ℕ} (boundaryEdge : Fin (boundarySize + 1) → E)
    (hboundaryEdge : Function.Injective boundaryEdge)
    (hboundary : boundaryEdges = Finset.univ.image boundaryEdge)
    (degree : ℤ)
    (hturn : ∀ k, turn (boundaryEdge k) = cyclicDegreeTurn degree k)
    (hodd : Odd degree) : False := by
  apply no_odd_integer_degree_of_local_lifts edgeEnds faceEdges boundaryEdges
    (modTwo_incidence_of_face_count faceEdges boundaryEdges hcount)
    (faceEven_of_variable_cyclic_face_data edgeEnds faceEdges faceSize
      faceVertex faceEdge hfaceVertex hfaceEdge hfaceEdges hends)
    transition turn hlocal (-degree)
  · rw [hboundary, Finset.sum_image
      (fun x _hx y _hy hxy ↦ hboundaryEdge hxy)]
    simp_rw [hturn]
    exact sum_cyclicDegreeTurn degree
  · exact hodd.neg

end

end GromovFilling
