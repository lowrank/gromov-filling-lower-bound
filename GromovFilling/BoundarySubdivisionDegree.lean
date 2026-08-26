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

end

end GromovFilling
