import GromovFilling.FinePolygonalModel

/-!
# The odd-degree obstruction for general polygon-side pairings

This file removes the special adjacent-preserving hypothesis from the
point-quotient obstruction.  For an arbitrary fixed-point-free involutive
pairing of the lower polygon edges, paired edge turns either agree or differ
by sign according to the gluing orientation.  Their reductions modulo two
therefore cancel in pairs, so the free boundary of the glued strip cannot
carry odd degree.
-/

namespace GromovFilling

noncomputable section

private def cylinderStripLowerBoundaryVertexValue
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) : UnitAddCircle :=
  H (cylinderStripGluedPointLowerBoundary P
    (angularSubdivisionPoint m j))

private theorem cylinderStripLowerBoundaryVertexStart_preserves_value
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) :
    cylinderStripLowerBoundaryVertexValue P H j =
      cylinderStripLowerBoundaryVertexValue P H (P.pairedStart j) := by
  apply congrArg H
  rcases horient : P.orientation j with _ | _
  · rw [P.pairedStart_preserving horient]
    change cylinderStripPointQuotientMap P
        (closedUnitIntervalStart, angularSubdivisionPoint m j) =
      cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (P.edgePair j))
    rw [← angularSubdivisionArc_start m j,
      ← angularSubdivisionArc_start m (P.edgePair j)]
    exact cylinderStripPointQuotientMap_lower_pair_preserving
      P horient closedUnitIntervalStart
  · rw [P.pairedStart_reversing horient]
    change cylinderStripPointQuotientMap P
        (closedUnitIntervalStart, angularSubdivisionPoint m j) =
      cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (cyclicSucc (P.edgePair j)))
    rw [← angularSubdivisionArc_start m j,
      ← angularSubdivisionArc_finish m (P.edgePair j)]
    simpa using
      cylinderStripPointQuotientMap_lower_pair_reversing
        P horient closedUnitIntervalStart

private theorem cylinderStripLowerBoundaryVertexFinish_preserves_value
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) :
    cylinderStripLowerBoundaryVertexValue P H (cyclicSucc j) =
      cylinderStripLowerBoundaryVertexValue P H (P.pairedFinish j) := by
  apply congrArg H
  rcases horient : P.orientation j with _ | _
  · rw [P.pairedFinish_preserving horient]
    change cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (cyclicSucc j)) =
      cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (cyclicSucc (P.edgePair j)))
    rw [← angularSubdivisionArc_finish m j,
      ← angularSubdivisionArc_finish m (P.edgePair j)]
    exact cylinderStripPointQuotientMap_lower_pair_preserving
      P horient closedUnitIntervalFinish
  · rw [P.pairedFinish_reversing horient]
    change cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (cyclicSucc j)) =
      cylinderStripPointQuotientMap P
        (closedUnitIntervalStart,
          angularSubdivisionPoint m (P.edgePair j))
    rw [← angularSubdivisionArc_finish m j,
      ← angularSubdivisionArc_start m (P.edgePair j)]
    simpa using
      cylinderStripPointQuotientMap_lower_pair_reversing
        P horient closedUnitIntervalFinish

private theorem cylinderStripLowerBoundaryVertexStep_preserves_value
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    {a b : Fin (m + 1)}
    (hstep : CylinderStripLowerBoundaryVertexStep P a b) :
    cylinderStripLowerBoundaryVertexValue P H a =
      cylinderStripLowerBoundaryVertexValue P H b := by
  cases hstep with
  | start =>
      exact cylinderStripLowerBoundaryVertexStart_preserves_value P H _
  | finish =>
      exact cylinderStripLowerBoundaryVertexFinish_preserves_value P H _

/-- The value of a circle map on a lower-boundary vertex.  The value descends
to the vertex quotient because the point quotient identifies exactly the
paired endpoints. -/
def cylinderStripGluedLowerBoundaryVertexValue
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle) :
    CylinderStripLowerBoundaryVertexClass P → UnitAddCircle :=
  Quotient.lift
    (cylinderStripLowerBoundaryVertexValue P H)
    (by
      intro a b hab
      induction hab with
      | rel _ _ hstep =>
          exact cylinderStripLowerBoundaryVertexStep_preserves_value P H hstep
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

@[simp] theorem cylinderStripGluedLowerBoundaryVertexValue_mk
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) :
    cylinderStripGluedLowerBoundaryVertexValue P H
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j) =
      H (cylinderStripGluedPointLowerBoundary P
        (angularSubdivisionPoint m j)) :=
  rfl

/-- The image under `H` of one lower-boundary edge of the point quotient. -/
def cylinderStripGluedLowerBoundaryEdgeValue
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) (x : ClosedUnitInterval) : UnitAddCircle :=
  H (cylinderStripGluedPointLowerBoundary P
    (angularSubdivisionArc m j x))

theorem continuous_cylinderStripGluedLowerBoundaryEdgeValue
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    {H : CylinderStripGluedPointSpace P → UnitAddCircle}
    (hH : Continuous H) (j : Fin (m + 1)) :
    Continuous (cylinderStripGluedLowerBoundaryEdgeValue P H j) :=
  hH.comp <| (continuous_cylinderStripGluedPointLowerBoundary P).comp
    (continuous_angularSubdivisionArc m j)

@[simp] theorem cylinderStripGluedLowerBoundaryEdgeValue_start
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) :
    cylinderStripGluedLowerBoundaryEdgeValue P H j
        closedUnitIntervalStart =
      cylinderStripGluedLowerBoundaryVertexValue P H
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j) := by
  unfold cylinderStripGluedLowerBoundaryEdgeValue
  rw [angularSubdivisionArc_start]
  rfl

@[simp] theorem cylinderStripGluedLowerBoundaryEdgeValue_finish
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    (j : Fin (m + 1)) :
    cylinderStripGluedLowerBoundaryEdgeValue P H j
        closedUnitIntervalFinish =
      cylinderStripGluedLowerBoundaryVertexValue P H
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
          (cyclicSucc j)) := by
  unfold cylinderStripGluedLowerBoundaryEdgeValue
  rw [angularSubdivisionArc_finish]
  rfl

theorem cylinderStripGluedLowerBoundaryEdgeValue_pair_preserving
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    {j : Fin (m + 1)} (horient : P.orientation j = .preserving)
    (x : ClosedUnitInterval) :
    cylinderStripGluedLowerBoundaryEdgeValue P H j x =
      cylinderStripGluedLowerBoundaryEdgeValue P H (P.edgePair j) x := by
  apply congrArg H
  exact cylinderStripPointQuotientMap_lower_pair_preserving P horient x

theorem cylinderStripGluedLowerBoundaryEdgeValue_pair_reversing
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    (H : CylinderStripGluedPointSpace P → UnitAddCircle)
    {j : Fin (m + 1)} (horient : P.orientation j = .reversing)
    (x : ClosedUnitInterval) :
    cylinderStripGluedLowerBoundaryEdgeValue P H j x =
      cylinderStripGluedLowerBoundaryEdgeValue P H (P.edgePair j)
        (reverseClosedUnitInterval x) := by
  apply congrArg H
  exact cylinderStripPointQuotientMap_lower_pair_reversing P horient x

/-- Every circle-valued map on a glued-strip point quotient has even degree
on the glued lower loop, for every fixed-point-free involutive side pairing
and for either orientation on each paired side. -/
theorem even_circleDegree_cylinderStripGluedPointLowerBoundary
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m)
    {degree : ℤ}
    {H : CylinderStripGluedPointSpace P → UnitAddCircle}
    (hdegree : HasCircleDegree
      (H ∘ cylinderStripGluedPointLowerBoundary P) degree) :
    Even degree := by
  classical
  have hdegreeOriginal := hdegree
  obtain ⟨degreeLift, hdegreeLift, hdegreeLiftProjects, _hperiod⟩ := hdegree
  choose vertexLift _hvertexIco hvertexLift using fun v :
      CylinderStripLowerBoundaryVertexClass P ↦
    AddCircle.eq_coe_Ico
      (cylinderStripGluedLowerBoundaryVertexValue P H v)
  let edgeLift : Fin (m + 1) → ClosedUnitInterval → ℝ :=
    fun j x ↦ degreeLift (angularSubdivisionParameter m j x)
  have hedgeLift (j : Fin (m + 1)) : Continuous (edgeLift j) := by
    exact hdegreeLift.comp <| by
      simpa [angularSubdivisionParameter] using
        (continuous_subtype_val.add continuous_const).div_const
          (((m + 1 : ℕ) : ℝ))
  have hedgeLiftProjects (j : Fin (m + 1)) (x : ClosedUnitInterval) :
      (edgeLift j x : UnitAddCircle) =
        cylinderStripGluedLowerBoundaryEdgeValue P H j x := by
    simpa [edgeLift, cylinderStripGluedLowerBoundaryEdgeValue,
      angularSubdivisionArc, Function.comp_apply] using
        hdegreeLiftProjects (angularSubdivisionParameter m j x)
  have hsameStart (j : Fin (m + 1)) :
      (edgeLift j closedUnitIntervalStart : UnitAddCircle) =
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j) :
            UnitAddCircle) := by
    rw [hedgeLiftProjects,
      cylinderStripGluedLowerBoundaryEdgeValue_start, hvertexLift]
  have hsameFinish (j : Fin (m + 1)) :
      (edgeLift j closedUnitIntervalFinish : UnitAddCircle) =
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
            (cyclicSucc j)) : UnitAddCircle) := by
    rw [hedgeLiftProjects,
      cylinderStripGluedLowerBoundaryEdgeValue_finish, hvertexLift]
  choose startOffset hstartOffset using fun j : Fin (m + 1) ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift j closedUnitIntervalStart)
      (vertexLift
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j))
      (hsameStart j)
  choose finishOffset hfinishOffset using fun j : Fin (m + 1) ↦
    exists_integer_difference_of_same_unitAddCircle
      (edgeLift j closedUnitIntervalFinish)
      (vertexLift
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
          (cyclicSucc j)))
      (hsameFinish j)
  let turn : Fin (m + 1) → ℤ :=
    fun j ↦ startOffset j - finishOffset j
  have hturn (j : Fin (m + 1)) : (turn j : ℝ) =
      (edgeLift j closedUnitIntervalStart -
          vertexLift
            (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j)) -
        (edgeLift j closedUnitIntervalFinish -
          vertexLift
            (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
              (cyclicSucc j))) := by
    change ((startOffset j - finishOffset j : ℤ) : ℝ) = _
    rw [Int.cast_sub, hstartOffset, hfinishOffset]
  have hturnSum : ∑ j : Fin (m + 1), turn j = -degree := by
    have hsum := boundary_edge_turn_sum_eq_neg_degree
      (X := UnitAddCircle)
      (V := CylinderStripLowerBoundaryVertexClass P)
      (E := Fin (m + 1))
      (fun j ↦
        (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j,
          Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
            (cyclicSucc j)))
      (fun j ↦ j) Function.injective_id
      (fun j ↦ Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j)
      (by intro j; rfl)
      (fun _ ↦ ClosedUnitInterval)
      (fun _ ↦ closedUnitIntervalStart)
      (fun _ ↦ closedUnitIntervalFinish)
      (cylinderStripGluedLowerBoundaryEdgeValue P H)
      (fun x ↦ x)
      (H ∘ cylinderStripGluedPointLowerBoundary P)
      (fun j ↦ angularSubdivisionParameter m j)
      (fun j ↦ by
        simpa [angularSubdivisionParameter] using
          (continuous_subtype_val.add continuous_const).div_const
            (((m + 1 : ℕ) : ℝ)))
      (by
        intro j
        simp [angularSubdivisionParameter, cyclicVertexParameter,
          closedUnitIntervalStart])
      (by
        intro j
        simp [angularSubdivisionParameter, cyclicEdgeFinishParameter,
          closedUnitIntervalFinish, add_comm])
      (by
        intro j x
        rfl)
      vertexLift edgeLift hedgeLift hedgeLiftProjects turn hturn degree
      (by simpa using hdegreeOriginal)
    simpa using hsum
  have hturn_pair (j : Fin (m + 1)) :
      turn j = turn (P.edgePair j) ∨
        turn j = -turn (P.edgePair j) := by
    rcases horient : P.orientation j with _ | _
    · left
      have hvertexStart :
          vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j) =
            vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (P.edgePair j)) := by
        apply congrArg vertexLift
        have h := mk_cylinderStripLowerBoundaryVertexClass_start P j
        rw [P.pairedStart_preserving horient] at h
        exact h
      have hvertexFinish :
          vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (cyclicSucc j)) =
            vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (cyclicSucc (P.edgePair j))) := by
        apply congrArg vertexLift
        have h := mk_cylinderStripLowerBoundaryVertexClass_finish P j
        rw [P.pairedFinish_preserving horient] at h
        exact h
      have hcompare := edge_turn_eq_face_transition
        (edgeLift j) (edgeLift (P.edgePair j))
        (hedgeLift j) (hedgeLift (P.edgePair j))
        (fun x ↦ by
          rw [hedgeLiftProjects, hedgeLiftProjects]
          exact cylinderStripGluedLowerBoundaryEdgeValue_pair_preserving
            P H horient x)
        closedUnitIntervalStart closedUnitIntervalFinish
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j))
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
            (cyclicSucc j)))
        (turn j) (hturn j)
      have hreal : (turn j : ℝ) = (turn (P.edgePair j) : ℝ) := by
        rw [hvertexStart, hvertexFinish] at hcompare
        exact hcompare.trans (hturn (P.edgePair j)).symm
      exact_mod_cast hreal
    · right
      have hvertexStart :
          vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j) =
            vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (cyclicSucc (P.edgePair j))) := by
        apply congrArg vertexLift
        have h := mk_cylinderStripLowerBoundaryVertexClass_start P j
        rw [P.pairedStart_reversing horient] at h
        exact h
      have hvertexFinish :
          vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (cyclicSucc j)) =
            vertexLift
              (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
                (P.edgePair j)) := by
        apply congrArg vertexLift
        have h := mk_cylinderStripLowerBoundaryVertexClass_finish P j
        rw [P.pairedFinish_reversing horient] at h
        exact h
      have hcompare := edge_turn_eq_face_transition
        (edgeLift j)
        (fun x ↦ edgeLift (P.edgePair j) (reverseClosedUnitInterval x))
        (hedgeLift j)
        ((hedgeLift (P.edgePair j)).comp continuous_reverseClosedUnitInterval)
        (fun x ↦ by
          rw [hedgeLiftProjects, hedgeLiftProjects]
          exact cylinderStripGluedLowerBoundaryEdgeValue_pair_reversing
            P H horient x)
        closedUnitIntervalStart closedUnitIntervalFinish
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P) j))
        (vertexLift
          (Quotient.mk (cylinderStripLowerBoundaryVertexSetoid P)
            (cyclicSucc j)))
        (turn j) (hturn j)
      have hreal : (turn j : ℝ) = -(turn (P.edgePair j) : ℝ) := by
        dsimp only at hcompare
        rw [reverseClosedUnitInterval_start,
          reverseClosedUnitInterval_finish,
          hvertexStart, hvertexFinish] at hcompare
        linarith only [hcompare, hturn (P.edgePair j)]
      exact_mod_cast hreal
  have hpairParity (j : Fin (m + 1)) :
      integerEdgeParity turn j +
          integerEdgeParity turn (P.edgePair j) = 0 := by
    have heq : integerEdgeParity turn j =
        integerEdgeParity turn (P.edgePair j) := by
      rcases hturn_pair j with hsame | hneg
      · simp [integerEdgeParity, hsame]
      · simp [integerEdgeParity, hneg]
    rw [heq]
    let a : ZMod 2 := integerEdgeParity turn (P.edgePair j)
    change a + a = 0
    calc
      a + a = -a + a := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := neg_add_cancel a
  have hparitySum :
      ∑ j : Fin (m + 1), integerEdgeParity turn j = 0 := by
    simpa using Finset.sum_ninvolution
      (s := Finset.univ) (f := integerEdgeParity turn)
      P.edgePair hpairParity
      (fun j _h ↦ P.edgePair_noFixed j)
      (fun j ↦ Finset.mem_univ (P.edgePair j))
      P.edgePair_involutive
  have hcastSum : ((∑ j : Fin (m + 1), turn j : ℤ) : ZMod 2) = 0 := by
    simpa [integerEdgeParity] using hparitySum
  rw [hturnSum] at hcastSum
  have hdegreeZero : (degree : ZMod 2) = 0 := by
    simpa only [Int.cast_neg, neg_eq_zero] using hcastSum
  apply Int.not_odd_iff_even.mp
  intro hodd
  have hone := intCast_zmod_two_eq_one_of_odd hodd
  rw [hdegreeZero] at hone
  exact zero_ne_one hone

/-- The glued lower loop for an arbitrary polygon-side pairing already
carries the odd-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_cylinderStripGluedPointLowerBoundary
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m) :
    HasOddBoundaryDegreeObstruction
      (cylinderStripGluedPointLowerBoundary P) := by
  intro H _hH degree hdegree hodd
  have heven :=
    even_circleDegree_cylinderStripGluedPointLowerBoundary P hdegree
  exact (Int.not_odd_iff_even.mpr heven) hodd

/-- Every glued-strip point quotient has the odd-degree obstruction on its
free upper boundary, with no special form assumed for its side pairing. -/
theorem hasOddBoundaryDegreeObstruction_cylinderStripGluedPointBoundary
    {m : ℕ} (P : CylinderStripLowerBoundaryPairing m) :
    HasOddBoundaryDegreeObstruction
      (cylinderStripGluedPointBoundary P) :=
  hasOddBoundaryDegreeObstruction_of_cylinderStripGluedPointLowerBoundary
    P (hasOddBoundaryDegreeObstruction_cylinderStripGluedPointLowerBoundary P)

end

end GromovFilling
