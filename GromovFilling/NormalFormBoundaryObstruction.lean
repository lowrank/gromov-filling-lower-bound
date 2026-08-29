import GromovFilling.GeneralSurfaceObstruction
import ClassificationOfSurfaces.EvalStatement
import Mathlib.Topology.CompactOpen

/-!
# Boundary loops of the classified surface normal forms

This file proves the canonical-normal-form half of the boundary-relative
bridge needed for manuscript Lemma 5.4.  For a normal form with exactly one
free boundary word, it constructs the complementary side pairing, descends it
through the glued-cylinder parity theorem, and transports the obstruction to
the free `h` loop in the trusted `OrientableRel` and `NonOrientableRel`
quotients.
-/

namespace GromovFilling

noncomputable section

open Complex Set
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.NormalForm
open LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex
open unitInterval

private theorem AddCircle.liftIco_one_apply_coe_unitInterval
    {Y : Type*} (f : ℝ → Y) (hends : f 0 = f 1)
    (t : Set.Icc (0 : ℝ) 1) :
    AddCircle.liftIco 1 0 f ((t : ℝ) : UnitAddCircle) = f t := by
  by_cases ht : (t : ℝ) = 1
  · rw [ht, show ((1 : ℝ) : UnitAddCircle) = 0 by
      exact AddCircle.coe_period (1 : ℝ)]
    change AddCircle.liftIco 1 0 f (((0 : ℝ) : UnitAddCircle)) = f 1
    rw [AddCircle.liftIco_coe_apply (p := (1 : ℝ)) (a := 0)
      (x := 0) (by norm_num)]
    exact hends
  · rw [AddCircle.liftIco_coe_apply (p := (1 : ℝ)) (a := 0)]
    exact ⟨t.2.1, by simpa using t.2.2.lt_of_ne ht⟩

/-- The penultimate member of `Fin (m + 2)`. -/
def finPenultimate (m : ℕ) : Fin (m + 2) :=
  ⟨m, by omega⟩

/-- Enumerate every index except the penultimate one, beginning with the last
index and then continuing from zero.  This is the cyclic order of the
complement of a penultimate polygon side. -/
def finComplementPenultimateEquiv (m : ℕ) :
    Fin (m + 1) ≃ {i : Fin (m + 2) // i ≠ finPenultimate m} :=
  (finRotate (m + 1)).symm.trans
    (finSuccAboveEquiv (finPenultimate m))

@[simp] theorem finComplementPenultimateEquiv_zero (m : ℕ) :
    (finComplementPenultimateEquiv m 0).1 = Fin.last (m + 1) := by
  have hrotate :
      (finRotate (m + 1)).symm (0 : Fin (m + 1)) = Fin.last m := by
    apply (finRotate (m + 1)).injective
    simp
  change (finPenultimate m).succAbove
      ((finRotate (m + 1)).symm (0 : Fin (m + 1))) = Fin.last (m + 1)
  rw [hrotate]
  exact Fin.succAbove_ne_last_last (by
    intro h
    have := congrArg Fin.val h
    simp [finPenultimate] at this)

theorem finComplementPenultimateEquiv_val_of_ne_zero
    (m : ℕ) (j : Fin (m + 1)) (hj : j ≠ 0) :
    (finComplementPenultimateEquiv m j).1.val = j.val - 1 := by
  let k : Fin (m + 1) := (finRotate (m + 1)).symm j
  have hkval : k.val = j.val - 1 := by
    exact coe_finRotate_symm_of_ne_zero hj
  have hklt : k.castSucc < finPenultimate m := by
    rw [Fin.lt_def]
    change k.val < m
    rw [hkval]
    have hjle : j.val ≤ m := Nat.le_of_lt_succ j.isLt
    omega
  change ((finPenultimate m).succAbove
    ((finRotate (m + 1)).symm j)).val = j.val - 1
  change ((finPenultimate m).succAbove k).val = j.val - 1
  rw [Fin.succAbove_of_castSucc_lt _ _ hklt]
  exact hkval

/-! ## Canonical partners of internal polygon occurrences -/

/-- The unique other occurrence of an internal polygon side. -/
noncomputable def occurrencePartner
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    K.BoundaryOccurrence :=
  Classical.choose (valid.exists_unique_partner source hsource)

theorem occurrencePartner_spec
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    source ≠ occurrencePartner valid source hsource ∧
      (K.occurrenceDart (occurrencePartner valid source hsource) =
          K.occurrenceDart source ∨
        K.occurrenceDart (occurrencePartner valid source hsource) =
          K.inv (K.occurrenceDart source)) :=
  (Classical.choose_spec
    (valid.exists_unique_partner source hsource)).1

theorem occurrencePartner_eq_of
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source))
    (target : K.BoundaryOccurrence)
    (htarget : source ≠ target ∧
      (K.occurrenceDart target = K.occurrenceDart source ∨
        K.occurrenceDart target = K.inv (K.occurrenceDart source))) :
    target = occurrencePartner valid source hsource :=
  (Classical.choose_spec
    (valid.exists_unique_partner source hsource)).2 target htarget

theorem occurrencePartner_not_boundary
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    ¬K.IsBoundaryDart
      (K.occurrenceDart (occurrencePartner valid source hsource)) := by
  rcases (occurrencePartner_spec valid source hsource).2 with hsame | hinv
  · simpa [hsame] using hsource
  · rw [hinv]
    simpa only [K.isBoundaryDart_inv_iff] using hsource

theorem occurrencePartner_involutive
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    occurrencePartner valid
        (occurrencePartner valid source hsource)
        (occurrencePartner_not_boundary valid source hsource) = source := by
  symm
  apply occurrencePartner_eq_of valid
    (occurrencePartner valid source hsource)
    (occurrencePartner_not_boundary valid source hsource)
  constructor
  · exact (occurrencePartner_spec valid source hsource).1.symm
  · rcases (occurrencePartner_spec valid source hsource).2 with hsame | hinv
    · exact Or.inl hsame.symm
    · right
      have h := congrArg K.inv hinv
      simpa only [K.inv_involutive] using h.symm

/-- Orientation of the unique partner relation, in the convention used by
the glued-cylinder parity theorem. -/
noncomputable def occurrencePartnerOrientation
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    CylinderStripLowerBoundaryOrientation := by
  classical
  exact if K.occurrenceDart (occurrencePartner valid source hsource) =
        K.occurrenceDart source then
      .preserving
    else
      .reversing

theorem occurrencePartnerOrientation_eq_preserving_iff
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    occurrencePartnerOrientation valid source hsource = .preserving ↔
      K.occurrenceDart (occurrencePartner valid source hsource) =
        K.occurrenceDart source := by
  classical
  simp [occurrencePartnerOrientation]

theorem occurrencePartnerOrientation_eq_reversing_iff
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    occurrencePartnerOrientation valid source hsource = .reversing ↔
      K.occurrenceDart (occurrencePartner valid source hsource) =
        K.inv (K.occurrenceDart source) := by
  classical
  constructor
  · intro horient
    unfold occurrencePartnerOrientation at horient
    split at horient
    · contradiction
    · exact (occurrencePartner_spec valid source hsource).2.resolve_left
        (by assumption)
  · intro hinv
    unfold occurrencePartnerOrientation
    split
    · next hsame =>
        have hne := valid.inv_ne (K.occurrenceDart source)
        rw [hsame] at hinv
        exact (hne hinv.symm).elim
    · rfl

/-- Looking from the partner back at the source gives the same unoriented
gluing flag. -/
theorem occurrencePartnerOrientation_partner
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    (source : K.BoundaryOccurrence)
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source)) :
    occurrencePartnerOrientation valid
        (occurrencePartner valid source hsource)
        (occurrencePartner_not_boundary valid source hsource) =
      occurrencePartnerOrientation valid source hsource := by
  have hpreserving :
      occurrencePartnerOrientation valid
          (occurrencePartner valid source hsource)
          (occurrencePartner_not_boundary valid source hsource) = .preserving ↔
        occurrencePartnerOrientation valid source hsource = .preserving := by
    rw [occurrencePartnerOrientation_eq_preserving_iff,
      occurrencePartnerOrientation_eq_preserving_iff,
      occurrencePartner_involutive]
    exact eq_comm
  cases hright : occurrencePartnerOrientation valid source hsource with
  | preserving =>
      exact hpreserving.mpr hright
  | reversing =>
      cases hleft : occurrencePartnerOrientation valid
          (occurrencePartner valid source hsource)
          (occurrencePartner_not_boundary valid source hsource) with
      | preserving =>
          have hcontra :
              CylinderStripLowerBoundaryOrientation.preserving = .reversing :=
            (hpreserving.mp hleft).symm.trans hright
          cases hcontra
      | reversing => rfl

theorem occurrencePartnerOrientation_congr
    {K : SurfaceCellComplex} (valid : K.OccurrencePairingValid)
    {source target : K.BoundaryOccurrence}
    (hsource : ¬K.IsBoundaryDart (K.occurrenceDart source))
    (htarget : ¬K.IsBoundaryDart (K.occurrenceDart target))
    (h : source = target) :
    occurrencePartnerOrientation valid source hsource =
      occurrencePartnerOrientation valid target htarget := by
  subst target
  rfl

/-- Recover the word index from an occurrence in a one-face presentation. -/
def oneFaceOccurrenceIndex {Edge : Type} [Fintype Edge]
    {word : List (SignedDart Edge)} :
    (oneFacePresentation Edge word).BoundaryOccurrence → Fin word.length
  | ⟨face, i⟩ => by
      cases face
      exact i

@[simp] theorem oneFaceOccurrenceIndex_oneFaceOccurrence
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge))
    (i : Fin word.length) :
    oneFaceOccurrenceIndex (oneFaceOccurrence word i) = i :=
  rfl

theorem oneFaceOccurrence_oneFaceOccurrenceIndex
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge))
    (o : (oneFacePresentation Edge word).BoundaryOccurrence) :
    oneFaceOccurrence word (oneFaceOccurrenceIndex o) = o := by
  rcases o with ⟨face, i⟩
  cases face
  rfl

/-- Every orientable one-boundary word position except the unique `h`
position is an internal occurrence. -/
theorem orientableNormalOccurrence_not_boundary
    (p : ℕ) (i : Fin (orientableBoundaryWord p 1).length)
    (hi : i ≠ orientableBoundaryPosition p 1 (0 : Fin 1) 1) :
    ¬(orientableCellComplex p 1).IsBoundaryDart
      ((orientableCellComplex p 1).occurrenceDart
        (oneFaceOccurrence (orientableBoundaryWord p 1) i)) := by
  let K := orientableCellComplex p 1
  let occurrence := fun j : Fin (orientableBoundaryWord p 1).length ↦
    oneFaceOccurrence (orientableBoundaryWord p 1) j
  have occurrence_ne {a b : Fin (orientableBoundaryWord p 1).length}
      (hab : a ≠ b) : occurrence a ≠ occurrence b := by
    intro h
    apply hab
    have hval := congrArg
      (fun o : (oneFacePresentation (OrientableEdge p 1)
        (orientableBoundaryWord p 1)).BoundaryOccurrence ↦ o.2.val) h
    exact Fin.ext hval
  have occurs_of_edgeName {j : Fin (orientableBoundaryWord p 1).length}
      (hname : SignedDart.edgeName ((orientableBoundaryWord p 1).get j) =
        SignedDart.edgeName ((orientableBoundaryWord p 1).get i)) :
      K.Occurs ((orientableBoundaryWord p 1).get i) (occurrence j) := by
    exact (SignedDart.eq_or_eq_flip_iff_edgeName_eq _ _).2 hname
  cases hedge : SignedDart.edgeName ((orientableBoundaryWord p 1).get i) with
  | a k =>
      apply not_isBoundaryDart_of_occurs_at_ne
        (occurrence_ne (orientableHandlePosition_zero_ne_two (n := 1) k))
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_handle_a_pos]
        exact hedge.symm
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_handle_a_neg]
        exact hedge.symm
  | b k =>
      apply not_isBoundaryDart_of_occurs_at_ne
        (occurrence_ne (orientableHandlePosition_one_ne_three (n := 1) k))
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_handle_b_pos]
        exact hedge.symm
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_handle_b_neg]
        exact hedge.symm
  | c k =>
      apply not_isBoundaryDart_of_occurs_at_ne
        (occurrence_ne (orientableBoundaryPosition_zero_ne_two (p := p) k))
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_boundary_c_pos]
        exact hedge.symm
      · apply occurs_of_edgeName
        rw [orientableBoundaryWord_get_boundary_c_neg]
        exact hedge.symm
  | h k =>
      have himem :
          i ∈ wordEdgeOccurrences (orientableBoundaryWord p 1) (.h k) :=
        (mem_wordEdgeOccurrences _ _ _).2 hedge
      rw [orientableBoundaryWord_edgeOccurrences_h] at himem
      have hieq : i = orientableBoundaryPosition p 1 k 1 := by
        simpa using himem
      have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      subst k
      exact (hi hieq).elim

/-- Every nonorientable one-boundary word position except the unique `h`
position is an internal occurrence. -/
theorem nonOrientableNormalOccurrence_not_boundary
    (p : ℕ) (i : Fin (nonOrientableBoundaryWord p 1).length)
    (hi : i ≠ nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1) :
    ¬(nonOrientableCellComplex p 1).IsBoundaryDart
      ((nonOrientableCellComplex p 1).occurrenceDart
        (oneFaceOccurrence (nonOrientableBoundaryWord p 1) i)) := by
  let K := nonOrientableCellComplex p 1
  let occurrence := fun j : Fin (nonOrientableBoundaryWord p 1).length ↦
    oneFaceOccurrence (nonOrientableBoundaryWord p 1) j
  have occurrence_ne {a b : Fin (nonOrientableBoundaryWord p 1).length}
      (hab : a ≠ b) : occurrence a ≠ occurrence b := by
    intro h
    apply hab
    have hval := congrArg
      (fun o : (oneFacePresentation (NonOrientableEdge p 1)
        (nonOrientableBoundaryWord p 1)).BoundaryOccurrence ↦ o.2.val) h
    exact Fin.ext hval
  have occurs_of_edgeName {j : Fin (nonOrientableBoundaryWord p 1).length}
      (hname : SignedDart.edgeName ((nonOrientableBoundaryWord p 1).get j) =
        SignedDart.edgeName ((nonOrientableBoundaryWord p 1).get i)) :
      K.Occurs ((nonOrientableBoundaryWord p 1).get i) (occurrence j) := by
    exact (SignedDart.eq_or_eq_flip_iff_edgeName_eq _ _).2 hname
  cases hedge : SignedDart.edgeName ((nonOrientableBoundaryWord p 1).get i) with
  | a k =>
      apply not_isBoundaryDart_of_occurs_at_ne
        (occurrence_ne (nonOrientableCrosscapPosition_zero_ne_one (n := 1) k))
      · apply occurs_of_edgeName
        rw [nonOrientableBoundaryWord_get_crosscap_a_first]
        exact hedge.symm
      · apply occurs_of_edgeName
        rw [nonOrientableBoundaryWord_get_crosscap_a_second]
        exact hedge.symm
  | c k =>
      apply not_isBoundaryDart_of_occurs_at_ne
        (occurrence_ne (nonOrientableBoundaryPosition_zero_ne_two (p := p) k))
      · apply occurs_of_edgeName
        rw [nonOrientableBoundaryWord_get_boundary_c_pos]
        exact hedge.symm
      · apply occurs_of_edgeName
        rw [nonOrientableBoundaryWord_get_boundary_c_neg]
        exact hedge.symm
  | h k =>
      have himem :
          i ∈ wordEdgeOccurrences (nonOrientableBoundaryWord p 1) (.h k) :=
        (mem_wordEdgeOccurrences _ _ _).2 hedge
      rw [nonOrientableBoundaryWord_edgeOccurrences_h] at himem
      have hieq : i = nonOrientableBoundaryPosition p 1 k 1 := by
        simpa using himem
      have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
      subst k
      exact (hi hieq).elim

/-! ## The cyclic complement of the unique free side -/

/-- The cyclic complement of the free orientable `h` side, indexed in the
order that starts immediately after that side. -/
def orientableNormalComplementPositionEquiv (p : ℕ) :
    Fin ((4 * p + 1) + 1) ≃
      {i : Fin (orientableBoundaryWord p 1).length //
        i ≠ orientableBoundaryPosition p 1 (0 : Fin 1) 1} :=
  (finComplementPenultimateEquiv (4 * p + 1)).trans <|
    (finCongr (by rw [orientableBoundaryWord_length])).subtypeEquiv (by
      intro i
      have heq :
          finCongr (by rw [orientableBoundaryWord_length]) i =
              orientableBoundaryPosition p 1 (0 : Fin 1) 1 ↔
            i = finPenultimate (4 * p + 1) := by
        constructor <;> intro hEq <;> apply Fin.ext <;>
          simpa [finPenultimate] using congrArg Fin.val hEq
      exact not_congr heq.symm)

/-- The cyclic complement of the free nonorientable `h` side. -/
def nonOrientableNormalComplementPositionEquiv (p : ℕ) :
    Fin ((2 * p + 1) + 1) ≃
      {i : Fin (nonOrientableBoundaryWord p 1).length //
        i ≠ nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1} :=
  (finComplementPenultimateEquiv (2 * p + 1)).trans <|
    (finCongr (by rw [nonOrientableBoundaryWord_length])).subtypeEquiv (by
      intro i
      have heq :
          finCongr (by rw [nonOrientableBoundaryWord_length]) i =
              nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1 ↔
            i = finPenultimate (2 * p + 1) := by
        constructor <;> intro hEq <;> apply Fin.ext <;>
          simpa [finPenultimate] using congrArg Fin.val hEq
      exact not_congr heq.symm)

@[simp] theorem orientableNormalComplementPositionEquiv_zero_val (p : ℕ) :
    (orientableNormalComplementPositionEquiv p 0).1.val = 4 * p + 2 := by
  change (finComplementPenultimateEquiv (4 * p + 1) 0).1.val = 4 * p + 2
  rw [finComplementPenultimateEquiv_zero]
  rfl

theorem orientableNormalComplementPositionEquiv_val_of_ne_zero
    (p : ℕ) (j : Fin ((4 * p + 1) + 1)) (hj : j ≠ 0) :
    (orientableNormalComplementPositionEquiv p j).1.val = j.val - 1 := by
  change (finComplementPenultimateEquiv (4 * p + 1) j).1.val = j.val - 1
  exact finComplementPenultimateEquiv_val_of_ne_zero _ _ hj

@[simp] theorem nonOrientableNormalComplementPositionEquiv_zero_val (p : ℕ) :
    (nonOrientableNormalComplementPositionEquiv p 0).1.val = 2 * p + 2 := by
  change (finComplementPenultimateEquiv (2 * p + 1) 0).1.val = 2 * p + 2
  rw [finComplementPenultimateEquiv_zero]
  rfl

theorem nonOrientableNormalComplementPositionEquiv_val_of_ne_zero
    (p : ℕ) (j : Fin ((2 * p + 1) + 1)) (hj : j ≠ 0) :
    (nonOrientableNormalComplementPositionEquiv p j).1.val = j.val - 1 := by
  change (finComplementPenultimateEquiv (2 * p + 1) j).1.val = j.val - 1
  exact finComplementPenultimateEquiv_val_of_ne_zero _ _ hj

/-- The real parameter of an angular subdivision arc, retained in `[0,1]`. -/
def angularSubdivisionParameterIcc (m : ℕ) (j : Fin (m + 1))
    (x : ClosedUnitInterval) : Set.Icc (0 : ℝ) 1 :=
  ⟨angularSubdivisionParameter m j x, by
    constructor
    · unfold angularSubdivisionParameter
      apply div_nonneg
      · exact add_nonneg x.2.1 (Nat.cast_nonneg _)
      · positivity
    · unfold angularSubdivisionParameter
      apply (div_le_one (by positivity)).2
      have hx := x.2.2
      have hj : (j.val : ℝ) ≤ m := by
        exact_mod_cast Nat.le_of_lt_succ j.isLt
      linarith⟩

@[simp] theorem angularSubdivisionParameterIcc_coe
    (m : ℕ) (j : Fin (m + 1)) (x : ClosedUnitInterval) :
    (angularSubdivisionParameterIcc m j x : ℝ) =
      angularSubdivisionParameter m j x :=
  rfl

/-- The unique orientable `h` occurrence really is a boundary dart. -/
theorem orientableNormalH_is_boundary (p : ℕ) :
    (orientableCellComplex p 1).IsBoundaryDart
      ((orientableCellComplex p 1).occurrenceDart
        (oneFaceOccurrence (orientableBoundaryWord p 1)
          (orientableBoundaryPosition p 1 (0 : Fin 1) 1))) := by
  unfold SurfaceCellComplex.IsBoundaryDart SurfaceCellComplex.OccursExactlyOnce
  refine ⟨oneFaceOccurrence (orientableBoundaryWord p 1)
      (orientableBoundaryPosition p 1 (0 : Fin 1) 1), Or.inl rfl, ?_⟩
  rintro ⟨f, i⟩ hi
  cases f
  change Fin (orientableBoundaryWord p 1).length at i
  change
    (orientableBoundaryWord p 1).get i =
        (orientableBoundaryWord p 1).get
          (orientableBoundaryPosition p 1 (0 : Fin 1) 1) ∨
      (orientableBoundaryWord p 1).get i =
        SignedDart.flip ((orientableBoundaryWord p 1).get
          (orientableBoundaryPosition p 1 (0 : Fin 1) 1)) at hi
  have hname :=
    (SignedDart.eq_or_eq_flip_iff_edgeName_eq _ _).1 hi
  have himem :
      i ∈ wordEdgeOccurrences (orientableBoundaryWord p 1)
        (.h (0 : Fin 1)) := by
    rw [mem_wordEdgeOccurrences]
    rw [orientableBoundaryWord_get_boundary_h_pos] at hname
    exact hname
  rw [orientableBoundaryWord_edgeOccurrences_h] at himem
  simp only [Finset.mem_singleton] at himem
  have hieq :
      i = orientableBoundaryPosition p 1 (0 : Fin 1) 1 := by
    exact himem
  subst i
  rfl

/-- The unique nonorientable `h` occurrence really is a boundary dart. -/
theorem nonOrientableNormalH_is_boundary (p : ℕ) :
    (nonOrientableCellComplex p 1).IsBoundaryDart
      ((nonOrientableCellComplex p 1).occurrenceDart
        (oneFaceOccurrence (nonOrientableBoundaryWord p 1)
          (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1))) := by
  unfold SurfaceCellComplex.IsBoundaryDart SurfaceCellComplex.OccursExactlyOnce
  refine ⟨oneFaceOccurrence (nonOrientableBoundaryWord p 1)
      (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1), Or.inl rfl, ?_⟩
  rintro ⟨f, i⟩ hi
  cases f
  change Fin (nonOrientableBoundaryWord p 1).length at i
  change
    (nonOrientableBoundaryWord p 1).get i =
        (nonOrientableBoundaryWord p 1).get
          (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1) ∨
      (nonOrientableBoundaryWord p 1).get i =
        SignedDart.flip ((nonOrientableBoundaryWord p 1).get
          (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1)) at hi
  have hname :=
    (SignedDart.eq_or_eq_flip_iff_edgeName_eq _ _).1 hi
  have himem :
      i ∈ wordEdgeOccurrences (nonOrientableBoundaryWord p 1)
        (.h (0 : Fin 1)) := by
    rw [mem_wordEdgeOccurrences]
    rw [nonOrientableBoundaryWord_get_boundary_h_pos] at hname
    exact hname
  rw [nonOrientableBoundaryWord_edgeOccurrences_h] at himem
  simp only [Finset.mem_singleton] at himem
  have hieq :
      i = nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1 := by
    exact himem
  subst i
  rfl

/-! ## Pairings carried by the cyclic complements -/

/-- The orientable polygon occurrence represented by one complementary
cylinder edge. -/
def orientableNormalComplementOccurrence (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    (orientableCellComplex p 1).BoundaryOccurrence :=
  oneFaceOccurrence (orientableBoundaryWord p 1)
    (orientableNormalComplementPositionEquiv p j).1

theorem orientableNormalComplementOccurrence_not_boundary (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    ¬(orientableCellComplex p 1).IsBoundaryDart
      ((orientableCellComplex p 1).occurrenceDart
        (orientableNormalComplementOccurrence p j)) :=
  orientableNormalOccurrence_not_boundary p
    (orientableNormalComplementPositionEquiv p j).1
    (orientableNormalComplementPositionEquiv p j).2

/-- The unique matching polygon occurrence of an orientable complementary
edge. -/
noncomputable def orientableNormalComplementPartnerOccurrence (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    (orientableCellComplex p 1).BoundaryOccurrence :=
  occurrencePartner
    (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
    (orientableNormalComplementOccurrence p j)
    (orientableNormalComplementOccurrence_not_boundary p j)

theorem orientableNormalComplementPartnerIndex_ne_boundary (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    oneFaceOccurrenceIndex
        (orientableNormalComplementPartnerOccurrence p j) ≠
      orientableBoundaryPosition p 1 (0 : Fin 1) 1 := by
  intro hindex
  have hoccurrence :
      orientableNormalComplementPartnerOccurrence p j =
        oneFaceOccurrence (orientableBoundaryWord p 1)
          (orientableBoundaryPosition p 1 (0 : Fin 1) 1) := by
    calc
      orientableNormalComplementPartnerOccurrence p j =
          oneFaceOccurrence (orientableBoundaryWord p 1)
            (oneFaceOccurrenceIndex
              (orientableNormalComplementPartnerOccurrence p j)) :=
        (oneFaceOccurrence_oneFaceOccurrenceIndex _ _).symm
      _ = oneFaceOccurrence (orientableBoundaryWord p 1)
          (orientableBoundaryPosition p 1 (0 : Fin 1) 1) :=
        congrArg (oneFaceOccurrence (orientableBoundaryWord p 1)) hindex
  have hnot := occurrencePartner_not_boundary
    (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
    (orientableNormalComplementOccurrence p j)
    (orientableNormalComplementOccurrence_not_boundary p j)
  change ¬(orientableCellComplex p 1).IsBoundaryDart
    ((orientableCellComplex p 1).occurrenceDart
      (orientableNormalComplementPartnerOccurrence p j)) at hnot
  apply hnot
  rw [hoccurrence]
  exact orientableNormalH_is_boundary p

/-- Pair a complementary orientable cylinder edge by transporting the unique
other polygon occurrence back through the cyclic indexing equivalence. -/
noncomputable def orientableNormalComplementEdgePair (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) : Fin ((4 * p + 1) + 1) :=
  (orientableNormalComplementPositionEquiv p).symm
    ⟨oneFaceOccurrenceIndex
        (orientableNormalComplementPartnerOccurrence p j),
      orientableNormalComplementPartnerIndex_ne_boundary p j⟩

theorem orientableNormalComplementOccurrence_edgePair (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    orientableNormalComplementOccurrence p
        (orientableNormalComplementEdgePair p j) =
      orientableNormalComplementPartnerOccurrence p j := by
  unfold orientableNormalComplementOccurrence orientableNormalComplementEdgePair
  rw [Equiv.apply_symm_apply]
  exact oneFaceOccurrence_oneFaceOccurrenceIndex
    (orientableBoundaryWord p 1)
    (orientableNormalComplementPartnerOccurrence p j)

theorem orientableNormalComplementPosition_edgePair (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    (orientableNormalComplementPositionEquiv p
        (orientableNormalComplementEdgePair p j)).1 =
      oneFaceOccurrenceIndex
        (orientableNormalComplementPartnerOccurrence p j) := by
  have hindex := congrArg oneFaceOccurrenceIndex
    (orientableNormalComplementOccurrence_edgePair p j)
  simpa [orientableNormalComplementOccurrence] using hindex

theorem orientableNormalComplementOccurrence_injective (p : ℕ) :
    Function.Injective (orientableNormalComplementOccurrence p) := by
  intro i j hij
  apply (orientableNormalComplementPositionEquiv p).injective
  apply Subtype.ext
  have hindex := congrArg oneFaceOccurrenceIndex hij
  simpa [orientableNormalComplementOccurrence] using hindex

theorem orientableNormalComplementPartnerOccurrence_edgePair (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    orientableNormalComplementPartnerOccurrence p
        (orientableNormalComplementEdgePair p j) =
      orientableNormalComplementOccurrence p j := by
  simpa [orientableNormalComplementPartnerOccurrence,
    orientableNormalComplementOccurrence_edgePair] using
    occurrencePartner_involutive
      (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
      (orientableNormalComplementOccurrence p j)
      (orientableNormalComplementOccurrence_not_boundary p j)

theorem orientableNormalComplementEdgePair_involutive (p : ℕ) :
    Function.Involutive (orientableNormalComplementEdgePair p) := by
  intro j
  apply orientableNormalComplementOccurrence_injective p
  rw [orientableNormalComplementOccurrence_edgePair,
    orientableNormalComplementPartnerOccurrence_edgePair]

theorem orientableNormalComplementEdgePair_noFixed (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    orientableNormalComplementEdgePair p j ≠ j := by
  intro hfixed
  apply (occurrencePartner_spec
    (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
    (orientableNormalComplementOccurrence p j)
    (orientableNormalComplementOccurrence_not_boundary p j)).1
  change orientableNormalComplementOccurrence p j =
    orientableNormalComplementPartnerOccurrence p j
  rw [← orientableNormalComplementOccurrence_edgePair, hfixed]

/-- The direction flag induced by the two signed orientable occurrences. -/
noncomputable def orientableNormalComplementOrientation (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    CylinderStripLowerBoundaryOrientation :=
  occurrencePartnerOrientation
    (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
    (orientableNormalComplementOccurrence p j)
    (orientableNormalComplementOccurrence_not_boundary p j)

theorem orientableNormalComplementOrientation_pair (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    orientableNormalComplementOrientation p
        (orientableNormalComplementEdgePair p j) =
      orientableNormalComplementOrientation p j := by
  unfold orientableNormalComplementOrientation
  calc
    occurrencePartnerOrientation
        (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
        (orientableNormalComplementOccurrence p
          (orientableNormalComplementEdgePair p j))
        (orientableNormalComplementOccurrence_not_boundary p _) =
      occurrencePartnerOrientation
        (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
        (orientableNormalComplementPartnerOccurrence p j)
        (occurrencePartner_not_boundary
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableNormalComplementOccurrence p j)
          (orientableNormalComplementOccurrence_not_boundary p j)) :=
      occurrencePartnerOrientation_congr _ _ _
        (orientableNormalComplementOccurrence_edgePair p j)
    _ = occurrencePartnerOrientation
        (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
        (orientableNormalComplementOccurrence p j)
        (orientableNormalComplementOccurrence_not_boundary p j) :=
      occurrencePartnerOrientation_partner
        (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
        (orientableNormalComplementOccurrence p j)
        (orientableNormalComplementOccurrence_not_boundary p j)

/-- The fixed-point-free pairing on all non-free sides of the orientable
one-boundary normal form. -/
noncomputable def orientableNormalComplementPairing (p : ℕ) :
    CylinderStripLowerBoundaryPairing (4 * p + 1) where
  edgePair := orientableNormalComplementEdgePair p
  orientation := orientableNormalComplementOrientation p
  edgePair_involutive := orientableNormalComplementEdgePair_involutive p
  edgePair_noFixed := orientableNormalComplementEdgePair_noFixed p
  orientation_pair := orientableNormalComplementOrientation_pair p

/-- The canonical polygon-side pairing underlying one complementary cylinder
edge. -/
noncomputable def orientableNormalComplementBoundaryPairing (p : ℕ)
    (j : Fin ((4 * p + 1) + 1)) :
    (orientableCellComplex p 1).BoundaryPairing where
  source := orientableNormalComplementOccurrence p j
  target := orientableNormalComplementPartnerOccurrence p j
  source_ne_target := by
    exact (occurrencePartner_spec
      (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
      (orientableNormalComplementOccurrence p j)
      (orientableNormalComplementOccurrence_not_boundary p j)).1
  source_not_boundary := orientableNormalComplementOccurrence_not_boundary p j
  target_not_boundary := by
    exact occurrencePartner_not_boundary
      (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
      (orientableNormalComplementOccurrence p j)
      (orientableNormalComplementOccurrence_not_boundary p j)
  direction :=
    match orientableNormalComplementOrientation p j with
    | .preserving => .same
    | .reversing => .opposite
  compatible := by
    cases horientation : orientableNormalComplementOrientation p j with
    | preserving =>
        change (orientableCellComplex p 1).occurrenceDart
            (orientableNormalComplementPartnerOccurrence p j) =
          (orientableCellComplex p 1).occurrenceDart
            (orientableNormalComplementOccurrence p j)
        exact (occurrencePartnerOrientation_eq_preserving_iff
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableNormalComplementOccurrence p j)
          (orientableNormalComplementOccurrence_not_boundary p j)).1
            horientation
    | reversing =>
        change (orientableCellComplex p 1).occurrenceDart
            (orientableNormalComplementPartnerOccurrence p j) =
          (orientableCellComplex p 1).inv
            ((orientableCellComplex p 1).occurrenceDart
              (orientableNormalComplementOccurrence p j))
        exact (occurrencePartnerOrientation_eq_reversing_iff
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableNormalComplementOccurrence p j)
          (orientableNormalComplementOccurrence_not_boundary p j)).1
            horientation

/-- The free interval in the one-boundary orientable normal form, written in
the negative-angle coordinates used by `OrientableRel`. -/
def orientableNormalBoundaryCarrierArc (p : ℕ) (t : ℝ) :
    ClosedUnitDisc :=
  ClosedUnitDisc.bdyPtOfReal ((t - 2) / (4 * p + 3))

def orientableNormalBoundaryArc (p : ℕ) (t : ℝ) :
    Quot (OrientableRel p 1) :=
  Quot.mk _ (orientableNormalBoundaryCarrierArc p t)

theorem continuous_orientableNormalBoundaryArc (p : ℕ) :
    Continuous (orientableNormalBoundaryArc p) := by
  apply continuous_quot_mk.comp
  apply Continuous.subtype_mk
  fun_prop

theorem orientableNormalBoundaryArc_zero_eq_one (p : ℕ) :
    orientableNormalBoundaryArc p 0 = orientableNormalBoundaryArc p 1 := by
  have h := Quot.sound (OrientableRel.c
    (p := p) (n := 1) (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) (0 : Fin 1))
  unfold orientableNormalBoundaryArc orientableNormalBoundaryCarrierArc
  convert h.symm using 1 <;> norm_num

/-- The canonical free boundary loop of the orientable normal form with one
boundary component. -/
def orientableNormalBoundaryLoop (p : ℕ) :
    UnitAddCircle → Quot (OrientableRel p 1) :=
  AddCircle.liftIco 1 0 (orientableNormalBoundaryArc p)

theorem continuous_orientableNormalBoundaryLoop (p : ℕ) :
    Continuous (orientableNormalBoundaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (orientableNormalBoundaryArc_zero_eq_one p)
    (continuous_orientableNormalBoundaryArc p).continuousOn

theorem orientableNormalBoundaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    orientableNormalBoundaryLoop p ((t : ℝ) : UnitAddCircle) =
      orientableNormalBoundaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (orientableNormalBoundaryArc_zero_eq_one p) t

/-- The complementary boundary path in the orientable one-boundary polygon.
It starts at the terminal point of `h`, traverses every paired side once in
the polygonal boundary order, and ends at the initial point of `h`. -/
def orientableNormalComplementaryCarrierArc (p : ℕ) (t : ℝ) :
    ClosedUnitDisc :=
  ClosedUnitDisc.bdyPtOfReal
    ((-1 + (4 * p + 2) * t) / (4 * p + 3))

def orientableNormalComplementaryArc (p : ℕ) (t : ℝ) :
    Quot (OrientableRel p 1) :=
  Quot.mk _ (orientableNormalComplementaryCarrierArc p t)

theorem continuous_orientableNormalComplementaryArc (p : ℕ) :
    Continuous (orientableNormalComplementaryArc p) := by
  apply continuous_quot_mk.comp
  apply Continuous.subtype_mk
  fun_prop

/-- On each angular subdivision edge, the complementary carrier path is the
carrier image of the corresponding canonical polygon occurrence. -/
theorem orientableNormalComplementaryCarrierArc_angularSubdivisionParameter
    (p : ℕ) (j : Fin ((4 * p + 1) + 1)) (x : ClosedUnitInterval) :
    orientableNormalComplementaryCarrierArc p
        (angularSubdivisionParameter (4 * p + 1) j x) =
      oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p 1)
        (orientableOccurrencePoint p 1
          (orientableNormalComplementPositionEquiv p j).1 x) := by
  rw [orientableCarrier_occurrencePoint]
  unfold orientableNormalComplementaryCarrierArc
  by_cases hj : j = 0
  · subst j
    rw [orientableNormalComplementPositionEquiv_zero_val,
      orientableBoundaryWord_length]
    let a : ℝ :=
      (-1 + (4 * (p : ℝ) + 2) *
          angularSubdivisionParameter (4 * p + 1) 0 x) /
        (4 * (p : ℝ) + 3)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    change ClosedUnitDisc.bdyPtOfReal a =
      ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 2 + (x : ℝ)) / (4 * (p : ℝ) + 3))
    calc
      ClosedUnitDisc.bdyPtOfReal a =
          ClosedUnitDisc.bdyPtOfReal (a + (1 : ℤ)) :=
        (ClosedUnitDisc.bdyPtOfReal_add_int a 1).symm
      _ = ClosedUnitDisc.bdyPtOfReal
          ((4 * (p : ℝ) + 2 + (x : ℝ)) /
            (4 * (p : ℝ) + 3)) := by
        apply congrArg ClosedUnitDisc.bdyPtOfReal
        unfold a angularSubdivisionParameter
        norm_num only [Fin.val_zero, Nat.cast_zero, add_zero, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat]
        field_simp [show 4 * (p : ℝ) + 2 ≠ 0 by positivity,
          show 4 * (p : ℝ) + 3 ≠ 0 by positivity]
        ring
  · rw [orientableNormalComplementPositionEquiv_val_of_ne_zero p j hj,
      orientableBoundaryWord_length]
    apply congrArg ClosedUnitDisc.bdyPtOfReal
    have hjpos : 1 ≤ j.val := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hjval
      apply hj
      apply Fin.ext
      exact hjval
    unfold angularSubdivisionParameter
    rw [Nat.cast_sub hjpos]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp [show 4 * (p : ℝ) + 2 ≠ 0 by positivity,
      show 4 * (p : ℝ) + 3 ≠ 0 by positivity]
    ring

theorem orientableNormalComplementaryCarrierArc_zero (p : ℕ) :
    orientableNormalComplementaryCarrierArc p 0 =
      orientableNormalBoundaryCarrierArc p 1 := by
  unfold orientableNormalComplementaryCarrierArc
    orientableNormalBoundaryCarrierArc
  congr 1
  ring

theorem orientableNormalComplementaryCarrierArc_one (p : ℕ) :
    orientableNormalComplementaryCarrierArc p 1 =
      orientableNormalBoundaryCarrierArc p 0 := by
  have hperiod := ClosedUnitDisc.bdyPtOfReal_add_int
    (-2 / (4 * (p : ℝ) + 3)) 1
  unfold orientableNormalComplementaryCarrierArc
    orientableNormalBoundaryCarrierArc
  calc
    ClosedUnitDisc.bdyPtOfReal
        ((-1 + (4 * (p : ℝ) + 2) * 1) / (4 * (p : ℝ) + 3)) =
      ClosedUnitDisc.bdyPtOfReal
        (-2 / (4 * (p : ℝ) + 3) + (1 : ℤ)) := by
      congr 1
      field_simp [show 4 * (p : ℝ) + 3 ≠ 0 by positivity]
      ring
    _ = ClosedUnitDisc.bdyPtOfReal
        (-2 / (4 * (p : ℝ) + 3)) := hperiod
    _ = ClosedUnitDisc.bdyPtOfReal
        ((0 - 2) / (4 * (p : ℝ) + 3)) := by
      congr 1
      ring

theorem orientableNormalComplementaryArc_zero_eq_one (p : ℕ) :
    orientableNormalComplementaryArc p 0 =
      orientableNormalComplementaryArc p 1 := by
  calc
    orientableNormalComplementaryArc p 0 =
        orientableNormalBoundaryArc p 1 := by
      exact congrArg (Quot.mk (OrientableRel p 1))
        (orientableNormalComplementaryCarrierArc_zero p)
    _ = orientableNormalBoundaryArc p 0 :=
      (orientableNormalBoundaryArc_zero_eq_one p).symm
    _ = orientableNormalComplementaryArc p 1 := by
      exact congrArg (Quot.mk (OrientableRel p 1))
        (orientableNormalComplementaryCarrierArc_one p).symm

/-- The loop formed by all paired sides of the orientable one-boundary
normal-form polygon. -/
def orientableNormalComplementaryLoop (p : ℕ) :
    UnitAddCircle → Quot (OrientableRel p 1) :=
  AddCircle.liftIco 1 0 (orientableNormalComplementaryArc p)

theorem continuous_orientableNormalComplementaryLoop (p : ℕ) :
    Continuous (orientableNormalComplementaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (orientableNormalComplementaryArc_zero_eq_one p)
    (continuous_orientableNormalComplementaryArc p).continuousOn

theorem orientableNormalComplementaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    orientableNormalComplementaryLoop p ((t : ℝ) : UnitAddCircle) =
      orientableNormalComplementaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (orientableNormalComplementaryArc_zero_eq_one p) t

theorem orientableNormalComplementaryLoop_angularSubdivisionArc
    (p : ℕ) (j : Fin ((4 * p + 1) + 1)) (x : ClosedUnitInterval) :
    orientableNormalComplementaryLoop p
        (angularSubdivisionArc (4 * p + 1) j x) =
      Quot.mk (OrientableRel p 1)
        (oneFacePolygonalPreRealizationHomeomorph
          (orientableBoundaryWord p 1)
          (orientableOccurrencePoint p 1
            (orientableNormalComplementPositionEquiv p j).1 x)) := by
  change orientableNormalComplementaryLoop p
      ((((angularSubdivisionParameterIcc (4 * p + 1) j x :
        Set.Icc (0 : ℝ) 1) : ℝ)) : UnitAddCircle) = _
  rw [orientableNormalComplementaryLoop_apply_unitInterval]
  unfold orientableNormalComplementaryArc
  exact congrArg (Quot.mk (OrientableRel p 1))
    (orientableNormalComplementaryCarrierArc_angularSubdivisionParameter p j x)

/-- An arbitrary occurrence of the canonical one-face word is recovered from
its index when interpreted as a polygon side point. -/
theorem orientableOccurrencePoint_oneFaceOccurrenceIndex
    (p : ℕ) (o : (orientableCellComplex p 1).BoundaryOccurrence)
    (x : unitInterval) :
    orientableOccurrencePoint p 1 (oneFaceOccurrenceIndex o) x =
      ((orientableCellComplex p 1).occurrenceSide o).point x := by
  rcases o with ⟨face, i⟩
  cases face
  rfl

/-- The complementary loop identifies each angular edge with its prescribed
partner, with the parameter direction dictated by the signed darts. -/
theorem orientableNormalComplementaryLoop_pair
    (p : ℕ) (j : Fin ((4 * p + 1) + 1)) (x : ClosedUnitInterval) :
    orientableNormalComplementaryLoop p
        (angularSubdivisionArc (4 * p + 1) j x) =
      orientableNormalComplementaryLoop p
        (match orientableNormalComplementOrientation p j with
        | .preserving => angularSubdivisionArc (4 * p + 1)
            (orientableNormalComplementEdgePair p j) x
        | .reversing => angularSubdivisionArc (4 * p + 1)
            (orientableNormalComplementEdgePair p j)
            (reverseClosedUnitInterval x)) := by
  have hgenerator := PolygonGluing.Generator.glue
    (orientableNormalComplementBoundaryPairing p j).identification
    (pairing_identification_mem
      (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
      (orientableNormalComplementBoundaryPairing p j)) x
  have heqv := orientableGenerator_to_eqvGen
    (Or.inr (by omega)) hgenerator
  cases horientation : orientableNormalComplementOrientation p j with
  | preserving =>
      rw [orientableNormalComplementaryLoop_angularSubdivisionArc,
        orientableNormalComplementaryLoop_angularSubdivisionArc,
        orientableNormalComplementPosition_edgePair]
      apply Quot.eqvGen_sound
      simpa [orientableNormalComplementBoundaryPairing, horientation,
        orientableNormalComplementOccurrence,
        orientableOccurrencePoint_oneFaceOccurrenceIndex,
        SurfaceCellComplex.BoundaryPairing.identification,
        PolygonGluing.Identification.parameter,
        PolygonGluing.ParameterDirection.homeomorph] using heqv
  | reversing =>
      rw [orientableNormalComplementaryLoop_angularSubdivisionArc,
        orientableNormalComplementaryLoop_angularSubdivisionArc,
        orientableNormalComplementPosition_edgePair]
      apply Quot.eqvGen_sound
      simpa [orientableNormalComplementBoundaryPairing, horientation,
        orientableNormalComplementOccurrence,
        orientableOccurrencePoint_oneFaceOccurrenceIndex,
        SurfaceCellComplex.BoundaryPairing.identification,
        PolygonGluing.Identification.parameter,
        PolygonGluing.ParameterDirection.homeomorph] using heqv

/-- Extend the complementary loop constantly in the radial coordinate of the
cylinder. -/
def orientableNormalComplementCylinderMap (p : ℕ) :
    ClosedUnitInterval × UnitAddCircle → Quot (OrientableRel p 1) :=
  fun q ↦ orientableNormalComplementaryLoop p q.2

theorem continuous_orientableNormalComplementCylinderMap (p : ℕ) :
    Continuous (orientableNormalComplementCylinderMap p) :=
  (continuous_orientableNormalComplementaryLoop p).comp continuous_snd

theorem orientableNormalComplementCylinderMap_respects_gluing (p : ℕ) :
    CylinderStripPointMapRespectsGluing
      (orientableNormalComplementPairing p)
      (orientableNormalComplementCylinderMap p) := by
  intro j x
  simpa [orientableNormalComplementCylinderMap,
    orientableNormalComplementPairing] using
    orientableNormalComplementaryLoop_pair p j x

/-- Descend the radial-constant complementary loop through its glued-cylinder
presentation. -/
noncomputable def orientableNormalComplementLift (p : ℕ) :
    CylinderStripGluedPointSpace (orientableNormalComplementPairing p) →
      Quot (OrientableRel p 1) :=
  cylinderStripGluedPointLift
    (orientableNormalComplementPairing p)
    (orientableNormalComplementCylinderMap p)
    (orientableNormalComplementCylinderMap_respects_gluing p)

theorem continuous_orientableNormalComplementLift (p : ℕ) :
    Continuous (orientableNormalComplementLift p) :=
  continuous_cylinderStripGluedPointLift
    (orientableNormalComplementPairing p)
    (continuous_orientableNormalComplementCylinderMap p)
    (orientableNormalComplementCylinderMap_respects_gluing p)

theorem orientableNormalComplementaryLoop_eq_lift_comp_boundary (p : ℕ) :
    orientableNormalComplementaryLoop p =
      orientableNormalComplementLift p ∘
        cylinderStripGluedPointBoundary
          (orientableNormalComplementPairing p) := by
  funext t
  rfl

/-- The paired-side complementary loop of every orientable one-boundary
normal form carries the arbitrary-pairing parity obstruction. -/
theorem hasOddBoundaryDegreeObstruction_orientableNormalComplementaryLoop
    (p : ℕ) :
    HasOddBoundaryDegreeObstruction
      (orientableNormalComplementaryLoop p) :=
  hasOddBoundaryDegreeObstruction_of_comp_continuous_cylinderStripGluedPointBoundary_pairing
    (orientableNormalComplementPairing p)
    (orientableNormalComplementLift p)
    (continuous_orientableNormalComplementLift p)
    (orientableNormalComplementaryLoop_eq_lift_comp_boundary p)

/-- The free orientable boundary interval with its direction reversed. -/
def orientableNormalReverseBoundaryArc (p : ℕ) (t : ℝ) :
    Quot (OrientableRel p 1) :=
  orientableNormalBoundaryArc p (1 - t)

theorem continuous_orientableNormalReverseBoundaryArc (p : ℕ) :
    Continuous (orientableNormalReverseBoundaryArc p) := by
  exact (continuous_orientableNormalBoundaryArc p).comp
    (continuous_const.sub continuous_id)

theorem orientableNormalReverseBoundaryArc_zero_eq_one (p : ℕ) :
  orientableNormalReverseBoundaryArc p 0 =
      orientableNormalReverseBoundaryArc p 1 := by
  simpa [orientableNormalReverseBoundaryArc] using
    (orientableNormalBoundaryArc_zero_eq_one p).symm

/-- The reverse traversal of the canonical orientable free boundary loop. -/
def orientableNormalReverseBoundaryLoop (p : ℕ) :
    UnitAddCircle → Quot (OrientableRel p 1) :=
  AddCircle.liftIco 1 0 (orientableNormalReverseBoundaryArc p)

theorem continuous_orientableNormalReverseBoundaryLoop (p : ℕ) :
    Continuous (orientableNormalReverseBoundaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (orientableNormalReverseBoundaryArc_zero_eq_one p)
    (continuous_orientableNormalReverseBoundaryArc p).continuousOn

theorem orientableNormalReverseBoundaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    orientableNormalReverseBoundaryLoop p ((t : ℝ) : UnitAddCircle) =
      orientableNormalReverseBoundaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (orientableNormalReverseBoundaryArc_zero_eq_one p) t

/-! ## The polygonal disk homotopy -/

/-- Linear interpolation between two points of the trusted closed-disk
carrier, retained inside that carrier by convexity. -/
def closedUnitDiscLine (a b : ClosedUnitDisc) (s : Set.Icc (0 : ℝ) 1) :
    ClosedUnitDisc :=
  ⟨AffineMap.lineMap (k := ℝ) a.1 b.1 s,
    (convex_closedBall (0 : ℂ) 1).lineMap_mem a.2 b.2 s.2⟩

theorem continuous_closedUnitDiscLine :
    Continuous (fun q : ClosedUnitDisc × ClosedUnitDisc × Set.Icc (0 : ℝ) 1 ↦
      closedUnitDiscLine q.1 q.2.1 q.2.2) := by
  apply continuous_induced_rng.2
  unfold closedUnitDiscLine
  fun_prop

@[simp] theorem closedUnitDiscLine_zero (a b : ClosedUnitDisc) :
    closedUnitDiscLine a b 0 = a := by
  apply Subtype.ext
  simp [closedUnitDiscLine]

@[simp] theorem closedUnitDiscLine_one (a b : ClosedUnitDisc) :
    closedUnitDiscLine a b 1 = b := by
  apply Subtype.ext
  simp [closedUnitDiscLine]

theorem closedUnitDiscLine_self (a : ClosedUnitDisc)
    (s : Set.Icc (0 : ℝ) 1) :
    closedUnitDiscLine a a s = a := by
  apply Subtype.ext
  simp [closedUnitDiscLine]

/-- Inside the polygonal disk, interpolate from the complementary paired-side
path to the reverse traversal of the free side. -/
def orientableNormalCarrierHomotopy (p : ℕ)
    (q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) : ClosedUnitDisc :=
  closedUnitDiscLine
    (orientableNormalComplementaryCarrierArc p q.2)
    (orientableNormalBoundaryCarrierArc p (unitInterval.symm q.2))
    q.1

theorem continuous_orientableNormalCarrierHomotopy (p : ℕ) :
    Continuous (orientableNormalCarrierHomotopy p) := by
  apply continuous_induced_rng.2
  unfold orientableNormalCarrierHomotopy closedUnitDiscLine
    orientableNormalComplementaryCarrierArc
    orientableNormalBoundaryCarrierArc ClosedUnitDisc.bdyPtOfReal
  fun_prop

/-- The disk homotopy after applying the orientable normal-form quotient map. -/
def orientableNormalIccHomotopy (p : ℕ)
    (q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :
    Quot (OrientableRel p 1) :=
  Quot.mk _ (orientableNormalCarrierHomotopy p q)

theorem continuous_orientableNormalIccHomotopy (p : ℕ) :
    Continuous (orientableNormalIccHomotopy p) :=
  continuous_quot_mk.comp (continuous_orientableNormalCarrierHomotopy p)

theorem orientableNormalIccHomotopy_second_endpoints
    (p : ℕ) (s : Set.Icc (0 : ℝ) 1) :
    orientableNormalIccHomotopy p (s, 0) =
      orientableNormalIccHomotopy p (s, 1) := by
  calc
    orientableNormalIccHomotopy p (s, 0) =
        orientableNormalBoundaryArc p 1 := by
      unfold orientableNormalIccHomotopy orientableNormalCarrierHomotopy
        orientableNormalBoundaryArc
      change Quot.mk _
        (closedUnitDiscLine
          (orientableNormalComplementaryCarrierArc p 0)
          (orientableNormalBoundaryCarrierArc p (unitInterval.symm (0 : I))) s) =
        Quot.mk _ (orientableNormalBoundaryCarrierArc p 1)
      rw [orientableNormalComplementaryCarrierArc_zero]
      simp only [unitInterval.symm_zero]
      change Quot.mk _
        (closedUnitDiscLine
          (orientableNormalBoundaryCarrierArc p 1)
          (orientableNormalBoundaryCarrierArc p 1) s) =
        Quot.mk _ (orientableNormalBoundaryCarrierArc p 1)
      rw [closedUnitDiscLine_self]
    _ = orientableNormalBoundaryArc p 0 :=
      (orientableNormalBoundaryArc_zero_eq_one p).symm
    _ = orientableNormalIccHomotopy p (s, 1) := by
      unfold orientableNormalIccHomotopy orientableNormalCarrierHomotopy
        orientableNormalBoundaryArc
      change Quot.mk _ (orientableNormalBoundaryCarrierArc p 0) =
        Quot.mk _
          (closedUnitDiscLine
            (orientableNormalComplementaryCarrierArc p 1)
            (orientableNormalBoundaryCarrierArc p (unitInterval.symm (1 : I))) s)
      rw [orientableNormalComplementaryCarrierArc_one]
      simp only [unitInterval.symm_one]
      change Quot.mk _ (orientableNormalBoundaryCarrierArc p 0) =
        Quot.mk _
          (closedUnitDiscLine
            (orientableNormalBoundaryCarrierArc p 0)
            (orientableNormalBoundaryCarrierArc p 0) s)
      rw [closedUnitDiscLine_self]

/-- Remove the syntactic `0 + 1` in the endpoint quotient's interval. -/
def endpointIdentUnitInterval :
    Set.Icc (0 : ℝ) (0 + 1) → Set.Icc (0 : ℝ) 1 :=
  fun t ↦ ⟨t, by simpa only [zero_add] using t.2⟩

theorem continuous_endpointIdentUnitInterval :
    Continuous endpointIdentUnitInterval :=
  continuous_induced_rng.2 continuous_subtype_val

/-- Descend the interval coordinate of the disk homotopy through endpoint
identification. -/
def orientableNormalQuotHomotopy (p : ℕ) :
    Set.Icc (0 : ℝ) 1 × Quot (AddCircle.EndpointIdent (1 : ℝ) 0) →
      Quot (OrientableRel p 1) :=
  fun q ↦ Quot.lift
    (r := AddCircle.EndpointIdent (1 : ℝ) 0)
    (fun t ↦ orientableNormalIccHomotopy p
      (q.1, endpointIdentUnitInterval t))
    (by
      rintro _ _ ⟨_⟩
      simpa [endpointIdentUnitInterval] using
        orientableNormalIccHomotopy_second_endpoints p q.1)
    q.2

theorem continuous_orientableNormalQuotHomotopy (p : ℕ) :
    Continuous (orientableNormalQuotHomotopy p) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_right
  simpa [orientableNormalQuotHomotopy] using
    (continuous_orientableNormalIccHomotopy p).comp
      (continuous_fst.prodMk
        (continuous_endpointIdentUnitInterval.comp continuous_snd))

/-- Circle-valued-parameter homotopy from the paired complementary loop to
the reverse free loop in the orientable normal form. -/
def orientableNormalBoundaryHomotopy (p : ℕ) :
    C(I × UnitAddCircle, Quot (OrientableRel p 1)) where
  toFun q := orientableNormalQuotHomotopy p
    (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2)
  continuous_toFun :=
    (continuous_orientableNormalQuotHomotopy p).comp
      (continuous_fst.prodMk
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd))

theorem orientableNormalBoundaryHomotopy_zero
    (p : ℕ) (t : UnitAddCircle) :
    orientableNormalBoundaryHomotopy p (0, t) =
      orientableNormalComplementaryLoop p t := by
  change orientableNormalQuotHomotopy p
      ((0 : I), AddCircle.homeoIccQuot (1 : ℝ) 0 t) =
    orientableNormalComplementaryLoop p t
  generalize hq : AddCircle.homeoIccQuot (1 : ℝ) 0 t = q
  have ht : t = (AddCircle.homeoIccQuot (1 : ℝ) 0).symm q := by
    rw [← hq]
    exact (AddCircle.homeoIccQuot (1 : ℝ) 0).symm_apply_apply t |>.symm
  rw [ht]
  induction q using Quot.inductionOn with
  | _ x =>
      change orientableNormalIccHomotopy p
          ((0 : I), endpointIdentUnitInterval x) =
        orientableNormalComplementaryLoop p
          (((endpointIdentUnitInterval x : I) : ℝ) : UnitAddCircle)
      rw [orientableNormalComplementaryLoop_apply_unitInterval]
      unfold orientableNormalIccHomotopy orientableNormalCarrierHomotopy
        orientableNormalComplementaryArc
      rw [closedUnitDiscLine_zero]

theorem orientableNormalBoundaryHomotopy_one
    (p : ℕ) (t : UnitAddCircle) :
    orientableNormalBoundaryHomotopy p (1, t) =
      orientableNormalReverseBoundaryLoop p t := by
  change orientableNormalQuotHomotopy p
      ((1 : I), AddCircle.homeoIccQuot (1 : ℝ) 0 t) =
    orientableNormalReverseBoundaryLoop p t
  generalize hq : AddCircle.homeoIccQuot (1 : ℝ) 0 t = q
  have ht : t = (AddCircle.homeoIccQuot (1 : ℝ) 0).symm q := by
    rw [← hq]
    exact (AddCircle.homeoIccQuot (1 : ℝ) 0).symm_apply_apply t |>.symm
  rw [ht]
  induction q using Quot.inductionOn with
  | _ x =>
      change orientableNormalIccHomotopy p
          ((1 : I), endpointIdentUnitInterval x) =
        orientableNormalReverseBoundaryLoop p
          (((endpointIdentUnitInterval x : I) : ℝ) : UnitAddCircle)
      rw [orientableNormalReverseBoundaryLoop_apply_unitInterval]
      unfold orientableNormalIccHomotopy orientableNormalCarrierHomotopy
        orientableNormalReverseBoundaryArc orientableNormalBoundaryArc
      rw [closedUnitDiscLine_one]
      rfl

/-- Reversal of the additive unit circle. -/
def unitAddCircleNegHomeomorph : UnitAddCircle ≃ₜ UnitAddCircle where
  toFun t := -t
  invFun t := -t
  left_inv t := by simp
  right_inv t := by simp
  continuous_toFun := continuous_id.neg
  continuous_invFun := continuous_id.neg

@[simp] theorem unitAddCircleNegHomeomorph_apply (t : UnitAddCircle) :
    unitAddCircleNegHomeomorph t = -t :=
  rfl

/-- The interval-defined reverse loop is exactly precomposition by circle
reversal. -/
theorem orientableNormalReverseBoundaryLoop_eq_comp_neg (p : ℕ) :
    orientableNormalReverseBoundaryLoop p =
      orientableNormalBoundaryLoop p ∘ unitAddCircleNegHomeomorph := by
  funext t
  obtain ⟨x, hx, hxt⟩ := AddCircle.eq_coe_Ico t
  rw [← hxt]
  let u : I := ⟨x, hx.1, hx.2.le⟩
  change orientableNormalReverseBoundaryLoop p
      (((u : I) : ℝ) : UnitAddCircle) =
    orientableNormalBoundaryLoop p
      (unitAddCircleNegHomeomorph (((u : I) : ℝ) : UnitAddCircle))
  rw [orientableNormalReverseBoundaryLoop_apply_unitInterval]
  have hneg :
      unitAddCircleNegHomeomorph (((u : I) : ℝ) : UnitAddCircle) =
        (((unitInterval.symm u : I) : ℝ) : UnitAddCircle) := by
    rw [unitAddCircleNegHomeomorph_apply, ← AddCircle.coe_neg]
    rw [show -((u : I) : ℝ) =
        ((unitInterval.symm u : I) : ℝ) - 1 by
      rw [unitInterval.coe_symm_eq]
      ring]
    simp [sub_eq_add_neg]
  rw [hneg, orientableNormalBoundaryLoop_apply_unitInterval]
  simp [orientableNormalReverseBoundaryArc, unitInterval.coe_symm_eq]

theorem hasOddBoundaryDegreeObstruction_orientableNormalReverseBoundaryLoop
    (p : ℕ) :
    HasOddBoundaryDegreeObstruction
      (orientableNormalReverseBoundaryLoop p) :=
  hasOddBoundaryDegreeObstruction_of_homotopy
    (orientableNormalBoundaryHomotopy p)
    (orientableNormalBoundaryHomotopy_zero p)
    (orientableNormalBoundaryHomotopy_one p)
    (hasOddBoundaryDegreeObstruction_orientableNormalComplementaryLoop p)

/-- The canonical free loop of every orientable one-boundary normal form has
the odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_orientableNormalBoundaryLoop
    (p : ℕ) :
    HasOddBoundaryDegreeObstruction (orientableNormalBoundaryLoop p) := by
  apply hasOddBoundaryDegreeObstruction_of_circleHomeomorph_reparametrization
    (boundary := orientableNormalReverseBoundaryLoop p)
    unitAddCircleNegHomeomorph
  · funext t
    rw [orientableNormalReverseBoundaryLoop_eq_comp_neg]
    simp [Function.comp_def]
  · exact
      hasOddBoundaryDegreeObstruction_orientableNormalReverseBoundaryLoop p

/-! ## The nonorientable cyclic-complement pairing -/

def nonOrientableNormalComplementOccurrence (p : ℕ)
    (j : Fin ((2 * p + 1) + 1)) :
    (nonOrientableCellComplex p 1).BoundaryOccurrence :=
  oneFaceOccurrence (nonOrientableBoundaryWord p 1)
    (nonOrientableNormalComplementPositionEquiv p j).1

theorem nonOrientableNormalComplementOccurrence_not_boundary (p : ℕ)
    (j : Fin ((2 * p + 1) + 1)) :
    ¬(nonOrientableCellComplex p 1).IsBoundaryDart
      ((nonOrientableCellComplex p 1).occurrenceDart
        (nonOrientableNormalComplementOccurrence p j)) :=
  nonOrientableNormalOccurrence_not_boundary p
    (nonOrientableNormalComplementPositionEquiv p j).1
    (nonOrientableNormalComplementPositionEquiv p j).2

noncomputable def nonOrientableNormalComplementPartnerOccurrence
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    (nonOrientableCellComplex p 1).BoundaryOccurrence :=
  occurrencePartner
    (nonOrientableCellComplex_occurrencePairingValid hp)
    (nonOrientableNormalComplementOccurrence p j)
    (nonOrientableNormalComplementOccurrence_not_boundary p j)

theorem nonOrientableNormalComplementPartnerIndex_ne_boundary
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    oneFaceOccurrenceIndex
        (nonOrientableNormalComplementPartnerOccurrence p hp j) ≠
      nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1 := by
  intro hindex
  have hoccurrence :
      nonOrientableNormalComplementPartnerOccurrence p hp j =
        oneFaceOccurrence (nonOrientableBoundaryWord p 1)
          (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1) := by
    calc
      nonOrientableNormalComplementPartnerOccurrence p hp j =
          oneFaceOccurrence (nonOrientableBoundaryWord p 1)
            (oneFaceOccurrenceIndex
              (nonOrientableNormalComplementPartnerOccurrence p hp j)) :=
        (oneFaceOccurrence_oneFaceOccurrenceIndex _ _).symm
      _ = oneFaceOccurrence (nonOrientableBoundaryWord p 1)
          (nonOrientableBoundaryPosition p 1 (0 : Fin 1) 1) :=
        congrArg (oneFaceOccurrence (nonOrientableBoundaryWord p 1)) hindex
  have hnot := occurrencePartner_not_boundary
    (nonOrientableCellComplex_occurrencePairingValid hp)
    (nonOrientableNormalComplementOccurrence p j)
    (nonOrientableNormalComplementOccurrence_not_boundary p j)
  change ¬(nonOrientableCellComplex p 1).IsBoundaryDart
    ((nonOrientableCellComplex p 1).occurrenceDart
      (nonOrientableNormalComplementPartnerOccurrence p hp j)) at hnot
  apply hnot
  rw [hoccurrence]
  exact nonOrientableNormalH_is_boundary p

noncomputable def nonOrientableNormalComplementEdgePair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    Fin ((2 * p + 1) + 1) :=
  (nonOrientableNormalComplementPositionEquiv p).symm
    ⟨oneFaceOccurrenceIndex
        (nonOrientableNormalComplementPartnerOccurrence p hp j),
      nonOrientableNormalComplementPartnerIndex_ne_boundary p hp j⟩

theorem nonOrientableNormalComplementOccurrence_edgePair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    nonOrientableNormalComplementOccurrence p
        (nonOrientableNormalComplementEdgePair p hp j) =
      nonOrientableNormalComplementPartnerOccurrence p hp j := by
  unfold nonOrientableNormalComplementOccurrence
    nonOrientableNormalComplementEdgePair
  rw [Equiv.apply_symm_apply]
  exact oneFaceOccurrence_oneFaceOccurrenceIndex
    (nonOrientableBoundaryWord p 1)
    (nonOrientableNormalComplementPartnerOccurrence p hp j)

theorem nonOrientableNormalComplementPosition_edgePair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    (nonOrientableNormalComplementPositionEquiv p
        (nonOrientableNormalComplementEdgePair p hp j)).1 =
      oneFaceOccurrenceIndex
        (nonOrientableNormalComplementPartnerOccurrence p hp j) := by
  have hindex := congrArg oneFaceOccurrenceIndex
    (nonOrientableNormalComplementOccurrence_edgePair p hp j)
  simpa [nonOrientableNormalComplementOccurrence] using hindex

theorem nonOrientableNormalComplementOccurrence_injective (p : ℕ) :
    Function.Injective (nonOrientableNormalComplementOccurrence p) := by
  intro i j hij
  apply (nonOrientableNormalComplementPositionEquiv p).injective
  apply Subtype.ext
  have hindex := congrArg oneFaceOccurrenceIndex hij
  simpa [nonOrientableNormalComplementOccurrence] using hindex

theorem nonOrientableNormalComplementPartnerOccurrence_edgePair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    nonOrientableNormalComplementPartnerOccurrence p hp
        (nonOrientableNormalComplementEdgePair p hp j) =
      nonOrientableNormalComplementOccurrence p j := by
  simpa [nonOrientableNormalComplementPartnerOccurrence,
    nonOrientableNormalComplementOccurrence_edgePair] using
    occurrencePartner_involutive
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableNormalComplementOccurrence p j)
      (nonOrientableNormalComplementOccurrence_not_boundary p j)

theorem nonOrientableNormalComplementEdgePair_involutive
    (p : ℕ) (hp : 1 ≤ p) :
    Function.Involutive (nonOrientableNormalComplementEdgePair p hp) := by
  intro j
  apply nonOrientableNormalComplementOccurrence_injective p
  rw [nonOrientableNormalComplementOccurrence_edgePair,
    nonOrientableNormalComplementPartnerOccurrence_edgePair]

theorem nonOrientableNormalComplementEdgePair_noFixed
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    nonOrientableNormalComplementEdgePair p hp j ≠ j := by
  intro hfixed
  apply (occurrencePartner_spec
    (nonOrientableCellComplex_occurrencePairingValid hp)
    (nonOrientableNormalComplementOccurrence p j)
    (nonOrientableNormalComplementOccurrence_not_boundary p j)).1
  change nonOrientableNormalComplementOccurrence p j =
    nonOrientableNormalComplementPartnerOccurrence p hp j
  rw [← nonOrientableNormalComplementOccurrence_edgePair, hfixed]

noncomputable def nonOrientableNormalComplementOrientation
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    CylinderStripLowerBoundaryOrientation :=
  occurrencePartnerOrientation
    (nonOrientableCellComplex_occurrencePairingValid hp)
    (nonOrientableNormalComplementOccurrence p j)
    (nonOrientableNormalComplementOccurrence_not_boundary p j)

theorem nonOrientableNormalComplementOrientation_pair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    nonOrientableNormalComplementOrientation p hp
        (nonOrientableNormalComplementEdgePair p hp j) =
      nonOrientableNormalComplementOrientation p hp j := by
  unfold nonOrientableNormalComplementOrientation
  calc
    occurrencePartnerOrientation
        (nonOrientableCellComplex_occurrencePairingValid hp)
        (nonOrientableNormalComplementOccurrence p
          (nonOrientableNormalComplementEdgePair p hp j))
        (nonOrientableNormalComplementOccurrence_not_boundary p _) =
      occurrencePartnerOrientation
        (nonOrientableCellComplex_occurrencePairingValid hp)
        (nonOrientableNormalComplementPartnerOccurrence p hp j)
        (occurrencePartner_not_boundary
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableNormalComplementOccurrence p j)
          (nonOrientableNormalComplementOccurrence_not_boundary p j)) :=
      occurrencePartnerOrientation_congr _ _ _
        (nonOrientableNormalComplementOccurrence_edgePair p hp j)
    _ = occurrencePartnerOrientation
        (nonOrientableCellComplex_occurrencePairingValid hp)
        (nonOrientableNormalComplementOccurrence p j)
        (nonOrientableNormalComplementOccurrence_not_boundary p j) :=
      occurrencePartnerOrientation_partner
        (nonOrientableCellComplex_occurrencePairingValid hp)
        (nonOrientableNormalComplementOccurrence p j)
        (nonOrientableNormalComplementOccurrence_not_boundary p j)

noncomputable def nonOrientableNormalComplementPairing
    (p : ℕ) (hp : 1 ≤ p) :
    CylinderStripLowerBoundaryPairing (2 * p + 1) where
  edgePair := nonOrientableNormalComplementEdgePair p hp
  orientation := nonOrientableNormalComplementOrientation p hp
  edgePair_involutive :=
    nonOrientableNormalComplementEdgePair_involutive p hp
  edgePair_noFixed := nonOrientableNormalComplementEdgePair_noFixed p hp
  orientation_pair := nonOrientableNormalComplementOrientation_pair p hp

noncomputable def nonOrientableNormalComplementBoundaryPairing
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1)) :
    (nonOrientableCellComplex p 1).BoundaryPairing where
  source := nonOrientableNormalComplementOccurrence p j
  target := nonOrientableNormalComplementPartnerOccurrence p hp j
  source_ne_target := by
    exact (occurrencePartner_spec
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableNormalComplementOccurrence p j)
      (nonOrientableNormalComplementOccurrence_not_boundary p j)).1
  source_not_boundary := nonOrientableNormalComplementOccurrence_not_boundary p j
  target_not_boundary := by
    exact occurrencePartner_not_boundary
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableNormalComplementOccurrence p j)
      (nonOrientableNormalComplementOccurrence_not_boundary p j)
  direction :=
    match nonOrientableNormalComplementOrientation p hp j with
    | .preserving => .same
    | .reversing => .opposite
  compatible := by
    cases horientation : nonOrientableNormalComplementOrientation p hp j with
    | preserving =>
        change (nonOrientableCellComplex p 1).occurrenceDart
            (nonOrientableNormalComplementPartnerOccurrence p hp j) =
          (nonOrientableCellComplex p 1).occurrenceDart
            (nonOrientableNormalComplementOccurrence p j)
        exact (occurrencePartnerOrientation_eq_preserving_iff
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableNormalComplementOccurrence p j)
          (nonOrientableNormalComplementOccurrence_not_boundary p j)).1
            horientation
    | reversing =>
        change (nonOrientableCellComplex p 1).occurrenceDart
            (nonOrientableNormalComplementPartnerOccurrence p hp j) =
          (nonOrientableCellComplex p 1).inv
            ((nonOrientableCellComplex p 1).occurrenceDart
              (nonOrientableNormalComplementOccurrence p j))
        exact (occurrencePartnerOrientation_eq_reversing_iff
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableNormalComplementOccurrence p j)
          (nonOrientableNormalComplementOccurrence_not_boundary p j)).1
            horientation

/-- The free interval in the one-boundary nonorientable normal form, written
in the negative-angle coordinates used by `NonOrientableRel`. -/
def nonOrientableNormalBoundaryCarrierArc (p : ℕ) (t : ℝ) :
    ClosedUnitDisc :=
  ClosedUnitDisc.bdyPtOfReal ((t - 2) / (2 * p + 3))

def nonOrientableNormalBoundaryArc (p : ℕ) (t : ℝ) :
    Quot (NonOrientableRel p 1) :=
  Quot.mk _ (nonOrientableNormalBoundaryCarrierArc p t)

theorem continuous_nonOrientableNormalBoundaryArc (p : ℕ) :
    Continuous (nonOrientableNormalBoundaryArc p) := by
  apply continuous_quot_mk.comp
  apply Continuous.subtype_mk
  fun_prop

theorem nonOrientableNormalBoundaryArc_zero_eq_one (p : ℕ) :
    nonOrientableNormalBoundaryArc p 0 =
      nonOrientableNormalBoundaryArc p 1 := by
  have h := Quot.sound (NonOrientableRel.c
    (p := p) (n := 1) (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) (0 : Fin 1))
  unfold nonOrientableNormalBoundaryArc nonOrientableNormalBoundaryCarrierArc
  convert h.symm using 1 <;> norm_num

/-- The canonical free boundary loop of the nonorientable normal form with one
boundary component. -/
def nonOrientableNormalBoundaryLoop (p : ℕ) :
    UnitAddCircle → Quot (NonOrientableRel p 1) :=
  AddCircle.liftIco 1 0 (nonOrientableNormalBoundaryArc p)

theorem continuous_nonOrientableNormalBoundaryLoop (p : ℕ) :
    Continuous (nonOrientableNormalBoundaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (nonOrientableNormalBoundaryArc_zero_eq_one p)
    (continuous_nonOrientableNormalBoundaryArc p).continuousOn

theorem nonOrientableNormalBoundaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    nonOrientableNormalBoundaryLoop p ((t : ℝ) : UnitAddCircle) =
      nonOrientableNormalBoundaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (nonOrientableNormalBoundaryArc_zero_eq_one p) t

/-- The complementary boundary path in the nonorientable one-boundary
polygon, traversing exactly the paired sides. -/
def nonOrientableNormalComplementaryCarrierArc (p : ℕ) (t : ℝ) :
    ClosedUnitDisc :=
  ClosedUnitDisc.bdyPtOfReal
    ((-1 + (2 * p + 2) * t) / (2 * p + 3))

def nonOrientableNormalComplementaryArc (p : ℕ) (t : ℝ) :
    Quot (NonOrientableRel p 1) :=
  Quot.mk _ (nonOrientableNormalComplementaryCarrierArc p t)

theorem continuous_nonOrientableNormalComplementaryArc (p : ℕ) :
    Continuous (nonOrientableNormalComplementaryArc p) := by
  apply continuous_quot_mk.comp
  apply Continuous.subtype_mk
  fun_prop

theorem nonOrientableNormalComplementaryCarrierArc_angularSubdivisionParameter
    (p : ℕ) (j : Fin ((2 * p + 1) + 1)) (x : ClosedUnitInterval) :
    nonOrientableNormalComplementaryCarrierArc p
        (angularSubdivisionParameter (2 * p + 1) j x) =
      oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p 1)
        (nonOrientableOccurrencePoint p 1
          (nonOrientableNormalComplementPositionEquiv p j).1 x) := by
  rw [nonOrientableCarrier_occurrencePoint]
  unfold nonOrientableNormalComplementaryCarrierArc
  by_cases hj : j = 0
  · subst j
    rw [nonOrientableNormalComplementPositionEquiv_zero_val,
      nonOrientableBoundaryWord_length]
    let a : ℝ :=
      (-1 + (2 * (p : ℝ) + 2) *
          angularSubdivisionParameter (2 * p + 1) 0 x) /
        (2 * (p : ℝ) + 3)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    change ClosedUnitDisc.bdyPtOfReal a =
      ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 2 + (x : ℝ)) / (2 * (p : ℝ) + 3))
    calc
      ClosedUnitDisc.bdyPtOfReal a =
          ClosedUnitDisc.bdyPtOfReal (a + (1 : ℤ)) :=
        (ClosedUnitDisc.bdyPtOfReal_add_int a 1).symm
      _ = ClosedUnitDisc.bdyPtOfReal
          ((2 * (p : ℝ) + 2 + (x : ℝ)) /
            (2 * (p : ℝ) + 3)) := by
        apply congrArg ClosedUnitDisc.bdyPtOfReal
        unfold a angularSubdivisionParameter
        norm_num only [Fin.val_zero, Nat.cast_zero, add_zero, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat]
        field_simp [show 2 * (p : ℝ) + 2 ≠ 0 by positivity,
          show 2 * (p : ℝ) + 3 ≠ 0 by positivity]
        ring
  · rw [nonOrientableNormalComplementPositionEquiv_val_of_ne_zero p j hj,
      nonOrientableBoundaryWord_length]
    apply congrArg ClosedUnitDisc.bdyPtOfReal
    have hjpos : 1 ≤ j.val := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hjval
      apply hj
      apply Fin.ext
      exact hjval
    unfold angularSubdivisionParameter
    rw [Nat.cast_sub hjpos]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp [show 2 * (p : ℝ) + 2 ≠ 0 by positivity,
      show 2 * (p : ℝ) + 3 ≠ 0 by positivity]
    ring

theorem nonOrientableNormalComplementaryCarrierArc_zero (p : ℕ) :
    nonOrientableNormalComplementaryCarrierArc p 0 =
      nonOrientableNormalBoundaryCarrierArc p 1 := by
  unfold nonOrientableNormalComplementaryCarrierArc
    nonOrientableNormalBoundaryCarrierArc
  congr 1
  ring

theorem nonOrientableNormalComplementaryCarrierArc_one (p : ℕ) :
    nonOrientableNormalComplementaryCarrierArc p 1 =
      nonOrientableNormalBoundaryCarrierArc p 0 := by
  have hperiod := ClosedUnitDisc.bdyPtOfReal_add_int
    (-2 / (2 * (p : ℝ) + 3)) 1
  unfold nonOrientableNormalComplementaryCarrierArc
    nonOrientableNormalBoundaryCarrierArc
  calc
    ClosedUnitDisc.bdyPtOfReal
        ((-1 + (2 * (p : ℝ) + 2) * 1) / (2 * (p : ℝ) + 3)) =
      ClosedUnitDisc.bdyPtOfReal
        (-2 / (2 * (p : ℝ) + 3) + (1 : ℤ)) := by
      congr 1
      field_simp [show 2 * (p : ℝ) + 3 ≠ 0 by positivity]
      ring
    _ = ClosedUnitDisc.bdyPtOfReal
        (-2 / (2 * (p : ℝ) + 3)) := hperiod
    _ = ClosedUnitDisc.bdyPtOfReal
        ((0 - 2) / (2 * (p : ℝ) + 3)) := by
      congr 1
      ring

theorem nonOrientableNormalComplementaryArc_zero_eq_one (p : ℕ) :
    nonOrientableNormalComplementaryArc p 0 =
      nonOrientableNormalComplementaryArc p 1 := by
  calc
    nonOrientableNormalComplementaryArc p 0 =
        nonOrientableNormalBoundaryArc p 1 := by
      exact congrArg (Quot.mk (NonOrientableRel p 1))
        (nonOrientableNormalComplementaryCarrierArc_zero p)
    _ = nonOrientableNormalBoundaryArc p 0 :=
      (nonOrientableNormalBoundaryArc_zero_eq_one p).symm
    _ = nonOrientableNormalComplementaryArc p 1 := by
      exact congrArg (Quot.mk (NonOrientableRel p 1))
        (nonOrientableNormalComplementaryCarrierArc_one p).symm

/-- The loop formed by all paired sides of the nonorientable one-boundary
normal-form polygon. -/
def nonOrientableNormalComplementaryLoop (p : ℕ) :
    UnitAddCircle → Quot (NonOrientableRel p 1) :=
  AddCircle.liftIco 1 0 (nonOrientableNormalComplementaryArc p)

theorem continuous_nonOrientableNormalComplementaryLoop (p : ℕ) :
    Continuous (nonOrientableNormalComplementaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (nonOrientableNormalComplementaryArc_zero_eq_one p)
    (continuous_nonOrientableNormalComplementaryArc p).continuousOn

theorem nonOrientableNormalComplementaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    nonOrientableNormalComplementaryLoop p ((t : ℝ) : UnitAddCircle) =
      nonOrientableNormalComplementaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (nonOrientableNormalComplementaryArc_zero_eq_one p) t

theorem nonOrientableNormalComplementaryLoop_angularSubdivisionArc
    (p : ℕ) (j : Fin ((2 * p + 1) + 1)) (x : ClosedUnitInterval) :
    nonOrientableNormalComplementaryLoop p
        (angularSubdivisionArc (2 * p + 1) j x) =
      Quot.mk (NonOrientableRel p 1)
        (oneFacePolygonalPreRealizationHomeomorph
          (nonOrientableBoundaryWord p 1)
          (nonOrientableOccurrencePoint p 1
            (nonOrientableNormalComplementPositionEquiv p j).1 x)) := by
  change nonOrientableNormalComplementaryLoop p
      ((((angularSubdivisionParameterIcc (2 * p + 1) j x :
        Set.Icc (0 : ℝ) 1) : ℝ)) : UnitAddCircle) = _
  rw [nonOrientableNormalComplementaryLoop_apply_unitInterval]
  unfold nonOrientableNormalComplementaryArc
  exact congrArg (Quot.mk (NonOrientableRel p 1))
    (nonOrientableNormalComplementaryCarrierArc_angularSubdivisionParameter p j x)

theorem nonOrientableOccurrencePoint_oneFaceOccurrenceIndex
    (p : ℕ) (o : (nonOrientableCellComplex p 1).BoundaryOccurrence)
    (x : unitInterval) :
    nonOrientableOccurrencePoint p 1 (oneFaceOccurrenceIndex o) x =
      ((nonOrientableCellComplex p 1).occurrenceSide o).point x := by
  rcases o with ⟨face, i⟩
  cases face
  rfl

theorem nonOrientableNormalComplementaryLoop_pair
    (p : ℕ) (hp : 1 ≤ p) (j : Fin ((2 * p + 1) + 1))
    (x : ClosedUnitInterval) :
    nonOrientableNormalComplementaryLoop p
        (angularSubdivisionArc (2 * p + 1) j x) =
      nonOrientableNormalComplementaryLoop p
        (match nonOrientableNormalComplementOrientation p hp j with
        | .preserving => angularSubdivisionArc (2 * p + 1)
            (nonOrientableNormalComplementEdgePair p hp j) x
        | .reversing => angularSubdivisionArc (2 * p + 1)
            (nonOrientableNormalComplementEdgePair p hp j)
            (reverseClosedUnitInterval x)) := by
  have hgenerator := PolygonGluing.Generator.glue
    (nonOrientableNormalComplementBoundaryPairing p hp j).identification
    (pairing_identification_mem
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableNormalComplementBoundaryPairing p hp j)) x
  have heqv := nonOrientableGenerator_to_eqvGen hp hgenerator
  cases horientation : nonOrientableNormalComplementOrientation p hp j with
  | preserving =>
      rw [nonOrientableNormalComplementaryLoop_angularSubdivisionArc,
        nonOrientableNormalComplementaryLoop_angularSubdivisionArc,
        nonOrientableNormalComplementPosition_edgePair]
      apply Quot.eqvGen_sound
      simpa [nonOrientableNormalComplementBoundaryPairing, horientation,
        nonOrientableNormalComplementOccurrence,
        nonOrientableOccurrencePoint_oneFaceOccurrenceIndex,
        SurfaceCellComplex.BoundaryPairing.identification,
        PolygonGluing.Identification.parameter,
        PolygonGluing.ParameterDirection.homeomorph] using heqv
  | reversing =>
      rw [nonOrientableNormalComplementaryLoop_angularSubdivisionArc,
        nonOrientableNormalComplementaryLoop_angularSubdivisionArc,
        nonOrientableNormalComplementPosition_edgePair]
      apply Quot.eqvGen_sound
      simpa [nonOrientableNormalComplementBoundaryPairing, horientation,
        nonOrientableNormalComplementOccurrence,
        nonOrientableOccurrencePoint_oneFaceOccurrenceIndex,
        SurfaceCellComplex.BoundaryPairing.identification,
        PolygonGluing.Identification.parameter,
        PolygonGluing.ParameterDirection.homeomorph] using heqv

def nonOrientableNormalComplementCylinderMap (p : ℕ) :
    ClosedUnitInterval × UnitAddCircle → Quot (NonOrientableRel p 1) :=
  fun q ↦ nonOrientableNormalComplementaryLoop p q.2

theorem continuous_nonOrientableNormalComplementCylinderMap (p : ℕ) :
    Continuous (nonOrientableNormalComplementCylinderMap p) :=
  (continuous_nonOrientableNormalComplementaryLoop p).comp continuous_snd

theorem nonOrientableNormalComplementCylinderMap_respects_gluing
    (p : ℕ) (hp : 1 ≤ p) :
    CylinderStripPointMapRespectsGluing
      (nonOrientableNormalComplementPairing p hp)
      (nonOrientableNormalComplementCylinderMap p) := by
  intro j x
  simpa [nonOrientableNormalComplementCylinderMap,
    nonOrientableNormalComplementPairing] using
    nonOrientableNormalComplementaryLoop_pair p hp j x

noncomputable def nonOrientableNormalComplementLift
    (p : ℕ) (hp : 1 ≤ p) :
    CylinderStripGluedPointSpace
        (nonOrientableNormalComplementPairing p hp) →
      Quot (NonOrientableRel p 1) :=
  cylinderStripGluedPointLift
    (nonOrientableNormalComplementPairing p hp)
    (nonOrientableNormalComplementCylinderMap p)
    (nonOrientableNormalComplementCylinderMap_respects_gluing p hp)

theorem continuous_nonOrientableNormalComplementLift
    (p : ℕ) (hp : 1 ≤ p) :
    Continuous (nonOrientableNormalComplementLift p hp) :=
  continuous_cylinderStripGluedPointLift
    (nonOrientableNormalComplementPairing p hp)
    (continuous_nonOrientableNormalComplementCylinderMap p)
    (nonOrientableNormalComplementCylinderMap_respects_gluing p hp)

theorem nonOrientableNormalComplementaryLoop_eq_lift_comp_boundary
    (p : ℕ) (hp : 1 ≤ p) :
    nonOrientableNormalComplementaryLoop p =
      nonOrientableNormalComplementLift p hp ∘
        cylinderStripGluedPointBoundary
          (nonOrientableNormalComplementPairing p hp) := by
  funext t
  rfl

theorem hasOddBoundaryDegreeObstruction_nonOrientableNormalComplementaryLoop
    (p : ℕ) (hp : 1 ≤ p) :
    HasOddBoundaryDegreeObstruction
      (nonOrientableNormalComplementaryLoop p) :=
  hasOddBoundaryDegreeObstruction_of_comp_continuous_cylinderStripGluedPointBoundary_pairing
    (nonOrientableNormalComplementPairing p hp)
    (nonOrientableNormalComplementLift p hp)
    (continuous_nonOrientableNormalComplementLift p hp)
    (nonOrientableNormalComplementaryLoop_eq_lift_comp_boundary p hp)

def nonOrientableNormalReverseBoundaryArc (p : ℕ) (t : ℝ) :
    Quot (NonOrientableRel p 1) :=
  nonOrientableNormalBoundaryArc p (1 - t)

theorem continuous_nonOrientableNormalReverseBoundaryArc (p : ℕ) :
    Continuous (nonOrientableNormalReverseBoundaryArc p) := by
  exact (continuous_nonOrientableNormalBoundaryArc p).comp
    (continuous_const.sub continuous_id)

theorem nonOrientableNormalReverseBoundaryArc_zero_eq_one (p : ℕ) :
    nonOrientableNormalReverseBoundaryArc p 0 =
      nonOrientableNormalReverseBoundaryArc p 1 := by
  simpa [nonOrientableNormalReverseBoundaryArc] using
    (nonOrientableNormalBoundaryArc_zero_eq_one p).symm

def nonOrientableNormalReverseBoundaryLoop (p : ℕ) :
    UnitAddCircle → Quot (NonOrientableRel p 1) :=
  AddCircle.liftIco 1 0 (nonOrientableNormalReverseBoundaryArc p)

theorem continuous_nonOrientableNormalReverseBoundaryLoop (p : ℕ) :
    Continuous (nonOrientableNormalReverseBoundaryLoop p) := by
  exact AddCircle.liftIco_zero_continuous
    (nonOrientableNormalReverseBoundaryArc_zero_eq_one p)
    (continuous_nonOrientableNormalReverseBoundaryArc p).continuousOn

theorem nonOrientableNormalReverseBoundaryLoop_apply_unitInterval
    (p : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    nonOrientableNormalReverseBoundaryLoop p ((t : ℝ) : UnitAddCircle) =
      nonOrientableNormalReverseBoundaryArc p t :=
  AddCircle.liftIco_one_apply_coe_unitInterval _
    (nonOrientableNormalReverseBoundaryArc_zero_eq_one p) t

def nonOrientableNormalCarrierHomotopy (p : ℕ)
    (q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) : ClosedUnitDisc :=
  closedUnitDiscLine
    (nonOrientableNormalComplementaryCarrierArc p q.2)
    (nonOrientableNormalBoundaryCarrierArc p (unitInterval.symm q.2))
    q.1

theorem continuous_nonOrientableNormalCarrierHomotopy (p : ℕ) :
    Continuous (nonOrientableNormalCarrierHomotopy p) := by
  apply continuous_induced_rng.2
  unfold nonOrientableNormalCarrierHomotopy closedUnitDiscLine
    nonOrientableNormalComplementaryCarrierArc
    nonOrientableNormalBoundaryCarrierArc ClosedUnitDisc.bdyPtOfReal
  fun_prop

def nonOrientableNormalIccHomotopy (p : ℕ)
    (q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :
    Quot (NonOrientableRel p 1) :=
  Quot.mk _ (nonOrientableNormalCarrierHomotopy p q)

theorem continuous_nonOrientableNormalIccHomotopy (p : ℕ) :
    Continuous (nonOrientableNormalIccHomotopy p) :=
  continuous_quot_mk.comp (continuous_nonOrientableNormalCarrierHomotopy p)

theorem nonOrientableNormalIccHomotopy_second_endpoints
    (p : ℕ) (s : Set.Icc (0 : ℝ) 1) :
    nonOrientableNormalIccHomotopy p (s, 0) =
      nonOrientableNormalIccHomotopy p (s, 1) := by
  calc
    nonOrientableNormalIccHomotopy p (s, 0) =
        nonOrientableNormalBoundaryArc p 1 := by
      unfold nonOrientableNormalIccHomotopy
        nonOrientableNormalCarrierHomotopy
        nonOrientableNormalBoundaryArc
      change Quot.mk _
        (closedUnitDiscLine
          (nonOrientableNormalComplementaryCarrierArc p 0)
          (nonOrientableNormalBoundaryCarrierArc p
            (unitInterval.symm (0 : I))) s) =
        Quot.mk _ (nonOrientableNormalBoundaryCarrierArc p 1)
      rw [nonOrientableNormalComplementaryCarrierArc_zero]
      simp only [unitInterval.symm_zero]
      change Quot.mk _
        (closedUnitDiscLine
          (nonOrientableNormalBoundaryCarrierArc p 1)
          (nonOrientableNormalBoundaryCarrierArc p 1) s) =
        Quot.mk _ (nonOrientableNormalBoundaryCarrierArc p 1)
      rw [closedUnitDiscLine_self]
    _ = nonOrientableNormalBoundaryArc p 0 :=
      (nonOrientableNormalBoundaryArc_zero_eq_one p).symm
    _ = nonOrientableNormalIccHomotopy p (s, 1) := by
      unfold nonOrientableNormalIccHomotopy
        nonOrientableNormalCarrierHomotopy
        nonOrientableNormalBoundaryArc
      change Quot.mk _ (nonOrientableNormalBoundaryCarrierArc p 0) =
        Quot.mk _
          (closedUnitDiscLine
            (nonOrientableNormalComplementaryCarrierArc p 1)
            (nonOrientableNormalBoundaryCarrierArc p
              (unitInterval.symm (1 : I))) s)
      rw [nonOrientableNormalComplementaryCarrierArc_one]
      simp only [unitInterval.symm_one]
      change Quot.mk _ (nonOrientableNormalBoundaryCarrierArc p 0) =
        Quot.mk _
          (closedUnitDiscLine
            (nonOrientableNormalBoundaryCarrierArc p 0)
            (nonOrientableNormalBoundaryCarrierArc p 0) s)
      rw [closedUnitDiscLine_self]

def nonOrientableNormalQuotHomotopy (p : ℕ) :
    Set.Icc (0 : ℝ) 1 × Quot (AddCircle.EndpointIdent (1 : ℝ) 0) →
      Quot (NonOrientableRel p 1) :=
  fun q ↦ Quot.lift
    (r := AddCircle.EndpointIdent (1 : ℝ) 0)
    (fun t ↦ nonOrientableNormalIccHomotopy p
      (q.1, endpointIdentUnitInterval t))
    (by
      rintro _ _ ⟨_⟩
      simpa [endpointIdentUnitInterval] using
        nonOrientableNormalIccHomotopy_second_endpoints p q.1)
    q.2

theorem continuous_nonOrientableNormalQuotHomotopy (p : ℕ) :
    Continuous (nonOrientableNormalQuotHomotopy p) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_right
  simpa [nonOrientableNormalQuotHomotopy] using
    (continuous_nonOrientableNormalIccHomotopy p).comp
      (continuous_fst.prodMk
        (continuous_endpointIdentUnitInterval.comp continuous_snd))

def nonOrientableNormalBoundaryHomotopy (p : ℕ) :
    C(I × UnitAddCircle, Quot (NonOrientableRel p 1)) where
  toFun q := nonOrientableNormalQuotHomotopy p
    (q.1, AddCircle.homeoIccQuot (1 : ℝ) 0 q.2)
  continuous_toFun :=
    (continuous_nonOrientableNormalQuotHomotopy p).comp
      (continuous_fst.prodMk
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd))

theorem nonOrientableNormalBoundaryHomotopy_zero
    (p : ℕ) (t : UnitAddCircle) :
    nonOrientableNormalBoundaryHomotopy p (0, t) =
      nonOrientableNormalComplementaryLoop p t := by
  change nonOrientableNormalQuotHomotopy p
      ((0 : I), AddCircle.homeoIccQuot (1 : ℝ) 0 t) =
    nonOrientableNormalComplementaryLoop p t
  generalize hq : AddCircle.homeoIccQuot (1 : ℝ) 0 t = q
  have ht : t = (AddCircle.homeoIccQuot (1 : ℝ) 0).symm q := by
    rw [← hq]
    exact (AddCircle.homeoIccQuot (1 : ℝ) 0).symm_apply_apply t |>.symm
  rw [ht]
  induction q using Quot.inductionOn with
  | _ x =>
      change nonOrientableNormalIccHomotopy p
          ((0 : I), endpointIdentUnitInterval x) =
        nonOrientableNormalComplementaryLoop p
          (((endpointIdentUnitInterval x : I) : ℝ) : UnitAddCircle)
      rw [nonOrientableNormalComplementaryLoop_apply_unitInterval]
      unfold nonOrientableNormalIccHomotopy
        nonOrientableNormalCarrierHomotopy
        nonOrientableNormalComplementaryArc
      rw [closedUnitDiscLine_zero]

theorem nonOrientableNormalBoundaryHomotopy_one
    (p : ℕ) (t : UnitAddCircle) :
    nonOrientableNormalBoundaryHomotopy p (1, t) =
      nonOrientableNormalReverseBoundaryLoop p t := by
  change nonOrientableNormalQuotHomotopy p
      ((1 : I), AddCircle.homeoIccQuot (1 : ℝ) 0 t) =
    nonOrientableNormalReverseBoundaryLoop p t
  generalize hq : AddCircle.homeoIccQuot (1 : ℝ) 0 t = q
  have ht : t = (AddCircle.homeoIccQuot (1 : ℝ) 0).symm q := by
    rw [← hq]
    exact (AddCircle.homeoIccQuot (1 : ℝ) 0).symm_apply_apply t |>.symm
  rw [ht]
  induction q using Quot.inductionOn with
  | _ x =>
      change nonOrientableNormalIccHomotopy p
          ((1 : I), endpointIdentUnitInterval x) =
        nonOrientableNormalReverseBoundaryLoop p
          (((endpointIdentUnitInterval x : I) : ℝ) : UnitAddCircle)
      rw [nonOrientableNormalReverseBoundaryLoop_apply_unitInterval]
      unfold nonOrientableNormalIccHomotopy
        nonOrientableNormalCarrierHomotopy
        nonOrientableNormalReverseBoundaryArc
        nonOrientableNormalBoundaryArc
      rw [closedUnitDiscLine_one]
      rfl

theorem nonOrientableNormalReverseBoundaryLoop_eq_comp_neg (p : ℕ) :
    nonOrientableNormalReverseBoundaryLoop p =
      nonOrientableNormalBoundaryLoop p ∘ unitAddCircleNegHomeomorph := by
  funext t
  obtain ⟨x, hx, hxt⟩ := AddCircle.eq_coe_Ico t
  rw [← hxt]
  let u : I := ⟨x, hx.1, hx.2.le⟩
  change nonOrientableNormalReverseBoundaryLoop p
      (((u : I) : ℝ) : UnitAddCircle) =
    nonOrientableNormalBoundaryLoop p
      (unitAddCircleNegHomeomorph (((u : I) : ℝ) : UnitAddCircle))
  rw [nonOrientableNormalReverseBoundaryLoop_apply_unitInterval]
  have hneg :
      unitAddCircleNegHomeomorph (((u : I) : ℝ) : UnitAddCircle) =
        (((unitInterval.symm u : I) : ℝ) : UnitAddCircle) := by
    rw [unitAddCircleNegHomeomorph_apply, ← AddCircle.coe_neg]
    rw [show -((u : I) : ℝ) =
        ((unitInterval.symm u : I) : ℝ) - 1 by
      rw [unitInterval.coe_symm_eq]
      ring]
    simp [sub_eq_add_neg]
  rw [hneg, nonOrientableNormalBoundaryLoop_apply_unitInterval]
  simp [nonOrientableNormalReverseBoundaryArc, unitInterval.coe_symm_eq]

theorem hasOddBoundaryDegreeObstruction_nonOrientableNormalReverseBoundaryLoop
    (p : ℕ) (hp : 1 ≤ p) :
    HasOddBoundaryDegreeObstruction
      (nonOrientableNormalReverseBoundaryLoop p) :=
  hasOddBoundaryDegreeObstruction_of_homotopy
    (nonOrientableNormalBoundaryHomotopy p)
    (nonOrientableNormalBoundaryHomotopy_zero p)
    (nonOrientableNormalBoundaryHomotopy_one p)
    (hasOddBoundaryDegreeObstruction_nonOrientableNormalComplementaryLoop p hp)

/-- The canonical free loop of every nonorientable one-boundary normal form
has the odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_nonOrientableNormalBoundaryLoop
    (p : ℕ) (hp : 1 ≤ p) :
    HasOddBoundaryDegreeObstruction
      (nonOrientableNormalBoundaryLoop p) := by
  apply hasOddBoundaryDegreeObstruction_of_circleHomeomorph_reparametrization
    (boundary := nonOrientableNormalReverseBoundaryLoop p)
    unitAddCircleNegHomeomorph
  · funext t
    rw [nonOrientableNormalReverseBoundaryLoop_eq_comp_neg]
    simp [Function.comp_def]
  · exact
      hasOddBoundaryDegreeObstruction_nonOrientableNormalReverseBoundaryLoop p hp

end

end GromovFilling
