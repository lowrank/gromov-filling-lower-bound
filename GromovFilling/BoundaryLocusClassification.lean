import ClassificationOfSurfaces.FiniteCyclicTerminalNormalization

/-!
# Boundary-locus preservation in finite-cyclic surface classification

The absolute classification theorem identifies the underlying quotient
spaces.  For Lemma 5.4 we additionally need its homeomorphism to remember
the unpaired polygon sides.  This module packages that relative invariant:
the polygonal boundary locus consists exactly of quotient points represented
on an edge occurring once in the presentation.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

noncomputable section

/-- The points represented on the once-used sides of a valid finite-cyclic
presentation.  Endpoints are included, so this is the full polygonal boundary
locus rather than just the relative interiors of its edges. -/
def PolygonalBoundaryLocus
    (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    Set (P.PolygonalRealization validP) :=
  {q | ∃ (o : P.BoundaryOccurrence) (t : unitInterval),
    P.IsBoundaryEdge o.edge ∧
      q = P.polygonalMk validP ((P.occurrenceSide o).point t)}

theorem mem_polygonalBoundaryLocus_iff
    {P : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {q : P.PolygonalRealization validP} :
    q ∈ P.PolygonalBoundaryLocus validP ↔
      ∃ (o : P.BoundaryOccurrence) (t : unitInterval),
        P.IsBoundaryEdge o.edge ∧
          q = P.polygonalMk validP ((P.occurrenceSide o).point t) :=
  Iff.rfl

/-- A homeomorphism of faithful polygonal realizations which preserves the
complete once-used-side locus in both directions. -/
structure BoundaryRealizationEquivData
    (P Q : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) where
  homeomorph : P.PolygonalRealization validP ≃ₜ
    Q.PolygonalRealization validQ
  maps_boundary : Set.MapsTo homeomorph
    (P.PolygonalBoundaryLocus validP)
    (Q.PolygonalBoundaryLocus validQ)
  symm_maps_boundary : Set.MapsTo homeomorph.symm
    (Q.PolygonalBoundaryLocus validQ)
    (P.PolygonalBoundaryLocus validP)

namespace BoundaryRealizationEquivData

/-- Boundary-faithful polygonal equivalence is reflexive. -/
def refl (P : FiniteCyclicPresentation) (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P P validP validP where
  homeomorph := Homeomorph.refl _
  maps_boundary := fun _ hq => hq
  symm_maps_boundary := fun _ hq => hq

/-- Reverse a boundary-faithful polygonal equivalence. -/
def symm {P Q : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    (D : BoundaryRealizationEquivData P Q validP validQ) :
    BoundaryRealizationEquivData Q P validQ validP where
  homeomorph := D.homeomorph.symm
  maps_boundary := D.symm_maps_boundary
  symm_maps_boundary := D.maps_boundary

/-- Compose boundary-faithful polygonal equivalences. -/
def trans {P Q R : FiniteCyclicPresentation}
    {validP : P.IsSurfaceValid} {validQ : Q.IsSurfaceValid}
    {validR : R.IsSurfaceValid}
    (D₁ : BoundaryRealizationEquivData P Q validP validQ)
    (D₂ : BoundaryRealizationEquivData Q R validQ validR) :
    BoundaryRealizationEquivData P R validP validR where
  homeomorph := D₁.homeomorph.trans D₂.homeomorph
  maps_boundary := D₂.maps_boundary.comp D₁.maps_boundary
  symm_maps_boundary := D₁.symm_maps_boundary.comp D₂.symm_maps_boundary

end BoundaryRealizationEquivData

namespace SignedPresentationIso

/-- A signed presentation isomorphism preserves the complete polygonal
boundary locus. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ where
  homeomorph := e.realizationHomeomorph validP validQ
  maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    refine ⟨e.mapOccurrence validQ o, t, ?_, ?_⟩
    · rw [e.mapOccurrence_edge]
      exact (e.isBoundaryEdge_iff o.edge).mp ho
    · change
        e.realizationHomeomorph validP validQ
            (P.polygonalMk validP ((P.occurrenceSide o).point t)) =
          Q.polygonalMk validQ
            ((Q.occurrenceSide (e.mapOccurrence validQ o)).point t)
      change Q.polygonalMk validQ
          (e.preHomeomorph ((P.occurrenceSide o).point t)) = _
      rw [e.preHomeomorph_occurrenceSide_point validQ]
  symm_maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    let source := (e.occurrenceEquiv validQ).symm o
    refine ⟨source, t, ?_, ?_⟩
    · have hedge := e.occurrenceEquiv_symm_edge validQ o
      rw [← hedge] at ho
      exact (e.isBoundaryEdge_iff source.edge).mpr ho
    · change
        (e.realizationHomeomorph validP validQ).symm
            (Q.polygonalMk validQ ((Q.occurrenceSide o).point t)) =
          P.polygonalMk validP ((P.occurrenceSide source).point t)
      change P.polygonalMk validP
          (e.preHomeomorph.symm ((Q.occurrenceSide o).point t)) = _
      rw [e.preHomeomorph_symm_occurrenceSide_point validQ]

end SignedPresentationIso

namespace UnorientedPresentationIso

/-- Reorienting faces independently still preserves the complete polygonal
boundary locus; reflected faces merely reverse their side parameter. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (e : UnorientedPresentationIso P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ where
  homeomorph := e.realizationHomeomorph validP validQ
  maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    refine ⟨e.mapOccurrence validQ o, e.sideParameter o.1 t, ?_, ?_⟩
    · rw [e.mapOccurrence_edge]
      exact (e.isBoundaryEdge_iff o.edge).mp ho
    · change
        e.realizationHomeomorph validP validQ
            (P.polygonalMk validP ((P.occurrenceSide o).point t)) =
          Q.polygonalMk validQ
            ((Q.occurrenceSide (e.mapOccurrence validQ o)).point
              (e.sideParameter o.1 t))
      change Q.polygonalMk validQ
          (e.preHomeomorph ((P.occurrenceSide o).point t)) = _
      rw [e.preHomeomorph_occurrenceSide_point validQ]
  symm_maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    let source := (e.occurrenceEquiv validQ).symm o
    refine ⟨source, e.sideParameter source.1 t, ?_, ?_⟩
    · have hedge := e.occurrenceEquiv_symm_edge validQ o
      rw [← hedge] at ho
      exact (e.isBoundaryEdge_iff source.edge).mpr ho
    · change
        (e.realizationHomeomorph validP validQ).symm
            (Q.polygonalMk validQ ((Q.occurrenceSide o).point t)) =
          P.polygonalMk validP
            ((P.occurrenceSide source).point (e.sideParameter source.1 t))
      change P.polygonalMk validP
          (e.preHomeomorph.symm ((Q.occurrenceSide o).point t)) = _
      rw [e.preHomeomorph_symm_occurrenceSide_point validQ]

end UnorientedPresentationIso

namespace P1

/-- Subdividing one edge preserves the complete polygonal boundary locus.
If the selected edge is a boundary edge, its two replacement sides inherit
that status and cover its two half-parameters. -/
noncomputable def boundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (a : P.Edge)
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (expand P a) validP
      (expand_isSurfaceValid P a validP) where
  homeomorph := realizationHomeomorph P a validP
  maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    by_cases hselected : o.edge = a
    · by_cases ht : (t : ℝ) ≤ 1 / 2
      · let p : ExpandedSourcePosition P a :=
          ⟨o, zeroOffset a o.dart⟩
        refine ⟨expandedOccurrenceAt P a p,
          firstHalfParameter t ht, ?_, ?_⟩
        · rw [expandedOccurrenceAt_edge,
            isBoundaryEdge_expandedSubedge_iff]
          exact ho
        · change
            (realizationHomeomorph P a validP)
                (P.polygonalMk validP ((P.occurrenceSide o).point t)) =
              (expand P a).polygonalMk
                (expand_isSurfaceValid P a validP)
                (((expand P a).occurrenceSide
                  (expandedOccurrenceAt P a p)).point
                    (firstHalfParameter t ht))
          change
            (expand P a).polygonalMk
                (expand_isSurfaceValid P a validP)
                (preHomeomorph P a validP
                  ((P.occurrenceSide o).point t)) = _
          rw [preHomeomorph_occurrenceSide_firstHalf
            P a validP o hselected t ht]
      · have ht' : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
        let p : ExpandedSourcePosition P a :=
          ⟨o, oneOffset a o.dart hselected⟩
        refine ⟨expandedOccurrenceAt P a p,
          secondHalfParameter t ht', ?_, ?_⟩
        · rw [expandedOccurrenceAt_edge,
            isBoundaryEdge_expandedSubedge_iff]
          exact ho
        · change
            (realizationHomeomorph P a validP)
                (P.polygonalMk validP ((P.occurrenceSide o).point t)) =
              (expand P a).polygonalMk
                (expand_isSurfaceValid P a validP)
                (((expand P a).occurrenceSide
                  (expandedOccurrenceAt P a p)).point
                    (secondHalfParameter t ht'))
          change
            (expand P a).polygonalMk
                (expand_isSurfaceValid P a validP)
                (preHomeomorph P a validP
                  ((P.occurrenceSide o).point t)) = _
          rw [preHomeomorph_occurrenceSide_secondHalf
            P a validP o hselected t ht']
    · let p : ExpandedSourcePosition P a :=
        ⟨o, zeroOffset a o.dart⟩
      refine ⟨expandedOccurrenceAt P a p, t, ?_, ?_⟩
      · rw [expandedOccurrenceAt_edge,
          isBoundaryEdge_expandedSubedge_iff]
        exact ho
      · change
          (realizationHomeomorph P a validP)
              (P.polygonalMk validP ((P.occurrenceSide o).point t)) =
            (expand P a).polygonalMk
              (expand_isSurfaceValid P a validP)
              (((expand P a).occurrenceSide
                (expandedOccurrenceAt P a p)).point t)
        change
          (expand P a).polygonalMk
              (expand_isSurfaceValid P a validP)
              (preHomeomorph P a validP
                ((P.occurrenceSide o).point t)) = _
        rw [preHomeomorph_occurrenceSide_of_not_selected
          P a validP o hselected t]
  symm_maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    let p : ExpandedSourcePosition P a :=
      (expandedOccurrenceEquiv P a).symm o
    have hp : expandedOccurrenceAt P a p = o :=
      (expandedOccurrenceEquiv P a).apply_symm_apply o
    have hpBoundary : P.IsBoundaryEdge p.1.edge := by
      have htarget :
          (expand P a).IsBoundaryEdge
            (expandedOccurrenceAt P a p).edge := by
        rwa [hp]
      rw [expandedOccurrenceAt_edge,
        isBoundaryEdge_expandedSubedge_iff] at htarget
      exact htarget
    refine ⟨p.1, unexpandParameter a p.1.dart p.2 t,
      hpBoundary, ?_⟩
    change
      (realizationHomeomorph P a validP).symm
          ((expand P a).polygonalMk
            (expand_isSurfaceValid P a validP)
            (((expand P a).occurrenceSide o).point t)) =
        P.polygonalMk validP
          ((P.occurrenceSide p.1).point
            (unexpandParameter a p.1.dart p.2 t))
    change P.polygonalMk validP
        ((preHomeomorph P a validP).symm
          (((expand P a).occurrenceSide o).point t)) = _
    rw [← hp, preHomeomorph_symm_expandedOccurrenceAt]

end P1

namespace P2

/-- A positive nondegenerate face split preserves the complete polygonal
boundary locus.  Every old side is routed to a cast-successor edge; the new
child seam occurs twice and is therefore internal. -/
noncomputable def positiveBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) where
  homeomorph :=
    positiveRealizationHomeomorph
      P cut horientation hl hr validP
  maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    refine ⟨positiveMapOccurrence P cut horientation hl hr o,
      t, ?_, ?_⟩
    · rw [positiveMapOccurrence_edge]
      unfold IsBoundaryEdge at ho ⊢
      rwa [← edgeMultiplicity_split_castSucc P cut]
    · change
        positiveRealizationHomeomorph
              P cut horientation hl hr validP
              (P.polygonalMk validP
                ((P.occurrenceSide o).point t)) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            (((split P cut).occurrenceSide
              (positiveMapOccurrence
                P cut horientation hl hr o)).point t)
      change positivePreMap P cut horientation hl hr validP
          ((P.occurrenceSide o).point t) = _
      exact positivePreMap_occurrenceSide
        P cut horientation hl hr validP o t
  symm_maps_boundary := by
    rintro _ ⟨q, t, hq, rfl⟩
    have hnotFresh : q.edge ≠ freshEdge P := by
      intro hqFresh
      apply positiveFresh_not_boundary P cut
      rwa [← hqFresh]
    have hnotLast : q.edge ≠ Fin.last P.edgeCount := by
      simpa [freshEdge, P1.freshEdge] using hnotFresh
    let e : P.Edge := q.edge.castPred hnotLast
    have hedge : q.edge = e.castSucc := by
      exact Fin.castSucc_castPred q.edge hnotLast
    obtain ⟨o, ho⟩ :=
      exists_positiveMapOccurrence_eq_of_edge_castSucc
        P cut horientation hl hr q e hedge
    have hoBoundary : P.IsBoundaryEdge o.edge := by
      have htarget :
          (split P cut).IsBoundaryEdge
            (positiveMapOccurrence
              P cut horientation hl hr o).edge := by
        rwa [ho]
      rw [positiveMapOccurrence_edge] at htarget
      unfold IsBoundaryEdge at htarget ⊢
      rw [edgeMultiplicity_split_castSucc P cut]
      exact htarget
    refine ⟨o, t, hoBoundary, ?_⟩
    change
      (positiveRealizationHomeomorph
          P cut horientation hl hr validP).symm
          ((split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            (((split P cut).occurrenceSide q).point t)) =
        P.polygonalMk validP ((P.occurrenceSide o).point t)
    change positiveInvPreMap P cut horientation hl hr validP
        (((split P cut).occurrenceSide q).point t) = _
    rw [← ho]
    exact positiveInvPreMap_mapOccurrence_side
      P cut horientation hl hr validP o t

/-- The positive empty-left P2 model also preserves the complete boundary
locus.  Its fresh monogon/right-child seam is internal, while every old side
is transported with unchanged interval parameter. -/
noncomputable def rightDegenerateBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hleft : cut.left = []) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) where
  homeomorph :=
    rightDegenerateRealizationHomeomorph
      P cut horientation hleft hr validP
  maps_boundary := by
    rintro _ ⟨o, t, ho, rfl⟩
    refine ⟨rightDegenerateMapOccurrence
        P cut horientation hleft hr o, t, ?_, ?_⟩
    · rw [rightDegenerateMapOccurrence_edge]
      unfold IsBoundaryEdge at ho ⊢
      rwa [← edgeMultiplicity_split_castSucc P cut]
    · change
        rightDegenerateRealizationHomeomorph
              P cut horientation hleft hr validP
              (P.polygonalMk validP
                ((P.occurrenceSide o).point t)) =
          (split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            (((split P cut).occurrenceSide
              (rightDegenerateMapOccurrence
                P cut horientation hleft hr o)).point t)
      change rightDegeneratePreMap
          P cut horientation hleft hr validP
          ((P.occurrenceSide o).point t) = _
      exact rightDegeneratePreMap_occurrenceSide
        P cut horientation hleft hr validP o t
  symm_maps_boundary := by
    rintro _ ⟨q, t, hq, rfl⟩
    have hnotFresh : q.edge ≠ freshEdge P := by
      intro hqFresh
      apply positiveFresh_not_boundary P cut
      rwa [← hqFresh]
    have hnotLast : q.edge ≠ Fin.last P.edgeCount := by
      simpa [freshEdge, P1.freshEdge] using hnotFresh
    let e : P.Edge := q.edge.castPred hnotLast
    have hedge : q.edge = e.castSucc := by
      exact Fin.castSucc_castPred q.edge hnotLast
    obtain ⟨o, ho⟩ :=
      exists_rightDegenerateMapOccurrence_eq_of_edge_castSucc
        P cut horientation hleft hr q e hedge
    have hoBoundary : P.IsBoundaryEdge o.edge := by
      have htarget :
          (split P cut).IsBoundaryEdge
            (rightDegenerateMapOccurrence
              P cut horientation hleft hr o).edge := by
        rwa [ho]
      rw [rightDegenerateMapOccurrence_edge] at htarget
      unfold IsBoundaryEdge at htarget ⊢
      rw [edgeMultiplicity_split_castSucc P cut]
      exact htarget
    refine ⟨o, t, hoBoundary, ?_⟩
    change
      (rightDegenerateRealizationHomeomorph
          P cut horientation hleft hr validP).symm
          ((split P cut).polygonalMk
            (split_isSurfaceValid P cut validP)
            (((split P cut).occurrenceSide q).point t)) =
        P.polygonalMk validP ((P.occurrenceSide o).point t)
    change rightDegenerateInvPreMap
        P cut horientation hleft hr validP
        (((split P cut).occurrenceSide q).point t) = _
    rw [← ho]
    exact rightDegenerateInvPreMap_mapOccurrence_side
      P cut horientation hleft hr validP o t

/-- A negative-orientation nondegenerate split is boundary-faithful after
reversing the cut and swapping the two target child faces. -/
noncomputable def negativeBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = true)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hflipOrientation : cut.flip.face.orientation = false := by
    simp [P2Cut.flip, OrientedFace.flip, horientation]
  have hflipLeft : 0 < cut.flip.left.length := by
    simpa [P2Cut.flip, inverseWord] using hr
  have hflipRight : 0 < cut.flip.right.length := by
    simpa [P2Cut.flip, inverseWord] using hl
  let validFlip := split_isSurfaceValid P cut.flip validP
  exact
    (positiveBoundaryRealizationEquivData
      P cut.flip hflipOrientation hflipLeft hflipRight validP).trans
      ((flipSignedPresentationIso P cut).boundaryRealizationEquivData
        validFlip (split_isSurfaceValid P cut validP))

/-- Every nondegenerate P2 split preserves the complete boundary locus. -/
noncomputable def nondegenerateBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (hl : 0 < cut.left.length) (hr : 0 < cut.right.length)
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  cases horientation : cut.face.orientation
  · exact positiveBoundaryRealizationEquivData
      P cut horientation hl hr validP
  · exact negativeBoundaryRealizationEquivData
      P cut horientation hl hr validP

/-- A positive empty-right split is reduced to the empty-left model by
swapping the displayed cut pieces. -/
noncomputable def leftDegenerateBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (hl : 0 < cut.left.length) (hright : cut.right = [])
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hswapOrientation : cut.swap.face.orientation = false := by
    simpa [P2Cut.swap] using horientation
  have hswapLeft : cut.swap.left = [] := by
    simpa [P2Cut.swap] using hright
  have hswapRight : 0 < cut.swap.right.length := by
    simpa [P2Cut.swap] using hl
  let validSwap := split_isSurfaceValid P cut.swap validP
  exact
    (rightDegenerateBoundaryRealizationEquivData
      P cut.swap hswapOrientation hswapLeft hswapRight validP).trans
      ((swapSignedPresentationIso P cut).boundaryRealizationEquivData
        validSwap (split_isSurfaceValid P cut validP))

/-- Every positive one-sided-degenerate P2 split preserves the complete
boundary locus. -/
noncomputable def positiveOneSidedBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = false)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  exact Classical.choice (by
    rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
    · exact ⟨rightDegenerateBoundaryRealizationEquivData
        P cut horientation hleft hr validP⟩
    · exact ⟨leftDegenerateBoundaryRealizationEquivData
        P cut horientation hl hright validP⟩)

/-- A negative one-sided split is reduced to the positive theorem by
reversing its selected face traversal. -/
noncomputable def negativeOneSidedBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (horientation : cut.face.orientation = true)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  have hflipOrientation : cut.flip.face.orientation = false := by
    simp [P2Cut.flip, OrientedFace.flip, horientation]
  have hflipOneSided :
      (cut.flip.left = [] ∧ 0 < cut.flip.right.length) ∨
        (0 < cut.flip.left.length ∧ cut.flip.right = []) := by
    rcases honeSided with ⟨hleft, hr⟩ | ⟨hl, hright⟩
    · right
      constructor
      · simpa [P2Cut.flip, inverseWord] using hr
      · simp [P2Cut.flip, inverseWord, hleft]
    · left
      constructor
      · simp [P2Cut.flip, inverseWord, hright]
      · simpa [P2Cut.flip, inverseWord] using hl
  let validFlip := split_isSurfaceValid P cut.flip validP
  exact
    (positiveOneSidedBoundaryRealizationEquivData
      P cut.flip hflipOrientation hflipOneSided validP).trans
      ((flipSignedPresentationIso P cut).boundaryRealizationEquivData
        validFlip (split_isSurfaceValid P cut validP))

/-- Every one-sided-degenerate P2 split preserves the complete boundary
locus, independently of orientation and of the empty displayed piece. -/
noncomputable def oneSidedBoundaryRealizationEquivData
    (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (honeSided :
      (cut.left = [] ∧ 0 < cut.right.length) ∨
        (0 < cut.left.length ∧ cut.right = []))
    (validP : P.IsSurfaceValid) :
    BoundaryRealizationEquivData P (split P cut) validP
      (split_isSurfaceValid P cut validP) := by
  cases horientation : cut.face.orientation
  · exact positiveOneSidedBoundaryRealizationEquivData
      P cut horientation honeSided validP
  · exact negativeOneSidedBoundaryRealizationEquivData
      P cut horientation honeSided validP

end P2

namespace P1Subdivision

/-- Every P1 subdivision, including its final signed relabeling, admits a
boundary-faithful realization homeomorphism. -/
theorem exists_boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : P1Subdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    Nonempty (BoundaryRealizationEquivData P Q validP validQ) := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  let validExpand := P1.expand_isSurfaceValid P a validP
  exact ⟨(P1.boundaryRealizationEquivData P a validP).trans
    (e.boundaryRealizationEquivData validExpand validQ)⟩

/-- Chosen boundary-faithful realization data for a P1 subdivision. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : P1Subdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ :=
  Classical.choice
    (hPQ.exists_boundaryRealizationEquivData validP validQ)

end P1Subdivision

namespace P2Subdivision

/-- Every ordinary-valid P2 subdivision admits a boundary-faithful
realization homeomorphism.  The exceptional empty-word branch is impossible
under the source validity hypothesis. -/
theorem exists_boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : P2Subdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    Nonempty (BoundaryRealizationEquivData P Q validP validQ) := by
  rcases hPQ with ⟨cut, hcut | hempty, ⟨e⟩⟩
  · have hlengths : 0 < cut.left.length ∧ 0 < cut.right.length :=
      (P2Cut.isNondegenerate_iff_lengths_pos cut).mp hcut
    let validSplit := P2.split_isSurfaceValid P cut validP
    exact ⟨(P2.nondegenerateBoundaryRealizationEquivData
      P cut hlengths.1 hlengths.2 validP).trans
        (e.boundaryRealizationEquivData validSplit validQ)⟩
  · exact (hempty.not_isSurfaceValid validP).elim

/-- Chosen boundary-faithful realization data for a P2 subdivision. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : P2Subdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ :=
  Classical.choice
    (hPQ.exists_boundaryRealizationEquivData validP validQ)

end P2Subdivision

namespace SubdivisionStep

/-- Every directed primitive move preserves the complete polygonal boundary
locus. -/
theorem exists_boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : SubdivisionStep P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    Nonempty (BoundaryRealizationEquivData P Q validP validQ) := by
  rcases hPQ with hIso | hrest
  · rcases hIso with ⟨e⟩
    exact ⟨e.boundaryRealizationEquivData validP validQ⟩
  · rcases hrest with hP1 | hP2
    · exact hP1.exists_boundaryRealizationEquivData validP validQ
    · exact hP2.exists_boundaryRealizationEquivData validP validQ

/-- Chosen boundary-faithful realization data for a directed primitive
move. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : SubdivisionStep P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ :=
  Classical.choice
    (hPQ.exists_boundaryRealizationEquivData validP validQ)

end SubdivisionStep

namespace Subdivides

/-- A directed subdivision chain preserves the complete polygonal boundary
locus. -/
theorem exists_boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    Nonempty (BoundaryRealizationEquivData P Q validP validQ) := by
  induction hPQ with
  | refl =>
      exact ⟨BoundaryRealizationEquivData.refl P validP⟩
  | @tail R Q hPR hstep ih =>
      let validR : R.IsSurfaceValid :=
        Subdivides.isSurfaceValid hPR validP
      exact ⟨(Classical.choice (ih validR)).trans
        (hstep.boundaryRealizationEquivData validR validQ)⟩

/-- Chosen boundary-faithful realization data for a directed subdivision
chain. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : Subdivides P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ :=
  Classical.choice
    (hPQ.exists_boundaryRealizationEquivData validP validQ)

end Subdivides

namespace HasCommonSubdivision

/-- A common subdivision yields a boundary-faithful homeomorphism of the two
original faithful polygonal realizations. -/
theorem exists_boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    Nonempty (BoundaryRealizationEquivData P Q validP validQ) := by
  rcases hPQ with ⟨R, hPR, hQR⟩
  let validR : R.IsSurfaceValid :=
    Subdivides.isSurfaceValid hPR validP
  exact ⟨(hPR.boundaryRealizationEquivData validP validR).trans
    (hQR.boundaryRealizationEquivData validQ validR).symm⟩

/-- Chosen boundary-faithful realization data from a common subdivision. -/
noncomputable def boundaryRealizationEquivData
    {P Q : FiniteCyclicPresentation} (hPQ : HasCommonSubdivision P Q)
    (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    BoundaryRealizationEquivData P Q validP validQ :=
  Classical.choice
    (hPQ.exists_boundaryRealizationEquivData validP validQ)

end HasCommonSubdivision

namespace NormalizationStep

/-- Every validity-safe normalization step preserves the complete polygonal
boundary locus. -/
theorem exists_boundaryRealizationEquivData
    {P Q : ValidPresentation} (hPQ : NormalizationStep P Q) :
    Nonempty (BoundaryRealizationEquivData
      P.presentation Q.presentation P.valid Q.valid) := by
  cases hPQ with
  | commonSubdivision hcommon =>
      exact hcommon.exists_boundaryRealizationEquivData P.valid Q.valid
  | unoriented horiented =>
      rcases horiented with hforward | hbackward
      · rcases hforward with ⟨e⟩
        exact ⟨e.boundaryRealizationEquivData P.valid Q.valid⟩
      · rcases hbackward with ⟨e⟩
        exact ⟨(e.boundaryRealizationEquivData Q.valid P.valid).symm⟩
  | oneSidedP2 cut honeSided =>
      exact ⟨P2.oneSidedBoundaryRealizationEquivData
        P.presentation cut honeSided P.valid⟩

/-- Chosen boundary-faithful realization data for one normalization step. -/
noncomputable def boundaryRealizationEquivData
    {P Q : ValidPresentation} (hPQ : NormalizationStep P Q) :
    BoundaryRealizationEquivData
      P.presentation Q.presentation P.valid Q.valid :=
  Classical.choice hPQ.exists_boundaryRealizationEquivData

end NormalizationStep

namespace NormalizationEquivalent

/-- Every validity-safe normalization chain preserves the complete polygonal
boundary locus. -/
theorem exists_boundaryRealizationEquivData
    {P Q : ValidPresentation} (hPQ : NormalizationEquivalent P Q) :
    Nonempty (BoundaryRealizationEquivData
      P.presentation Q.presentation P.valid Q.valid) := by
  induction hPQ with
  | rel _ _ hstep =>
      exact hstep.exists_boundaryRealizationEquivData
  | refl P =>
      exact ⟨BoundaryRealizationEquivData.refl
        P.presentation P.valid⟩
  | symm _ _ _ ih =>
      exact ⟨(Classical.choice ih).symm⟩
  | trans _ _ _ _ _ ihPQ ihQR =>
      exact ⟨(Classical.choice ihPQ).trans
        (Classical.choice ihQR)⟩

/-- Chosen boundary-faithful realization data for a normalization chain. -/
noncomputable def boundaryRealizationEquivData
    {P Q : ValidPresentation} (hPQ : NormalizationEquivalent P Q) :
    BoundaryRealizationEquivData
      P.presentation Q.presentation P.valid Q.valid :=
  Classical.choice hPQ.exists_boundaryRealizationEquivData

end NormalizationEquivalent

namespace NormalizationResult

/-- The Gallier--Xu normalizer's chosen homeomorphism preserves the complete
polygonal boundary locus all the way to its exact canonical endpoint. -/
noncomputable def boundaryRealizationEquivData
    {P : ValidPresentation} (result : NormalizationResult P) :
    BoundaryRealizationEquivData
      P.presentation result.normalForm.canonicalPresentation
      P.valid
      (result.normalForm.canonicalPresentation_isSurfaceValid
        result.admissible) :=
  result.equivalent.boundaryRealizationEquivData

end NormalizationResult

/-- Boundary-relative Gallier--Xu normalization: every valid connected
finite-cyclic presentation is homeomorphic to its admissible canonical normal
form by a homeomorphism preserving precisely the once-used-side locus. -/
theorem exists_admissible_normalForm_boundaryRealizationEquivData
    (P : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid) (connectedP : P.IsConnected) :
    ∃ N : NormalForm, ∃ hN : N.IsEvalAdmissible,
      Nonempty (BoundaryRealizationEquivData
        P N.canonicalPresentation validP
        (N.canonicalPresentation_isSurfaceValid hN)) := by
  let result :=
    normalizeConnectedToCanonical ⟨P, validP⟩ connectedP
  exact ⟨result.normalForm, result.admissible,
    ⟨result.boundaryRealizationEquivData⟩⟩

end

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
