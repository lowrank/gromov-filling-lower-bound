import GromovFilling.BoundaryLocusClassification
import GromovFilling.NormalFormBoundaryObstruction
import ClassificationOfSurfaces.FiniteCyclicCanonicalRealization

/-!
# Canonical boundary loci in the raw surface quotients

The finite-cyclic normalizer remembers exactly the sides used once.  This
module identifies those sides at its canonical orientable and nonorientable
endpoints and follows them through the final adapter to the raw Lean-Eval
quotients.  In the one-boundary case the resulting set is exactly the range
of the canonical loop used by the parity obstruction.
-/

namespace GromovFilling

noncomputable section

open Complex Set
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.NormalForm
open LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex

/-- The unique finite-cyclic occurrence corresponding to the free `h_j`
side of an orientable canonical word. -/
def orientableCanonicalBoundaryOccurrence (p n : ℕ) (j : Fin n) :
    (canonicalPresentation (.orientable p n)).BoundaryOccurrence :=
  (FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv
      (orientableBoundaryWord p n)).symm
    (oneFaceOccurrence (orientableBoundaryWord p n)
      (orientableBoundaryPosition p n j 1))

/-- The unique finite-cyclic occurrence corresponding to the free `h_j`
side of a nonorientable canonical word. -/
def nonOrientableCanonicalBoundaryOccurrence (p n : ℕ) (j : Fin n) :
    (canonicalPresentation (.nonOrientable p n)).BoundaryOccurrence :=
  (FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv
      (nonOrientableBoundaryWord p n)).symm
    (oneFaceOccurrence (nonOrientableBoundaryWord p n)
      (nonOrientableBoundaryPosition p n j 1))

theorem orientableCanonicalBoundaryOccurrence_edge (p n : ℕ) (j : Fin n) :
    (orientableCanonicalBoundaryOccurrence p n j).edge =
      FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv
        (orientableBoundaryWord p n) (.h j) := by
  unfold orientableCanonicalBoundaryOccurrence
  change FiniteCyclicPresentation.edgeOfDart
      (FiniteCyclicPresentation.BoundaryOccurrence.dart
        ((FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv
          (orientableBoundaryWord p n)).symm
          (oneFaceOccurrence (orientableBoundaryWord p n)
            (orientableBoundaryPosition p n j 1)))) = _
  rw [← FiniteCyclicPresentation.ofOneFaceWordComapOccurrence_dart]
  rw [oneFaceOccurrence_dart, orientableBoundaryWord_get_boundary_h_pos]
  rfl

theorem nonOrientableCanonicalBoundaryOccurrence_edge
    (p n : ℕ) (j : Fin n) :
    (nonOrientableCanonicalBoundaryOccurrence p n j).edge =
      FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv
        (nonOrientableBoundaryWord p n) (.h j) := by
  unfold nonOrientableCanonicalBoundaryOccurrence
  change FiniteCyclicPresentation.edgeOfDart
      (FiniteCyclicPresentation.BoundaryOccurrence.dart
        ((FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv
          (nonOrientableBoundaryWord p n)).symm
          (oneFaceOccurrence (nonOrientableBoundaryWord p n)
            (nonOrientableBoundaryPosition p n j 1)))) = _
  rw [← FiniteCyclicPresentation.ofOneFaceWordComapOccurrence_dart]
  rw [oneFaceOccurrence_dart, nonOrientableBoundaryWord_get_boundary_h_pos]
  rfl

theorem orientableCanonicalBoundaryOccurrence_isBoundaryEdge
    (p n : ℕ) (j : Fin n) :
    (canonicalPresentation (.orientable p n)).IsBoundaryEdge
      (orientableCanonicalBoundaryOccurrence p n j).edge := by
  rw [orientableCanonicalBoundaryOccurrence_edge]
  unfold FiniteCyclicPresentation.IsBoundaryEdge
  change (FiniteCyclicPresentation.ofOneFaceWord
      (orientableBoundaryWord p n)).edgeMultiplicity
        (FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv
          (orientableBoundaryWord p n) (.h j)) = 1
  rw [FiniteCyclicPresentation.ofOneFaceWord_edgeMultiplicity]
  rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
  rw [← wordEdgeOccurrences_card_eq_count_edgeName]
  rw [orientableBoundaryWord_edge_occurrences]

theorem nonOrientableCanonicalBoundaryOccurrence_isBoundaryEdge
    (p n : ℕ) (j : Fin n) :
    (canonicalPresentation (.nonOrientable p n)).IsBoundaryEdge
      (nonOrientableCanonicalBoundaryOccurrence p n j).edge := by
  rw [nonOrientableCanonicalBoundaryOccurrence_edge]
  unfold FiniteCyclicPresentation.IsBoundaryEdge
  change (FiniteCyclicPresentation.ofOneFaceWord
      (nonOrientableBoundaryWord p n)).edgeMultiplicity
        (FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv
          (nonOrientableBoundaryWord p n) (.h j)) = 1
  rw [FiniteCyclicPresentation.ofOneFaceWord_edgeMultiplicity]
  rw [FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName]
  rw [← wordEdgeOccurrences_card_eq_count_edgeName]
  rw [nonOrientableBoundaryWord_edge_occurrences]

private theorem signedDart_edgeName_eq_edgeOfDart
    {Edge : Type} (d : SignedDart Edge) :
    SignedDart.edgeName d = FiniteCyclicPresentation.edgeOfDart d := by
  cases d <;> rfl

private theorem ofOneFaceWordMapOccurrence_edge
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge))
    (o : (FiniteCyclicPresentation.ofOneFaceWord word).BoundaryOccurrence) :
    o.edge = FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv word
      (FiniteCyclicPresentation.edgeOfDart
        ((oneFacePresentation Edge word).occurrenceDart
          (FiniteCyclicPresentation.ofOneFaceWordMapOccurrence word o))) := by
  have h := congrArg FiniteCyclicPresentation.edgeOfDart
    (FiniteCyclicPresentation.ofOneFaceWordMapOccurrence_dart word o)
  simpa only [FiniteCyclicPresentation.edgeOfDart_mapEquiv] using h.symm

private theorem exists_orientableEdge_eq_h_of_count_eq_one
    (p n : ℕ) (e : OrientableEdge p n)
    (hcount : ((orientableBoundaryWord p n).map
      FiniteCyclicPresentation.edgeOfDart).count e = 1) :
    ∃ j : Fin n, e = .h j := by
  cases e with
  | a i =>
      have h := orientableBoundaryWord_edge_occurrences p n (.a i)
      rw [wordEdgeOccurrences_card_eq_count_edgeName] at h
      rw [← FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName] at h
      simp only at h
      omega
  | b i =>
      have h := orientableBoundaryWord_edge_occurrences p n (.b i)
      rw [wordEdgeOccurrences_card_eq_count_edgeName] at h
      rw [← FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName] at h
      simp only at h
      omega
  | c j =>
      have h := orientableBoundaryWord_edge_occurrences p n (.c j)
      rw [wordEdgeOccurrences_card_eq_count_edgeName] at h
      rw [← FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName] at h
      simp only at h
      omega
  | h j => exact ⟨j, rfl⟩

/-- The free `h_j` sides are all the once-used sides of an orientable
canonical finite-cyclic presentation. -/
theorem exists_eq_orientableCanonicalBoundaryOccurrence_of_isBoundaryEdge
    {p n : ℕ}
    (o : (canonicalPresentation (.orientable p n)).BoundaryOccurrence)
    (ho : (canonicalPresentation (.orientable p n)).IsBoundaryEdge o.edge) :
    ∃ j : Fin n, o = orientableCanonicalBoundaryOccurrence p n j := by
  let word := orientableBoundaryWord p n
  let typed := FiniteCyclicPresentation.ofOneFaceWordMapOccurrence word o
  let i := oneFaceOccurrenceIndex typed
  have htypedIndex : typed = oneFaceOccurrence word i :=
    (oneFaceOccurrence_oneFaceOccurrenceIndex word typed).symm
  let e : OrientableEdge p n :=
    FiniteCyclicPresentation.edgeOfDart (word.get i)
  have hedge : o.edge =
      FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv word e := by
    have h := ofOneFaceWordMapOccurrence_edge word o
    change o.edge = FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv word
      (FiniteCyclicPresentation.edgeOfDart
        ((oneFacePresentation (OrientableEdge p n) word).occurrenceDart typed)) at h
    rw [htypedIndex] at h
    exact h
  have hcount :
      (word.map FiniteCyclicPresentation.edgeOfDart).count e = 1 := by
    change (FiniteCyclicPresentation.ofOneFaceWord word).IsBoundaryEdge
      o.edge at ho
    unfold FiniteCyclicPresentation.IsBoundaryEdge at ho
    rw [hedge, FiniteCyclicPresentation.ofOneFaceWord_edgeMultiplicity] at ho
    exact ho
  have he : ∃ j : Fin n, e = .h j :=
    exists_orientableEdge_eq_h_of_count_eq_one p n e (by
      simpa only [word] using hcount)
  rcases he with ⟨j, he⟩
  have hedgeTyped : FiniteCyclicPresentation.edgeOfDart (word.get i) = .h j := by
    exact (show FiniteCyclicPresentation.edgeOfDart (word.get i) = e
      from rfl).trans he
  have hmem : i ∈ wordEdgeOccurrences word (.h j) := by
    rw [mem_wordEdgeOccurrences]
    rw [signedDart_edgeName_eq_edgeOfDart]
    exact hedgeTyped
  have hmem' : i ∈ wordEdgeOccurrences
      (orientableBoundaryWord p n) (.h j) := by
    simpa only [word] using hmem
  rw [orientableBoundaryWord_edgeOccurrences_h] at hmem'
  have hindex : i = orientableBoundaryPosition p n j 1 :=
    Finset.mem_singleton.mp hmem'
  have htyped : typed = oneFaceOccurrence word
      (orientableBoundaryPosition p n j 1) := by
    calc
      typed = oneFaceOccurrence word i := htypedIndex
      _ = oneFaceOccurrence word (orientableBoundaryPosition p n j 1) :=
        congrArg (oneFaceOccurrence word) hindex
  refine ⟨j, ?_⟩
  apply (FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv word).injective
  unfold orientableCanonicalBoundaryOccurrence
  rw [FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv_apply]
  rw [FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv_apply]
  rw [FiniteCyclicPresentation.ofOneFaceWordMapOccurrence_comap]
  exact htyped

private theorem exists_nonOrientableEdge_eq_h_of_count_eq_one
    (p n : ℕ) (e : NonOrientableEdge p n)
    (hcount : ((nonOrientableBoundaryWord p n).map
      FiniteCyclicPresentation.edgeOfDart).count e = 1) :
    ∃ j : Fin n, e = .h j := by
  cases e with
  | a i =>
      have h := nonOrientableBoundaryWord_edge_occurrences p n (.a i)
      rw [wordEdgeOccurrences_card_eq_count_edgeName] at h
      rw [← FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName] at h
      simp only at h
      omega
  | c j =>
      have h := nonOrientableBoundaryWord_edge_occurrences p n (.c j)
      rw [wordEdgeOccurrences_card_eq_count_edgeName] at h
      rw [← FiniteCyclicPresentation.map_edgeOfDart_eq_map_edgeName] at h
      simp only at h
      omega
  | h j => exact ⟨j, rfl⟩

/-- The free `h_j` sides are all the once-used sides of a nonorientable
canonical finite-cyclic presentation. -/
theorem exists_eq_nonOrientableCanonicalBoundaryOccurrence_of_isBoundaryEdge
    {p n : ℕ}
    (o : (canonicalPresentation (.nonOrientable p n)).BoundaryOccurrence)
    (ho : (canonicalPresentation (.nonOrientable p n)).IsBoundaryEdge o.edge) :
    ∃ j : Fin n, o = nonOrientableCanonicalBoundaryOccurrence p n j := by
  let word := nonOrientableBoundaryWord p n
  let typed := FiniteCyclicPresentation.ofOneFaceWordMapOccurrence word o
  let i := oneFaceOccurrenceIndex typed
  have htypedIndex : typed = oneFaceOccurrence word i :=
    (oneFaceOccurrence_oneFaceOccurrenceIndex word typed).symm
  let e : NonOrientableEdge p n :=
    FiniteCyclicPresentation.edgeOfDart (word.get i)
  have hedge : o.edge =
      FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv word e := by
    have h := ofOneFaceWordMapOccurrence_edge word o
    change o.edge = FiniteCyclicPresentation.ofOneFaceWordEdgeEquiv word
      (FiniteCyclicPresentation.edgeOfDart
        ((oneFacePresentation (NonOrientableEdge p n) word).occurrenceDart typed)) at h
    rw [htypedIndex] at h
    exact h
  have hcount :
      (word.map FiniteCyclicPresentation.edgeOfDart).count e = 1 := by
    change (FiniteCyclicPresentation.ofOneFaceWord word).IsBoundaryEdge
      o.edge at ho
    unfold FiniteCyclicPresentation.IsBoundaryEdge at ho
    rw [hedge, FiniteCyclicPresentation.ofOneFaceWord_edgeMultiplicity] at ho
    exact ho
  have he : ∃ j : Fin n, e = .h j :=
    exists_nonOrientableEdge_eq_h_of_count_eq_one p n e (by
      simpa only [word] using hcount)
  rcases he with ⟨j, he⟩
  have hedgeTyped : FiniteCyclicPresentation.edgeOfDart (word.get i) = .h j := by
    exact (show FiniteCyclicPresentation.edgeOfDart (word.get i) = e
      from rfl).trans he
  have hmem : i ∈ wordEdgeOccurrences word (.h j) := by
    rw [mem_wordEdgeOccurrences]
    rw [signedDart_edgeName_eq_edgeOfDart]
    exact hedgeTyped
  have hmem' : i ∈ wordEdgeOccurrences
      (nonOrientableBoundaryWord p n) (.h j) := by
    simpa only [word] using hmem
  rw [nonOrientableBoundaryWord_edgeOccurrences_h] at hmem'
  have hindex : i = nonOrientableBoundaryPosition p n j 1 :=
    Finset.mem_singleton.mp hmem'
  have htyped : typed = oneFaceOccurrence word
      (nonOrientableBoundaryPosition p n j 1) := by
    calc
      typed = oneFaceOccurrence word i := htypedIndex
      _ = oneFaceOccurrence word (nonOrientableBoundaryPosition p n j 1) :=
        congrArg (oneFaceOccurrence word) hindex
  refine ⟨j, ?_⟩
  apply (FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv word).injective
  unfold nonOrientableCanonicalBoundaryOccurrence
  rw [FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv_apply]
  rw [FiniteCyclicPresentation.ofOneFaceWordOccurrenceEquiv_apply]
  rw [FiniteCyclicPresentation.ofOneFaceWordMapOccurrence_comap]
  exact htyped

private theorem ofOneFaceWordRealizationHomeomorph_polygonalMk
    {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge))
    (validFinite : (FiniteCyclicPresentation.ofOneFaceWord word).IsSurfaceValid)
    (validTyped : (oneFacePresentation Edge word).OccurrencePairingValid)
    (x : (FiniteCyclicPresentation.ofOneFaceWord word).PolygonalPreRealization) :
    FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
        word validFinite validTyped
        ((FiniteCyclicPresentation.ofOneFaceWord word).polygonalMk validFinite x) =
      (oneFacePresentation Edge word).polygonalMk validTyped
        (FiniteCyclicPresentation.ofOneFaceWordPreHomeomorph word x) := by
  rfl

private theorem orientablePolygonalRealizationHomeomorph_polygonalMk
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    (x : (orientableCellComplex p n).PolygonalPreRealization) :
    orientablePolygonalRealizationHomeomorph hvalid
        ((orientableCellComplex p n).polygonalMk
          (orientableCellComplex_occurrencePairingValid hvalid) x) =
      Quot.mk (OrientableRel p n)
        (oneFacePolygonalPreRealizationHomeomorph
          (orientableBoundaryWord p n) x) := by
  rfl

private theorem nonOrientablePolygonalRealizationHomeomorph_polygonalMk
    {p n : ℕ} (hp : 1 ≤ p)
    (x : (nonOrientableCellComplex p n).PolygonalPreRealization) :
    nonOrientablePolygonalRealizationHomeomorph hp
        ((nonOrientableCellComplex p n).polygonalMk
          (nonOrientableCellComplex_occurrencePairingValid hp) x) =
      Quot.mk (NonOrientableRel p n)
        (oneFacePolygonalPreRealizationHomeomorph
          (nonOrientableBoundaryWord p n) x) := by
  rfl

/-- The final orientable adapter is parameter-exact on a canonical free
side, up to the raw quotient's closed-disk coordinates. -/
theorem canonicalOrientableRealizationHomeomorph_boundaryOccurrence_point
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n)
    (t : unitInterval) :
    canonicalOrientableRealizationHomeomorph hvalid
        ((canonicalPresentation (.orientable p n)).polygonalMk
          (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
          (((canonicalPresentation (.orientable p n)).occurrenceSide
            (orientableCanonicalBoundaryOccurrence p n j)).point t)) =
      Quot.mk (OrientableRel p n)
        (ClosedUnitDisc.bdyPtOfReal
          ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
            (4 * p + 3 * n))) := by
  simp only [canonicalOrientableRealizationHomeomorph]
  simp only [canonicalPresentation_orientable]
  change orientablePolygonalRealizationHomeomorph hvalid
      (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
        (orientableBoundaryWord p n)
        (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
        (orientableCellComplex_occurrencePairingValid hvalid)
        ((FiniteCyclicPresentation.ofOneFaceWord
            (orientableBoundaryWord p n)).polygonalMk
          (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
          (((FiniteCyclicPresentation.ofOneFaceWord
              (orientableBoundaryWord p n)).occurrenceSide
            (orientableCanonicalBoundaryOccurrence p n j)).point t))) = _
  rw [ofOneFaceWordRealizationHomeomorph_polygonalMk]
  change orientablePolygonalRealizationHomeomorph hvalid
      ((orientableCellComplex p n).polygonalMk
        (orientableCellComplex_occurrencePairingValid hvalid)
        (FiniteCyclicPresentation.ofOneFaceWordPreHomeomorph
          (orientableBoundaryWord p n)
          (((FiniteCyclicPresentation.ofOneFaceWord
              (orientableBoundaryWord p n)).occurrenceSide
            (orientableCanonicalBoundaryOccurrence p n j)).point t))) = _
  rw [orientablePolygonalRealizationHomeomorph_polygonalMk]
  rw [FiniteCyclicPresentation.ofOneFaceWordPreHomeomorph_occurrenceSide_point]
  rw [orientableCanonicalBoundaryOccurrence]
  rw [FiniteCyclicPresentation.ofOneFaceWordMapOccurrence_comap]
  change Quot.mk (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t)) = _
  rw [orientableCarrier_boundary_h_pos]

/-- The final nonorientable adapter is parameter-exact on a canonical free
side, up to the raw quotient's closed-disk coordinates. -/
theorem canonicalNonOrientableRealizationHomeomorph_boundaryOccurrence_point
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n) (t : unitInterval) :
    canonicalNonOrientableRealizationHomeomorph hp
        ((canonicalPresentation (.nonOrientable p n)).polygonalMk
          (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
          (((canonicalPresentation (.nonOrientable p n)).occurrenceSide
            (nonOrientableCanonicalBoundaryOccurrence p n j)).point t)) =
      Quot.mk (NonOrientableRel p n)
        (ClosedUnitDisc.bdyPtOfReal
          ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
            (2 * p + 3 * n))) := by
  simp only [canonicalNonOrientableRealizationHomeomorph]
  simp only [canonicalPresentation_nonOrientable]
  change nonOrientablePolygonalRealizationHomeomorph hp
      (FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph
        (nonOrientableBoundaryWord p n)
        (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
        (nonOrientableCellComplex_occurrencePairingValid hp)
        ((FiniteCyclicPresentation.ofOneFaceWord
            (nonOrientableBoundaryWord p n)).polygonalMk
          (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
          (((FiniteCyclicPresentation.ofOneFaceWord
              (nonOrientableBoundaryWord p n)).occurrenceSide
            (nonOrientableCanonicalBoundaryOccurrence p n j)).point t))) = _
  rw [ofOneFaceWordRealizationHomeomorph_polygonalMk]
  change nonOrientablePolygonalRealizationHomeomorph hp
      ((nonOrientableCellComplex p n).polygonalMk
        (nonOrientableCellComplex_occurrencePairingValid hp)
        (FiniteCyclicPresentation.ofOneFaceWordPreHomeomorph
          (nonOrientableBoundaryWord p n)
          (((FiniteCyclicPresentation.ofOneFaceWord
              (nonOrientableBoundaryWord p n)).occurrenceSide
            (nonOrientableCanonicalBoundaryOccurrence p n j)).point t))) = _
  rw [nonOrientablePolygonalRealizationHomeomorph_polygonalMk]
  rw [FiniteCyclicPresentation.ofOneFaceWordPreHomeomorph_occurrenceSide_point]
  rw [nonOrientableCanonicalBoundaryOccurrence]
  rw [FiniteCyclicPresentation.ofOneFaceWordMapOccurrence_comap]
  change Quot.mk (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t)) = _
  rw [nonOrientableCarrier_boundary_h_pos]

/-- The complete free-side locus in the raw orientable quotient. -/
def orientableRawBoundaryLocus (p n : ℕ) :
    Set (Quot (OrientableRel p n)) :=
  {q | ∃ (j : Fin n) (t : unitInterval),
    q = Quot.mk (OrientableRel p n)
      (ClosedUnitDisc.bdyPtOfReal
        ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
          (4 * p + 3 * n)))}

/-- The complete free-side locus in the raw nonorientable quotient. -/
def nonOrientableRawBoundaryLocus (p n : ℕ) :
    Set (Quot (NonOrientableRel p n)) :=
  {q | ∃ (j : Fin n) (t : unitInterval),
    q = Quot.mk (NonOrientableRel p n)
      (ClosedUnitDisc.bdyPtOfReal
        ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
          (2 * p + 3 * n)))}

/-- The final orientable adapter carries the full finite-cyclic boundary
locus onto exactly the raw quotient's free-side locus. -/
theorem image_canonicalOrientableRealizationHomeomorph_polygonalBoundaryLocus
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    canonicalOrientableRealizationHomeomorph hvalid ''
        (canonicalPresentation (.orientable p n)).PolygonalBoundaryLocus
          (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid) =
      orientableRawBoundaryLocus p n := by
  ext q
  constructor
  · rintro ⟨x, ⟨o, t, ho, rfl⟩, rfl⟩
    obtain ⟨j, rfl⟩ :=
      exists_eq_orientableCanonicalBoundaryOccurrence_of_isBoundaryEdge o ho
    exact ⟨j, t,
      canonicalOrientableRealizationHomeomorph_boundaryOccurrence_point
        hvalid j t⟩
  · rintro ⟨j, t, rfl⟩
    let x := (canonicalPresentation (.orientable p n)).polygonalMk
      (canonicalPresentation_isSurfaceValid (.orientable p n) hvalid)
      (((canonicalPresentation (.orientable p n)).occurrenceSide
        (orientableCanonicalBoundaryOccurrence p n j)).point t)
    refine ⟨x, ?_, ?_⟩
    · exact ⟨orientableCanonicalBoundaryOccurrence p n j, t,
        orientableCanonicalBoundaryOccurrence_isBoundaryEdge p n j, rfl⟩
    · exact
        canonicalOrientableRealizationHomeomorph_boundaryOccurrence_point
          hvalid j t

/-- The final nonorientable adapter carries the full finite-cyclic boundary
locus onto exactly the raw quotient's free-side locus. -/
theorem image_canonicalNonOrientableRealizationHomeomorph_polygonalBoundaryLocus
    {p n : ℕ} (hp : 1 ≤ p) :
    canonicalNonOrientableRealizationHomeomorph hp ''
        (canonicalPresentation (.nonOrientable p n)).PolygonalBoundaryLocus
          (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp) =
      nonOrientableRawBoundaryLocus p n := by
  ext q
  constructor
  · rintro ⟨x, ⟨o, t, ho, rfl⟩, rfl⟩
    obtain ⟨j, rfl⟩ :=
      exists_eq_nonOrientableCanonicalBoundaryOccurrence_of_isBoundaryEdge o ho
    exact ⟨j, t,
      canonicalNonOrientableRealizationHomeomorph_boundaryOccurrence_point
        hp j t⟩
  · rintro ⟨j, t, rfl⟩
    let x := (canonicalPresentation (.nonOrientable p n)).polygonalMk
      (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hp)
      (((canonicalPresentation (.nonOrientable p n)).occurrenceSide
        (nonOrientableCanonicalBoundaryOccurrence p n j)).point t)
    refine ⟨x, ?_, ?_⟩
    · exact ⟨nonOrientableCanonicalBoundaryOccurrence p n j, t,
        nonOrientableCanonicalBoundaryOccurrence_isBoundaryEdge p n j, rfl⟩
    · exact
        canonicalNonOrientableRealizationHomeomorph_boundaryOccurrence_point
          hp j t

private theorem orientableRawBoundaryPoint_eq_normalBoundaryArc
    (p : ℕ) (t : unitInterval) :
    Quot.mk (OrientableRel p 1)
        (ClosedUnitDisc.bdyPtOfReal
          ((4 * (p : ℝ) + 1 + (t : ℝ)) / (4 * p + 3))) =
      orientableNormalBoundaryArc p t := by
  unfold orientableNormalBoundaryArc orientableNormalBoundaryCarrierArc
  apply congrArg (Quot.mk (OrientableRel p 1))
  have hden : 4 * (p : ℝ) + 3 ≠ 0 := by positivity
  have harg :
      (4 * (p : ℝ) + 1 + (t : ℝ)) / (4 * p + 3) =
        ((t : ℝ) - 2) / (4 * p + 3) + (1 : ℤ) := by
    norm_num only [Int.cast_one]
    field_simp
    ring
  rw [harg]
  exact ClosedUnitDisc.bdyPtOfReal_add_int _ 1

private theorem nonOrientableRawBoundaryPoint_eq_normalBoundaryArc
    (p : ℕ) (t : unitInterval) :
    Quot.mk (NonOrientableRel p 1)
        (ClosedUnitDisc.bdyPtOfReal
          ((2 * (p : ℝ) + 1 + (t : ℝ)) / (2 * p + 3))) =
      nonOrientableNormalBoundaryArc p t := by
  unfold nonOrientableNormalBoundaryArc nonOrientableNormalBoundaryCarrierArc
  apply congrArg (Quot.mk (NonOrientableRel p 1))
  have hden : 2 * (p : ℝ) + 3 ≠ 0 := by positivity
  have harg :
      (2 * (p : ℝ) + 1 + (t : ℝ)) / (2 * p + 3) =
        ((t : ℝ) - 2) / (2 * p + 3) + (1 : ℤ) := by
    norm_num only [Int.cast_one]
    field_simp
    ring
  rw [harg]
  exact ClosedUnitDisc.bdyPtOfReal_add_int _ 1

/-- With one boundary block, the complete raw orientable free-side locus is
exactly the range of the canonical obstruction loop. -/
theorem orientableRawBoundaryLocus_one_eq_range (p : ℕ) :
    orientableRawBoundaryLocus p 1 =
      Set.range (orientableNormalBoundaryLoop p) := by
  ext q
  constructor
  · rintro ⟨j, t, rfl⟩
    have hj : j = 0 := Fin.eq_zero j
    subst j
    refine ⟨((t : ℝ) : UnitAddCircle), ?_⟩
    rw [orientableNormalBoundaryLoop_apply_unitInterval]
    simpa using (orientableRawBoundaryPoint_eq_normalBoundaryArc p t).symm
  · rintro ⟨s, rfl⟩
    obtain ⟨x, hx, hxs⟩ := AddCircle.eq_coe_Ico s
    let t : unitInterval := ⟨x, hx.1, hx.2.le⟩
    refine ⟨0, t, ?_⟩
    rw [← hxs]
    change orientableNormalBoundaryLoop p
        (((t : unitInterval) : ℝ) : UnitAddCircle) = _
    rw [orientableNormalBoundaryLoop_apply_unitInterval]
    simpa using (orientableRawBoundaryPoint_eq_normalBoundaryArc p t).symm

/-- With one boundary block, the complete raw nonorientable free-side locus
is exactly the range of the canonical obstruction loop. -/
theorem nonOrientableRawBoundaryLocus_one_eq_range (p : ℕ) :
    nonOrientableRawBoundaryLocus p 1 =
      Set.range (nonOrientableNormalBoundaryLoop p) := by
  ext q
  constructor
  · rintro ⟨j, t, rfl⟩
    have hj : j = 0 := Fin.eq_zero j
    subst j
    refine ⟨((t : ℝ) : UnitAddCircle), ?_⟩
    rw [nonOrientableNormalBoundaryLoop_apply_unitInterval]
    simpa using (nonOrientableRawBoundaryPoint_eq_normalBoundaryArc p t).symm
  · rintro ⟨s, rfl⟩
    obtain ⟨x, hx, hxs⟩ := AddCircle.eq_coe_Ico s
    let t : unitInterval := ⟨x, hx.1, hx.2.le⟩
    refine ⟨0, t, ?_⟩
    rw [← hxs]
    change nonOrientableNormalBoundaryLoop p
        (((t : unitInterval) : ℝ) : UnitAddCircle) = _
    rw [nonOrientableNormalBoundaryLoop_apply_unitInterval]
    simpa using (nonOrientableRawBoundaryPoint_eq_normalBoundaryArc p t).symm

/-- In the one-boundary orientable case, the final canonical adapter carries
the complete once-used-side locus onto precisely the canonical obstruction
loop. -/
theorem image_canonicalOrientableRealizationHomeomorph_boundaryLocus_one
    (p : ℕ) :
    canonicalOrientableRealizationHomeomorph
        (p := p) (n := 1) (Or.inr (by omega)) ''
        (canonicalPresentation (.orientable p 1)).PolygonalBoundaryLocus
          (canonicalPresentation_isSurfaceValid (.orientable p 1)
            (Or.inr (by omega))) =
      Set.range (orientableNormalBoundaryLoop p) :=
  (image_canonicalOrientableRealizationHomeomorph_polygonalBoundaryLocus
    (p := p) (n := 1) (Or.inr (by omega))).trans
      (orientableRawBoundaryLocus_one_eq_range p)

/-- In the one-boundary nonorientable case, the final canonical adapter
carries the complete once-used-side locus onto precisely the canonical
obstruction loop. -/
theorem image_canonicalNonOrientableRealizationHomeomorph_boundaryLocus_one
    (p : ℕ) (hp : 1 ≤ p) :
    canonicalNonOrientableRealizationHomeomorph (p := p) (n := 1) hp ''
        (canonicalPresentation (.nonOrientable p 1)).PolygonalBoundaryLocus
          (canonicalPresentation_isSurfaceValid (.nonOrientable p 1) hp) =
      Set.range (nonOrientableNormalBoundaryLoop p) :=
  (image_canonicalNonOrientableRealizationHomeomorph_polygonalBoundaryLocus
    (p := p) (n := 1) hp).trans
      (nonOrientableRawBoundaryLocus_one_eq_range p)

end

end GromovFilling
