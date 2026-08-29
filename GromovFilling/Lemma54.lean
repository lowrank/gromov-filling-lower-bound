import GromovFilling.CanonicalBoundaryConnectedness
import GromovFilling.RadoAmbientBoundary

/-!
# Lemma 5.4: the odd boundary-degree obstruction for compact surfaces

This file closes the relative-boundary classification argument.  A boundary-aware Radó
triangulation is normalized through boundary-faithful polygonal homeomorphisms.  Connectedness
of the supplied Jordan boundary forces the canonical endpoint to have exactly one free boundary
block.  The canonical parity obstruction then transfers back through the surface homeomorphism
and the unique circle reparametrization of the boundary.
-/

open scoped Manifold

namespace GromovFilling

noncomputable section

open Set
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.NormalForm

private theorem image_eq_of_homeomorph_mapsTo
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} {t : Set Y}
    (hforward : Set.MapsTo e s t)
    (hbackward : Set.MapsTo e.symm t s) :
    e '' s = t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hforward hx
  · intro y hy
    exact ⟨e.symm y, hbackward hy, e.apply_symm_apply y⟩

private theorem image_symm_eq_of_image_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} {t : Set Y} (h : e '' s = t) :
    e.symm '' t = s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [← h] at hy
    rcases hy with ⟨x, hx, rfl⟩
    simpa using hx
  · intro x hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    rw [← h]
    exact ⟨x, hx, rfl⟩

private noncomputable def circleRangeHomeomorph
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    UnitAddCircle ≃ₜ Set.range curve := by
  let toRange : UnitAddCircle → Set.range curve := fun x ↦
    ⟨curve x, ⟨x, rfl⟩⟩
  have hbijective : Function.Bijective toRange := by
    constructor
    · intro x y hxy
      exact hinjective (congrArg Subtype.val hxy)
    · rintro ⟨_y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e : UnitAddCircle ≃ Set.range curve :=
    Equiv.ofBijective toRange hbijective
  have heContinuous : Continuous e := by
    change Continuous toRange
    exact hcurve.subtype_mk (fun x ↦ ⟨x, rfl⟩)
  exact Continuous.homeoOfEquivCompactToT2 heContinuous

@[simp]
private theorem circleRangeHomeomorph_coe
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) (x : UnitAddCircle) :
    ((circleRangeHomeomorph curve hcurve hinjective x : Set.range curve) : Y) =
      curve x :=
  rfl

/-- Two continuous injective circle parametrizations with the same range differ by a circle
homeomorphism. -/
theorem exists_circleHomeomorph_of_continuous_injective_of_range_eq
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f g : UnitAddCircle → Y)
    (hf : Continuous f) (hfi : Function.Injective f)
    (hg : Continuous g) (hgi : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    ∃ e : UnitAddCircle ≃ₜ UnitAddCircle, f = g ∘ e := by
  let ef : UnitAddCircle ≃ₜ Set.range f :=
    circleRangeHomeomorph f hf hfi
  let eg : UnitAddCircle ≃ₜ Set.range g :=
    circleRangeHomeomorph g hg hgi
  let e : UnitAddCircle ≃ₜ UnitAddCircle :=
    (ef.trans (Homeomorph.setCongr hrange)).trans eg.symm
  refine ⟨e, ?_⟩
  funext x
  have heq : eg (e x) = Homeomorph.setCongr hrange (ef x) := by
    exact eg.apply_symm_apply (Homeomorph.setCongr hrange (ef x))
  have hval := congrArg Subtype.val heq
  simpa only [Function.comp_apply, circleRangeHomeomorph_coe] using hval.symm

/-- **Lemma 5.4, topological core.**  If the whole boundary of a compact connected Hausdorff
topological surface is parametrized by a Jordan circle, then no circle-valued map on the surface
can restrict to odd degree on that boundary. -/
theorem hasOddBoundaryDegreeObstruction_of_compact_connected_surface_boundary
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (boundary : UnitAddCircle → S)
    (hboundary : Continuous boundary)
    (hinjective : Function.Injective boundary)
    (hrange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S) :
    HasOddBoundaryDegreeObstruction boundary := by
  obtain ⟨P, hPcovers, hPregular, _hPincidence⟩ :=
    exists_full_support_boundary_facewise_regular_partial_triangulation S
  let T := P.toGeometricTriangulation hPcovers
  let valid : T.toFiniteCyclicPresentation.IsSurfaceValid :=
    T.toFiniteCyclicPresentation_isSurfaceValid T.surfaceIncidence
  let connected : T.toFiniteCyclicPresentation.IsConnected :=
    T.toFiniteCyclicPresentation_isConnected T.surfaceIncidence
  let hstar : TriangleFamily.IsStrongVertexStarConnected T.faces :=
    T.faces_isStrongVertexStarConnected
  let hregular : T.BoundaryFacewiseRegular := by
    simpa only [T] using
      GeometricTriangulation.boundaryFacewiseRegular_toGeometricTriangulation
        P hPcovers hPregular
  let eP : T.toFiniteCyclicPresentation.PolygonalRealization valid ≃ₜ S :=
    (T.polygonalRealizationHomeomorph valid hstar).trans T.homeo
  have hPboundary :
      eP '' T.toFiniteCyclicPresentation.PolygonalBoundaryLocus valid =
        (modelWithCornersEuclideanHalfSpace 2).boundary S := by
    change (fun x ↦ T.homeo
      (T.polygonalRealizationHomeomorph valid hstar x)) ''
        T.toFiniteCyclicPresentation.PolygonalBoundaryLocus valid = _
    rw [← Set.image_image]
    rw [T.image_polygonalBoundaryLocus_polygonalRealizationHomeomorph
      valid hstar]
    exact T.image_simplicialBoundaryLocus_eq_boundary_of_circle
      hregular boundary hboundary hinjective hrange
  obtain ⟨N, hN, ⟨D⟩⟩ :=
    T.toFiniteCyclicPresentation
      |>.exists_admissible_normalForm_boundaryRealizationEquivData
        valid connected
  let eN : N.canonicalPresentation.PolygonalRealization
        (N.canonicalPresentation_isSurfaceValid hN) ≃ₜ S :=
    D.homeomorph.symm.trans eP
  have hDsymm :
      D.homeomorph.symm ''
          N.canonicalPresentation.PolygonalBoundaryLocus
            (N.canonicalPresentation_isSurfaceValid hN) =
        T.toFiniteCyclicPresentation.PolygonalBoundaryLocus valid :=
    image_eq_of_homeomorph_mapsTo D.homeomorph.symm
      D.symm_maps_boundary D.maps_boundary
  have hNboundary :
      eN '' N.canonicalPresentation.PolygonalBoundaryLocus
          (N.canonicalPresentation_isSurfaceValid hN) =
        Set.range boundary := by
    change (fun x ↦ eP (D.homeomorph.symm x)) ''
      N.canonicalPresentation.PolygonalBoundaryLocus
        (N.canonicalPresentation_isSurfaceValid hN) = _
    rw [← Set.image_image, hDsymm, hPboundary, ← hrange]
  cases N with
  | sphere =>
      have hb : boundary 0 ∈ Set.range boundary := ⟨0, rfl⟩
      have hempty :
          (NormalForm.canonicalPresentation .sphere).PolygonalBoundaryLocus
              (NormalForm.canonicalPresentation_isSurfaceValid .sphere hN) = ∅ := by
        ext q
        constructor
        · rintro ⟨o, _t, ho, _hq⟩
          exact (FiniteCyclicPresentation.twoMonogon_not_isBoundaryEdge
            o.edge (by simpa using ho)).elim
        · intro hq
          exact hq.elim
      rw [← hNboundary, hempty, Set.image_empty] at hb
      exact hb.elim
  | orientable p n =>
      let eRaw : Quot (OrientableRel p n) ≃ₜ S :=
        (canonicalOrientableRealizationHomeomorph hN).symm.trans eN
      letI : T2Space (Quot (OrientableRel p n)) :=
        eRaw.isEmbedding.t2Space
      have hcanonicalAdapterSymm :
          (canonicalOrientableRealizationHomeomorph hN).symm ''
              orientableRawBoundaryLocus p n =
            (canonicalPresentation (.orientable p n)).PolygonalBoundaryLocus
              (canonicalPresentation_isSurfaceValid (.orientable p n) hN) :=
        image_symm_eq_of_image_eq
          (canonicalOrientableRealizationHomeomorph hN)
          (image_canonicalOrientableRealizationHomeomorph_polygonalBoundaryLocus
            hN)
      have hRawBoundary :
          eRaw '' orientableRawBoundaryLocus p n = Set.range boundary := by
        change (fun x ↦ eN
          ((canonicalOrientableRealizationHomeomorph hN).symm x)) ''
            orientableRawBoundaryLocus p n = _
        rw [← Set.image_image, hcanonicalAdapterSymm]
        exact hNboundary
      have hRawConnected : IsConnected (orientableRawBoundaryLocus p n) := by
        apply (eRaw.isConnected_image).mp
        rw [hRawBoundary]
        exact isConnected_range hboundary
      have hn : n = 1 :=
        orientableRawBoundaryLocus_eq_one_of_isConnected hN hRawConnected
      subst n
      have hCanonicalRange :
          Set.range (eRaw ∘ orientableNormalBoundaryLoop p) =
            Set.range boundary := by
        rw [Set.range_comp, ← orientableRawBoundaryLocus_one_eq_range]
        exact hRawBoundary
      have hCanonicalContinuous :
          Continuous (eRaw ∘ orientableNormalBoundaryLoop p) :=
        eRaw.continuous.comp (continuous_orientableNormalBoundaryLoop p)
      have hCanonicalInjective :
          Function.Injective (eRaw ∘ orientableNormalBoundaryLoop p) :=
        eRaw.injective.comp (injective_orientableNormalBoundaryLoop p)
      have hCanonicalObstruction :
          HasOddBoundaryDegreeObstruction
            (eRaw ∘ orientableNormalBoundaryLoop p) :=
        hasOddBoundaryDegreeObstruction_of_homeomorph eRaw rfl
          (hasOddBoundaryDegreeObstruction_orientableNormalBoundaryLoop p)
      obtain ⟨r, hreparam⟩ :=
        exists_circleHomeomorph_of_continuous_injective_of_range_eq
          boundary (eRaw ∘ orientableNormalBoundaryLoop p)
          hboundary hinjective hCanonicalContinuous hCanonicalInjective
          hCanonicalRange.symm
      exact hasOddBoundaryDegreeObstruction_of_circleHomeomorph_reparametrization
        r hreparam hCanonicalObstruction
  | nonOrientable p n =>
      let eRaw : Quot (NonOrientableRel p n) ≃ₜ S :=
        (canonicalNonOrientableRealizationHomeomorph hN).symm.trans eN
      letI : T2Space (Quot (NonOrientableRel p n)) :=
        eRaw.isEmbedding.t2Space
      have hcanonicalAdapterSymm :
          (canonicalNonOrientableRealizationHomeomorph hN).symm ''
              nonOrientableRawBoundaryLocus p n =
            (canonicalPresentation (.nonOrientable p n)).PolygonalBoundaryLocus
              (canonicalPresentation_isSurfaceValid (.nonOrientable p n) hN) :=
        image_symm_eq_of_image_eq
          (canonicalNonOrientableRealizationHomeomorph hN)
          (image_canonicalNonOrientableRealizationHomeomorph_polygonalBoundaryLocus
            hN)
      have hRawBoundary :
          eRaw '' nonOrientableRawBoundaryLocus p n = Set.range boundary := by
        change (fun x ↦ eN
          ((canonicalNonOrientableRealizationHomeomorph hN).symm x)) ''
            nonOrientableRawBoundaryLocus p n = _
        rw [← Set.image_image, hcanonicalAdapterSymm]
        exact hNboundary
      have hRawConnected : IsConnected (nonOrientableRawBoundaryLocus p n) := by
        apply (eRaw.isConnected_image).mp
        rw [hRawBoundary]
        exact isConnected_range hboundary
      have hn : n = 1 :=
        nonOrientableRawBoundaryLocus_eq_one_of_isConnected hN hRawConnected
      subst n
      have hCanonicalRange :
          Set.range (eRaw ∘ nonOrientableNormalBoundaryLoop p) =
            Set.range boundary := by
        rw [Set.range_comp, ← nonOrientableRawBoundaryLocus_one_eq_range]
        exact hRawBoundary
      have hCanonicalContinuous :
          Continuous (eRaw ∘ nonOrientableNormalBoundaryLoop p) :=
        eRaw.continuous.comp (continuous_nonOrientableNormalBoundaryLoop p)
      have hCanonicalInjective :
          Function.Injective (eRaw ∘ nonOrientableNormalBoundaryLoop p) :=
        eRaw.injective.comp (injective_nonOrientableNormalBoundaryLoop p hN)
      have hCanonicalObstruction :
          HasOddBoundaryDegreeObstruction
            (eRaw ∘ nonOrientableNormalBoundaryLoop p) :=
        hasOddBoundaryDegreeObstruction_of_homeomorph eRaw rfl
          (hasOddBoundaryDegreeObstruction_nonOrientableNormalBoundaryLoop p hN)
      obtain ⟨r, hreparam⟩ :=
        exists_circleHomeomorph_of_continuous_injective_of_range_eq
          boundary (eRaw ∘ nonOrientableNormalBoundaryLoop p)
          hboundary hinjective hCanonicalContinuous hCanonicalInjective
          hCanonicalRange.symm
      exact hasOddBoundaryDegreeObstruction_of_circleHomeomorph_reparametrization
        r hreparam hCanonicalObstruction

end

end GromovFilling
