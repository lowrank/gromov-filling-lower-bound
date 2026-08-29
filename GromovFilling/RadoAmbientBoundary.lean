import GromovFilling.RadoBoundaryLocus
import ClassificationOfSurfaces.Moise.EmbeddedComplexBoundary
import Mathlib.Topology.Perfect

/-!
# The Radó simplicial boundary is the ambient manifold boundary

This file proves the topological half of the boundary bridge for Lemma 5.4.  The local
half-disk/disk theorem identifies edge-midpoint boundary status with valence one.  Radó's
facewise regularity then propagates that status along every exposed edge; preperfectness of the
ambient boundary rules out a boundary vertex with no incident exposed edge.
-/

open scoped Manifold

namespace LeanEval.Topology.ClassificationOfSurfaces

open Set

namespace GeometricTriangulation

noncomputable section

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanHalfSpace 2) S]

/-- On each triangle of a geometric triangulation, the ambient manifold boundary is an exposed
simplicial face of cardinality at most one-dimensional. -/
def BoundaryFacewiseRegular (T : GeometricTriangulation S) : Prop :=
  ∀ t ∈ T.faces, ∃ b : Finset T.Vertex,
    b ⊆ t ∧ b.card ≤ 2 ∧
      ∀ x : T.realization, x ∈ T.toIntrinsic.faceCarrier t →
        (T.homeo x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary S ↔
          x ∈ T.toIntrinsic.faceCarrier b)

/-- Full-support conversion retains Radó's facewise boundary regularity. -/
theorem boundaryFacewiseRegular_toGeometricTriangulation
    (P : Moise.PartialTriangulation S)
    (hcovers : P.support = Set.univ)
    (hregular : P.BoundaryFacewiseRegular) :
    (P.toGeometricTriangulation hcovers).BoundaryFacewiseRegular := by
  intro t ht
  simpa [BoundaryFacewiseRegular, Moise.PartialTriangulation.toGeometricTriangulation]
    using hregular t ht

/-- Every point carried by a valence-one edge is an ambient manifold-boundary point. -/
theorem simplicialBoundaryLocus_subset_homeo_preimage_boundary
    (T : GeometricTriangulation S) (hregular : T.BoundaryFacewiseRegular) :
    T.SimplicialBoundaryLocus ⊆
      T.homeo ⁻¹' (modelWithCornersEuclideanHalfSpace 2).boundary S := by
  classical
  rintro x ⟨e, heBoundary, hxe⟩
  let t := T.toIntrinsic.edgeParent e
  have htF : t ∈ T.faces := T.toIntrinsic.edgeParent_mem e
  have het : e.1 ⊆ t := T.toIntrinsic.edge_subset_parent e
  obtain ⟨b, hbt, hbcard, hbregular⟩ := hregular t htF
  have hmidT : T.toIntrinsic.edgeMidpoint e ∈
      T.toIntrinsic.faceCarrier t := by
    apply (T.toIntrinsic.mem_faceCarrier_iff t _).mpr
    intro v hvt
    apply (T.toIntrinsic.mem_faceCarrier_iff e.1 _).mp ?_ v
    · exact fun hve => hvt (het hve)
    · rw [← T.toIntrinsic.range_edgePath e]
      exact ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩
  have hmidBoundary : T.homeo (T.toIntrinsic.edgeMidpoint e) ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S :=
    (T.isBoundaryPoint_homeo_edgeMidpoint_iff_isBoundaryEdge e).mpr heBoundary
  have hmidB : T.toIntrinsic.edgeMidpoint e ∈
      T.toIntrinsic.faceCarrier b :=
    (hbregular (T.toIntrinsic.edgeMidpoint e) hmidT).mp hmidBoundary
  have heb : e.1 ⊆ b := by
    rw [T.toIntrinsic.edge_eq_pair e]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    constructor
    · by_contra ha
      have hzero := (T.toIntrinsic.mem_faceCarrier_iff b
        (T.toIntrinsic.edgeMidpoint e)).mp hmidB
          (T.toIntrinsic.edgeFirst e) ha
      rw [T.toIntrinsic.edgeMidpoint_apply_first] at hzero
      norm_num at hzero
    · by_contra hb
      have hzero := (T.toIntrinsic.mem_faceCarrier_iff b
        (T.toIntrinsic.edgeMidpoint e)).mp hmidB
          (T.toIntrinsic.edgeSecond e) hb
      rw [T.toIntrinsic.edgeMidpoint_apply_second] at hzero
      norm_num at hzero
  have hbe : b = e.1 := by
    have hbcard' : b.card ≤ e.1.card := by
      rw [T.edge_card e]
      exact hbcard
    exact (Finset.eq_of_subset_of_card_le heb hbcard').symm
  apply (hbregular x ?_).mpr
  · rwa [hbe]
  · apply (T.toIntrinsic.mem_faceCarrier_iff t _).mpr
    intro v hvt
    apply (T.toIntrinsic.mem_faceCarrier_iff e.1 _).mp hxe v
    exact fun hve => hvt (het hve)

/-- A continuous injective circle has no isolated point in its range. -/
theorem preperfect_range_of_continuous_injective_circle
    {Y : Type*} [TopologicalSpace Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    Preperfect (Set.range curve) := by
  have hzeroHalf : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro h
    change ((0 : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) at h
    have hrealeq : (0 : ℝ) = 1 / 2 :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (a := (0 : ℝ)) (p := (1 : ℝ)) (by norm_num)
        (by norm_num)).mp h
    norm_num at hrealeq
  letI : Nontrivial UnitAddCircle :=
    ⟨⟨0, ((1 / 2 : ℝ) : UnitAddCircle), hzeroHalf⟩⟩
  rw [preperfect_iff_nhds]
  rintro _ ⟨x, rfl⟩ U hU
  have hpreimage : curve ⁻¹' U ∈ nhds x :=
    hcurve.continuousAt.preimage_mem_nhds hU
  have hunit : Preperfect (Set.univ : Set UnitAddCircle) :=
    PerfectSpace.univ_preperfect
  obtain ⟨y, hy, hyne⟩ :=
    (preperfect_iff_nhds.mp hunit) x (Set.mem_univ x)
        (curve ⁻¹' U) hpreimage
  exact ⟨curve y, ⟨hy.1, ⟨y, rfl⟩⟩, hinjective.ne hyne⟩

/-- If the ambient manifold boundary has no isolated points, every ambient boundary point of a
boundary-facewise-regular triangulation lies on a valence-one edge.

For a putative counterexample `y`, intersect the complements of all face carriers which do not
contain `y`.  Finiteness makes this an open neighborhood.  Any other boundary point in that
neighborhood lies with `y` in the exposed face of one triangle.  A two-vertex exposed face is a
valence-one edge; a smaller exposed face contains at most one realization point.  Both cases
contradict the choice of the second boundary point. -/
theorem homeo_preimage_boundary_subset_simplicialBoundaryLocus
    (T : GeometricTriangulation S) (hregular : T.BoundaryFacewiseRegular)
    (hpreperfect : Preperfect
      ((modelWithCornersEuclideanHalfSpace 2).boundary S)) :
    T.homeo ⁻¹' (modelWithCornersEuclideanHalfSpace 2).boundary S ⊆
      T.SimplicialBoundaryLocus := by
  classical
  intro y hyBoundary
  by_contra hyNotSimplicial
  have hyNoBoundaryEdge : ∀ e : T.Edge, T.IsBoundaryEdge e →
      y ∉ T.toIntrinsic.faceCarrier e.1 := by
    intro e heBoundary hye
    exact hyNotSimplicial ⟨e, heBoundary, hye⟩
  let U : Set T.realization :=
    ⋂ b : Finset T.Vertex,
      if y ∈ T.toIntrinsic.faceCarrier b then Set.univ
      else (T.toIntrinsic.faceCarrier b)ᶜ
  have hUOpen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro b
    split_ifs
    · exact isOpen_univ
    · exact (T.toIntrinsic.faceCarrier_closed b).isOpen_compl
  have hyU : y ∈ U := by
    change y ∈ ⋂ b : Finset T.Vertex,
      if y ∈ T.toIntrinsic.faceCarrier b then Set.univ
      else (T.toIntrinsic.faceCarrier b)ᶜ
    refine Set.mem_iInter.mpr fun b ↦ ?_
    by_cases hyb : y ∈ T.toIntrinsic.faceCarrier b
    · simp [hyb]
    · simp [hyb]
  have hImageOpen : IsOpen (T.homeo '' U) :=
    T.homeo.isOpenMap U hUOpen
  have hyImage : T.homeo y ∈ T.homeo '' U := ⟨y, hyU, rfl⟩
  obtain ⟨s, hsImageBoundary, hsne⟩ :=
    (preperfect_iff_nhds.mp hpreperfect) (T.homeo y) hyBoundary
      (T.homeo '' U) (hImageOpen.mem_nhds hyImage)
  rcases hsImageBoundary.1 with ⟨z, hzU, rfl⟩
  have hzBoundary : T.homeo z ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary S :=
    hsImageBoundary.2
  rcases z.2.2 with ⟨t, htF, hzt⟩
  obtain ⟨b, hbt, hbcard, hbregular⟩ := hregular t htF
  have hzb : z ∈ T.toIntrinsic.faceCarrier b :=
    (hbregular z hzt).mp hzBoundary
  have hyb : y ∈ T.toIntrinsic.faceCarrier b := by
    by_contra hyb
    have hzUb : z ∈
        (if y ∈ T.toIntrinsic.faceCarrier b then Set.univ
          else (T.toIntrinsic.faceCarrier b)ᶜ) := by
      apply Set.mem_iInter.mp hzU b
    simp [hyb] at hzUb
    exact hzUb hzb
  by_cases hbsmall : b.card ≤ 1
  · have hyz : y = z :=
      T.toIntrinsic.eq_of_mem_faceCarrier_of_card_le_one hbsmall hyb hzb
    exact hsne (congrArg T.homeo hyz.symm)
  · have hbcardTwo : b.card = 2 := by omega
    let e : T.Edge := ⟨b, T.mem_edges_of_subset_face htF hbt hbcardTwo⟩
    have hmidB : T.toIntrinsic.edgeMidpoint e ∈
        T.toIntrinsic.faceCarrier b := by
      change T.toIntrinsic.edgeMidpoint e ∈
        T.toIntrinsic.faceCarrier e.1
      rw [← T.toIntrinsic.range_edgePath e]
      exact ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩
    have hmidT : T.toIntrinsic.edgeMidpoint e ∈
        T.toIntrinsic.faceCarrier t := by
      apply (T.toIntrinsic.mem_faceCarrier_iff t _).mpr
      intro v hvt
      apply (T.toIntrinsic.mem_faceCarrier_iff b _).mp hmidB v
      exact fun hvb ↦ hvt (hbt hvb)
    have hmidBoundary : T.homeo (T.toIntrinsic.edgeMidpoint e) ∈
        (modelWithCornersEuclideanHalfSpace 2).boundary S :=
      (hbregular (T.toIntrinsic.edgeMidpoint e) hmidT).mpr hmidB
    have heBoundary : T.IsBoundaryEdge e :=
      (T.isBoundaryPoint_homeo_edgeMidpoint_iff_isBoundaryEdge e).mp
        hmidBoundary
    exact hyNoBoundaryEdge e heBoundary (by simpa [e] using hyb)

/-- In a boundary-facewise-regular triangulation whose ambient boundary has no isolated points,
the simplicial valence-one locus is exactly the pullback of the ambient manifold boundary. -/
theorem simplicialBoundaryLocus_eq_homeo_preimage_boundary
    (T : GeometricTriangulation S) (hregular : T.BoundaryFacewiseRegular)
    (hpreperfect : Preperfect
      ((modelWithCornersEuclideanHalfSpace 2).boundary S)) :
    T.SimplicialBoundaryLocus =
      T.homeo ⁻¹' (modelWithCornersEuclideanHalfSpace 2).boundary S :=
  Set.Subset.antisymm
    (T.simplicialBoundaryLocus_subset_homeo_preimage_boundary hregular)
    (T.homeo_preimage_boundary_subset_simplicialBoundaryLocus
      hregular hpreperfect)

/-- For an ambient boundary parametrized injectively by a circle, the simplicial valence-one
locus is exactly the ambient boundary under the triangulation homeomorphism. -/
theorem image_simplicialBoundaryLocus_eq_boundary_of_circle
    (T : GeometricTriangulation S) (hregular : T.BoundaryFacewiseRegular)
    (boundary : UnitAddCircle → S) (hboundary : Continuous boundary)
    (hinjective : Function.Injective boundary)
    (hrange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S) :
    T.homeo '' T.SimplicialBoundaryLocus =
      (modelWithCornersEuclideanHalfSpace 2).boundary S := by
  have hpreperfect : Preperfect
      ((modelWithCornersEuclideanHalfSpace 2).boundary S) := by
    rw [← hrange]
    exact preperfect_range_of_continuous_injective_circle
      boundary hboundary hinjective
  rw [T.simplicialBoundaryLocus_eq_homeo_preimage_boundary
    hregular hpreperfect]
  exact Set.image_preimage_eq _ T.homeo.surjective

end

end GeometricTriangulation

end LeanEval.Topology.ClassificationOfSurfaces
