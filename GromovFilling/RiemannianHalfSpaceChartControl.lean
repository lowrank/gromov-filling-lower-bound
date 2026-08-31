import GromovFilling.RiemannianHalfSpaceChart

/-!
# Controlled complex half-space charts

The quantitative inverse-chart data used for interior area estimates also
controls the full model half-ball, including its boundary face.  This module
packages that observation in the standard complex coordinates for a
two-dimensional manifold with boundary.  The resulting inverse charts are
Lipschitz on controlled half-space domains, and compactness supplies a finite
cover of the whole manifold by their images.
-/

open Bundle Function Manifold Metric Set
open scoped Manifold NNReal Topology

namespace GromovFilling

noncomputable section

/-- The controlled model half-ball associated with inverse-chart derivative
control at a point of a two-dimensional manifold with boundary. -/
def controlledHalfSpaceChartSet
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ball
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x)
      c.r ∩
    range (modelWithCornersEuclideanHalfSpace 2)

/-- A controlled model half-ball lies in the inverse extended-chart target. -/
theorem controlledHalfSpaceChartSet_subset_target
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    controlledHalfSpaceChartSet c ⊆
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target := by
  intro y hy
  exact (c.controlled hy).1

/-- The controlled model half-ball is convex. -/
theorem convex_controlledHalfSpaceChartSet
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    Convex ℝ (controlledHalfSpaceChartSet c) :=
  (convex_ball _ _).inter
    (modelWithCornersEuclideanHalfSpace 2).convex_range

/-- The controlled half-space chart domain in standard complex coordinates. -/
def controlledHalfSpaceComplexChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    Set ℂ :=
  Complex.orthonormalBasisOneI.repr ⁻¹'
    controlledHalfSpaceChartSet c

/-- A controlled half-space domain lies in the full complex extended-chart
domain. -/
theorem controlledHalfSpaceComplexChartDomain_subset_domain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    controlledHalfSpaceComplexChartDomain c ⊆
      halfSpaceComplexExtChartDomain x := by
  intro z hz
  exact controlledHalfSpaceChartSet_subset_target c hz

/-- Every controlled half-space coordinate has nonnegative real part. -/
theorem controlledHalfSpaceComplexChartDomain_subset_rightClosedHalfPlane
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    controlledHalfSpaceComplexChartDomain c ⊆
      complexRightClosedHalfPlane :=
  (controlledHalfSpaceComplexChartDomain_subset_domain c).trans
    (halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane x)

/-- The controlled inverse half-space chart is Lipschitz on its full model
half-ball, with the constant stored in the inverse-chart control data. -/
theorem lipschitzOnWith_controlledHalfSpaceComplexChart
    {M : Type*} [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun y : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) y)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    LipschitzOnWith c.C (halfSpaceComplexExtChart x)
      (controlledHalfSpaceComplexChartDomain c) := by
  change LipschitzOnWith c.C
    (interiorComplexExtChart (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr x)
    (Complex.orthonormalBasisOneI.repr ⁻¹'
      controlledHalfSpaceChartSet c)
  apply lipschitzOnWith_interiorComplexExtChart_of_convex
    (modelWithCornersEuclideanHalfSpace 2)
    Complex.orthonormalBasisOneI.repr x
    (controlledHalfSpaceChartSet c)
    (convex_controlledHalfSpaceChartSet c)
    (controlledHalfSpaceChartSet_subset_target c)
  intro y hy
  exact (c.controlled hy).2.le

/-- The image of a controlled complex half-space domain is exactly the
ambient controlled chart neighborhood, including its boundary points. -/
theorem image_controlledHalfSpaceComplexChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    {x : M}
    (c : InteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) :
    halfSpaceComplexExtChart x ''
        controlledHalfSpaceComplexChartDomain c =
      controlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2) c := by
  rw [halfSpaceComplexExtChart,
    controlledHalfSpaceComplexChartDomain, Set.image_comp,
    Set.image_preimage_eq _
      Complex.orthonormalBasisOneI.repr.surjective]
  rw [(extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm_image_eq_source_inter_preimage
    (controlledHalfSpaceChartSet_subset_target c)]
  ext y
  simp only [controlledHalfSpaceChartSet,
    controlledInteriorChartNeighborhood, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hsource, hball, _hrange⟩
    exact ⟨hsource, hball⟩
  · rintro ⟨hsource, hball⟩
    refine ⟨hsource, hball, ?_⟩
    exact extChartAt_target_subset_range x
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) x).map_source
        hsource)

/-- A canonical controlled half-space coordinate domain at each point. -/
def chosenControlledHalfSpaceComplexChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun y : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) y)]
    (x : M) : Set ℂ :=
  controlledHalfSpaceComplexChartDomain
    (chosenInteriorChartControl
      (modelWithCornersEuclideanHalfSpace 2) x)

/-- The canonical controlled interior coordinate domain is contained in the
corresponding controlled half-space domain.  The only additional condition in
the interior domain is membership in the interior of the model range. -/
theorem chosenControlledInteriorComplexChartDomain_subset_chosenControlledHalfSpaceComplexChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) y)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun y : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) y)]
    (x : M) :
    chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr x ⊆
      chosenControlledHalfSpaceComplexChartDomain x := by
  intro z hz
  change Complex.orthonormalBasisOneI.repr z ∈
    ball (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x)
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x).r ∩
      interior (Set.range (modelWithCornersEuclideanHalfSpace 2)) at hz
  change Complex.orthonormalBasisOneI.repr z ∈
    ball (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x)
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x).r ∩
      Set.range (modelWithCornersEuclideanHalfSpace 2)
  exact ⟨hz.1, interior_subset hz.2⟩

/-- Compactness selects finitely many controlled half-space inverse charts
whose images cover the entire manifold, boundary included. -/
theorem exists_fin_controlledHalfSpaceComplexExtChart_cover
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun y : M ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) y)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun y : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) y)]
    [CompactSpace M] :
    ∃ n : ℕ, ∃ centers : Fin n → M,
      (Set.univ : Set M) ⊆ ⋃ i,
        halfSpaceComplexExtChart (centers i) ''
          chosenControlledHalfSpaceComplexChartDomain (centers i) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Finset M,
      (Set.univ : Set M) ⊆
        ⋃ x ∈ t, chosenControlledInteriorChartNeighborhood
          (modelWithCornersEuclideanHalfSpace 2) x := by
    refine isCompact_univ.elim_finite_subcover
      (chosenControlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2))
      (fun x ↦ isOpen_controlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2)
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) x)) ?_
    intro x _hx
    exact Set.mem_iUnion.mpr ⟨x,
      mem_controlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2)
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) x)⟩
  refine ⟨t.card, fun j ↦ t.equivFin.symm j, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  rw [chosenControlledHalfSpaceComplexChartDomain,
    image_controlledHalfSpaceComplexChartDomain]
  have hcenter :
      ((t.equivFin.symm (t.equivFin ⟨x, hxt⟩) : t) : M) = x :=
    congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨x, hxt⟩)
  change y ∈ chosenControlledInteriorChartNeighborhood
    (modelWithCornersEuclideanHalfSpace 2)
      ((t.equivFin.symm (t.equivFin ⟨x, hxt⟩) : t) : M)
  rw [hcenter]
  exact hyx

#print axioms controlledHalfSpaceChartSet_subset_target
#print axioms convex_controlledHalfSpaceChartSet
#print axioms controlledHalfSpaceComplexChartDomain_subset_domain
#print axioms
  controlledHalfSpaceComplexChartDomain_subset_rightClosedHalfPlane
#print axioms
  chosenControlledInteriorComplexChartDomain_subset_chosenControlledHalfSpaceComplexChartDomain
#print axioms lipschitzOnWith_controlledHalfSpaceComplexChart
#print axioms image_controlledHalfSpaceComplexChartDomain
#print axioms exists_fin_controlledHalfSpaceComplexExtChart_cover

end

end GromovFilling
