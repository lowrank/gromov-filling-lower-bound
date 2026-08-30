import GromovFilling.RiemannianBoundaryPartition
import GromovFilling.RiemannianHalfSpaceChartControl

/-!
# Finite controlled boundary-chart partitions

The smooth boundary-chart partition used for localized Stokes can be chosen
subordinate to the same controlled inverse-chart neighborhoods that support the
Riemannian area estimates.  This module packages that common choice.  Thus one
finite family of centers simultaneously supplies compactly supported smooth
cutoffs, controlled half-space charts on the whole surface, and controlled
complex charts on the interior.
-/

open Bundle Function Manifold Set
open scoped BigOperators ContDiff Manifold

namespace GromovFilling

noncomputable section

universe uM

/-- A finite smooth partition of unity whose closed supports lie in the chosen
controlled inverse-chart neighborhoods. -/
structure FiniteControlledBoundaryChartPartition
    (M : Type uM) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)] where
  ι : Type uM
  fintype : Fintype ι
  center : ι → M
  partition : SmoothPartitionOfUnity ι
    (modelWithCornersEuclideanHalfSpace 2) M Set.univ
  controlledSubordinate : partition.IsSubordinate fun i ↦
    chosenControlledInteriorChartNeighborhood
      (modelWithCornersEuclideanHalfSpace 2) (center i)

instance {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    (P : FiniteControlledBoundaryChartPartition M) : Fintype P.ι :=
  P.fintype

/-- Forgetting the quantitative control recovers an ordinary finite boundary
chart partition. -/
def FiniteControlledBoundaryChartPartition.toFiniteBoundaryChartPartition
    {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    (P : FiniteControlledBoundaryChartPartition M) :
    FiniteBoundaryChartPartition M where
  ι := P.ι
  fintype := P.fintype
  center := P.center
  partition := P.partition
  subordinate i := by
    exact (P.controlledSubordinate i).trans fun _y hy ↦ hy.1

/-- Compactness turns a smooth bump covering subordinate to the chosen
controlled neighborhoods into a finite controlled boundary partition. -/
theorem nonempty_finiteControlledBoundaryChartPartition
    (M : Type uM) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [T2Space M] [CompactSpace M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)] :
    Nonempty (FiniteControlledBoundaryChartPartition M) := by
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate
    (modelWithCornersEuclideanHalfSpace 2) isClosed_univ
    (U := chosenControlledInteriorChartNeighborhood
      (modelWithCornersEuclideanHalfSpace 2))
    (fun x _hx ↦
      (isOpen_controlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2)
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) x)).mem_nhds
        (mem_controlledInteriorChartNeighborhood
          (modelWithCornersEuclideanHalfSpace 2)
          (chosenInteriorChartControl
            (modelWithCornersEuclideanHalfSpace 2) x)))
  letI : Fintype ι := f.fintype
  exact ⟨{
    ι := ι
    fintype := inferInstance
    center := f.c
    partition := f.toSmoothPartitionOfUnity
    controlledSubordinate := hf.toSmoothPartitionOfUnity
  }⟩

variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]

/-- The controlled cutoffs add to one at every point. -/
theorem FiniteControlledBoundaryChartPartition.sum_partition_eq_one
    (P : FiniteControlledBoundaryChartPartition M) (x : M) :
    ∑ i, P.partition i x = 1 := by
  simpa [FiniteControlledBoundaryChartPartition.toFiniteBoundaryChartPartition]
    using P.toFiniteBoundaryChartPartition.sum_partition_eq_one x

/-- Every controlled cutoff is nonnegative. -/
theorem FiniteControlledBoundaryChartPartition.partition_nonneg
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (x : M) :
    0 ≤ P.partition i x :=
  P.partition.nonneg i x

/-- Every controlled cutoff is infinitely manifold-smooth. -/
theorem FiniteControlledBoundaryChartPartition.contMDiff_partition
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    ContMDiff (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ) ∞
      (P.partition i) :=
  (P.partition i).contMDiff

/-- The closed support of a controlled cutoff lies in its chosen extended
chart source. -/
theorem FiniteControlledBoundaryChartPartition.tsupport_partition_subset_extChart_source
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    tsupport (P.partition i) ⊆
      (extChartAt (modelWithCornersEuclideanHalfSpace 2)
        (P.center i)).source :=
  P.toFiniteBoundaryChartPartition.tsupport_partition_subset_extChart_source i

/-- The closed support of a controlled cutoff lies in the corresponding
controlled complex half-space chart image. -/
theorem FiniteControlledBoundaryChartPartition.tsupport_partition_subset_controlledHalfSpace_image
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    tsupport (P.partition i) ⊆
      halfSpaceComplexExtChart (P.center i) ''
        chosenControlledHalfSpaceComplexChartDomain (P.center i) := by
  rw [chosenControlledHalfSpaceComplexChartDomain,
    image_controlledHalfSpaceComplexChartDomain]
  exact P.controlledSubordinate i

/-- On a compact surface every controlled cutoff has compact support. -/
theorem FiniteControlledBoundaryChartPartition.hasCompactSupport_partition
    [CompactSpace M] (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    HasCompactSupport (P.partition i) :=
  (isClosed_tsupport (P.partition i)).isCompact

/-- At every point, at least one controlled cutoff is nonzero. -/
theorem FiniteControlledBoundaryChartPartition.exists_partition_ne_zero
    (P : FiniteControlledBoundaryChartPartition M) (x : M) :
    ∃ i, P.partition i x ≠ 0 := by
  by_contra h
  have hall : ∀ i, P.partition i x = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hzero : (∑ i, P.partition i x) = 0 := by
    exact Finset.sum_eq_zero fun i _hi ↦ hall i
  exact zero_ne_one (hzero.symm.trans (P.sum_partition_eq_one x))

/-- The controlled centers cover the whole surface by their chosen ambient
chart neighborhoods. -/
theorem FiniteControlledBoundaryChartPartition.univ_subset_iUnion_controlledNeighborhood
    (P : FiniteControlledBoundaryChartPartition M) :
    (Set.univ : Set M) ⊆ ⋃ i,
      chosenControlledInteriorChartNeighborhood
        (modelWithCornersEuclideanHalfSpace 2) (P.center i) := by
  intro x _hx
  obtain ⟨i, hi⟩ := P.exists_partition_ne_zero x
  refine Set.mem_iUnion.mpr ⟨i, P.controlledSubordinate i ?_⟩
  exact subset_closure hi

/-- The same controlled centers cover the manifold interior by controlled
complex interior charts. -/
theorem FiniteControlledBoundaryChartPartition.interior_subset_iUnion_controlledInterior_image
    (P : FiniteControlledBoundaryChartPartition M) :
    (modelWithCornersEuclideanHalfSpace 2).interior M ⊆ ⋃ i,
      interiorComplexExtChart (modelWithCornersEuclideanHalfSpace 2)
          Complex.orthonormalBasisOneI.repr (P.center i) ''
        chosenControlledInteriorComplexChartDomain
          (modelWithCornersEuclideanHalfSpace 2)
          Complex.orthonormalBasisOneI.repr (P.center i) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp
    (P.univ_subset_iUnion_controlledNeighborhood (Set.mem_univ x))
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [chosenControlledInteriorComplexChartDomain,
    image_controlledInteriorComplexChartDomain]
  exact ⟨hxi, hx⟩

#print axioms nonempty_finiteControlledBoundaryChartPartition
#print axioms FiniteControlledBoundaryChartPartition.sum_partition_eq_one
#print axioms
  FiniteControlledBoundaryChartPartition.tsupport_partition_subset_controlledHalfSpace_image
#print axioms
  FiniteControlledBoundaryChartPartition.univ_subset_iUnion_controlledNeighborhood
#print axioms
  FiniteControlledBoundaryChartPartition.interior_subset_iUnion_controlledInterior_image

end

end GromovFilling
