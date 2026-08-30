import Mathlib.Geometry.Manifold.PartitionOfUnity
import GromovFilling.RiemannianHalfSpaceChart

/-!
# Finite smooth boundary-chart partitions

On a compact smooth surface with boundary, Mathlib's locally finite smooth
bump covering has a finite index type.  This module packages the resulting
partition of unity together with one extended half-space chart per cutoff.
It also records the finite derivative cancellation used to eliminate the
localized symplectic primitive errors after chartwise Stokes.
-/

open Bundle Function Manifold Set
open scoped BigOperators ContDiff Manifold

namespace GromovFilling

noncomputable section

universe uM

/-- A finite smooth partition of unity on a compact surface with boundary,
with the closed support of each cutoff contained in the source of its chosen
extended chart. -/
structure FiniteBoundaryChartPartition
    (M : Type uM) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] where
  ι : Type uM
  fintype : Fintype ι
  center : ι → M
  partition : SmoothPartitionOfUnity ι
    (modelWithCornersEuclideanHalfSpace 2) M Set.univ
  subordinate : partition.IsSubordinate fun i ↦
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) (center i)).source

instance {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    (P : FiniteBoundaryChartPartition M) : Fintype P.ι :=
  P.fintype

/-- Compactness turns a subordinate smooth bump covering into a finite
boundary-chart partition. -/
theorem nonempty_finiteBoundaryChartPartition
    (M : Type uM) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [T2Space M] [CompactSpace M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M] :
    Nonempty (FiniteBoundaryChartPartition M) := by
  obtain ⟨ι, f, hf⟩ := SmoothBumpCovering.exists_isSubordinate
    (modelWithCornersEuclideanHalfSpace 2) isClosed_univ
    (U := fun x : M ↦
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).source)
    (fun x _hx ↦ extChartAt_source_mem_nhds x)
  letI : Fintype ι := f.fintype
  exact ⟨{
    ι := ι
    fintype := inferInstance
    center := f.c
    partition := f.toSmoothPartitionOfUnity
    subordinate := hf.toSmoothPartitionOfUnity
  }⟩

variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]

/-- The finite cutoffs add to one at every point. -/
theorem FiniteBoundaryChartPartition.sum_partition_eq_one
    (P : FiniteBoundaryChartPartition M) (x : M) :
    ∑ i, P.partition i x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using
    P.partition.sum_eq_one (Set.mem_univ x)

/-- Every cutoff is nonnegative. -/
theorem FiniteBoundaryChartPartition.partition_nonneg
    (P : FiniteBoundaryChartPartition M) (i : P.ι) (x : M) :
    0 ≤ P.partition i x :=
  P.partition.nonneg i x

/-- Each cutoff is infinitely manifold-smooth. -/
theorem FiniteBoundaryChartPartition.contMDiff_partition
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    (P : FiniteBoundaryChartPartition M) (i : P.ι) :
    ContMDiff (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ) ∞
      (P.partition i) :=
  (P.partition i).contMDiff

/-- The closed support of each cutoff lies in its chosen extended chart. -/
theorem FiniteBoundaryChartPartition.tsupport_partition_subset_extChart_source
    (P : FiniteBoundaryChartPartition M) (i : P.ι) :
    tsupport (P.partition i) ⊆
      (extChartAt (modelWithCornersEuclideanHalfSpace 2)
        (P.center i)).source :=
  P.subordinate i

/-- Equivalently, the closed support lies in the image of the chosen inverse
half-space chart in complex coordinates. -/
theorem FiniteBoundaryChartPartition.tsupport_partition_subset_halfSpaceChart_image
    (P : FiniteBoundaryChartPartition M) (i : P.ι) :
    tsupport (P.partition i) ⊆
      halfSpaceComplexExtChart (P.center i) ''
        halfSpaceComplexExtChartDomain (P.center i) := by
  rw [image_halfSpaceComplexExtChartDomain]
  exact P.subordinate i

/-- On a compact surface every cutoff has compact support. -/
theorem FiniteBoundaryChartPartition.hasCompactSupport_partition
    [CompactSpace M] (P : FiniteBoundaryChartPartition M) (i : P.ι) :
    HasCompactSupport (P.partition i) :=
  (isClosed_tsupport (P.partition i)).isCompact

/-- The derivative of a finite family of differentiable cutoffs adds to zero
whenever the cutoffs add pointwise to one.  This is the exact cancellation
used for the localized symplectic primitive-error terms. -/
theorem sum_fderiv_eq_zero_of_sum_eq_one
    {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ι → E → ℝ) (x : E)
    (hρ : ∀ i, DifferentiableAt ℝ (ρ i) x)
    (hsum : ∀ y, ∑ i, ρ i y = 1) :
    ∑ i, fderiv ℝ (ρ i) x = 0 := by
  rw [← fderiv_fun_sum (u := Finset.univ)
    (fun i _hi ↦ hρ i)]
  have hfun : (fun y ↦ ∑ i, ρ i y) = fun _y : E ↦ (1 : ℝ) := by
    funext y
    exact hsum y
  rw [hfun]
  exact (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).fderiv

end

end GromovFilling

#print axioms GromovFilling.nonempty_finiteBoundaryChartPartition
#print axioms GromovFilling.FiniteBoundaryChartPartition.sum_partition_eq_one
#print axioms
  GromovFilling.FiniteBoundaryChartPartition.tsupport_partition_subset_halfSpaceChart_image
#print axioms GromovFilling.sum_fderiv_eq_zero_of_sum_eq_one
