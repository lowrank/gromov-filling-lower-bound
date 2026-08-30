import GromovFilling.RiemannianControlledBoundaryPartition
import GromovFilling.RiemannianInteriorAtlasArea

/-!
# Interior atlas carried by a controlled boundary partition

The controlled boundary partition already supplies finitely many quantitative
half-space chart centers whose interior pieces cover the whole manifold
interior.  This module reindexes those centers by a finite ordinal and feeds
them into the canonical controlled-interior-atlas constructor.  Consequently
the boundary Stokes cover and the canonical Riemannian area measure can use
the same chart family.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- The controlled interior atlas obtained by reindexing the centers of one
finite controlled boundary partition. -/
def FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas
    (P : FiniteControlledBoundaryChartPartition M) (fallback : M) :
    ControlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2) M := by
  let centers : Fin (Fintype.card P.ι) → M :=
    fun k ↦ P.center ((Fintype.equivFin P.ι).symm k)
  apply controlledInteriorAtlasOfFinCover
    (modelWithCornersEuclideanHalfSpace 2)
    Complex.orthonormalBasisOneI.repr centers fallback
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (P.interior_subset_iUnion_controlledInterior_image hx)
  refine Set.mem_iUnion.mpr ⟨Fintype.equivFin P.ι i, ?_⟩
  simpa only [centers, Equiv.symm_apply_apply] using hi

/-- The atlas chart indexed by the finite reindexing of a partition index is
the interior inverse chart at the same center. -/
@[simp] theorem FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_parametrization
    (P : FiniteControlledBoundaryChartPartition M) (fallback : M)
    (i : P.ι) :
    (P.toControlledInteriorAtlas fallback).parametrization
        (Fintype.equivFin P.ι i) =
      interiorComplexExtChart
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr (P.center i) := by
  simp [FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas,
    controlledInteriorAtlasOfFinCover,
    finControlledInteriorParametrization]

/-- The corresponding reindexed atlas domain is exactly the chosen
controlled interior coordinate domain at that center. -/
@[simp] theorem FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_domain
    (P : FiniteControlledBoundaryChartPartition M) (fallback : M)
    (i : P.ι) :
    (P.toControlledInteriorAtlas fallback).domain
        (Fintype.equivFin P.ι i) =
      chosenControlledInteriorComplexChartDomain
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr (P.center i) := by
  simp [FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas,
    controlledInteriorAtlasOfFinCover,
    finControlledInteriorDomain]

/-- In particular, every controlled boundary partition canonically supplies
a nonempty controlled atlas of the manifold interior. -/
theorem nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition
    (P : FiniteControlledBoundaryChartPartition M) (fallback : M) :
    Nonempty
      (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
  ⟨P.toControlledInteriorAtlas fallback⟩

#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas
#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_parametrization
#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_domain
#print axioms
  nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition

end

end GromovFilling
