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

open Bundle Manifold MeasureTheory Set
open scoped Bundle Manifold NNReal

namespace GromovFilling

noncomputable section

universe uM uι

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

/-- A globally Lipschitz finite complex map is coordinatewise manifold
differentiable almost everywhere on each controlled interior domain carried
by a boundary partition. -/
theorem FiniteControlledBoundaryChartPartition.ae_mdifferentiableAt_comp_halfSpace_of_lipschitzWith
    (P : FiniteControlledBoundaryChartPartition M) (fallback : M)
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type uι} [Fintype ι] (G : M → ι → ℂ)
    {CG : ℝ≥0} (hG : LipschitzWith CG G) (i : P.ι) :
    ∀ᵐ z ∂volume.restrict
        (chosenControlledInteriorComplexChartDomain
          (modelWithCornersEuclideanHalfSpace 2)
          Complex.orthonormalBasisOneI.repr (P.center i)),
      ∀ j : ι, MDifferentiableAt
        (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
        (fun x ↦ G x j)
        (halfSpaceComplexExtChart (P.center i) z) := by
  let A : ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M :=
    P.toControlledInteriorAtlas fallback
  let k : ℕ := (Fintype.equivFin P.ι i : Fin (Fintype.card P.ι))
  rw [ae_all_iff]
  intro j
  have hGj : LipschitzWith CG (fun x ↦ G x j) := by
    simpa only [Function.comp_apply, one_mul] using
      ((LipschitzWith.eval j).comp hG)
  simpa only [A, k,
    FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_parametrization,
    FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_domain,
    halfSpaceComplexExtChart, interiorComplexExtChart] using
    (A.ae_mdifferentiableAt_of_lipschitzWith_on_domain
      (modelWithCornersEuclideanHalfSpace 2) (fun x ↦ G x j) hGj k)

#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas
#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_parametrization
#print axioms
  FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_domain
#print axioms
  nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition
#print axioms
  FiniteControlledBoundaryChartPartition.ae_mdifferentiableAt_comp_halfSpace_of_lipschitzWith

end

end GromovFilling
