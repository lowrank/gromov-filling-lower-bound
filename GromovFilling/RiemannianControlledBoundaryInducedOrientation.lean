import GromovFilling.RiemannianControlledBoundaryAxisLiftSpan
import GromovFilling.RiemannianControlledSurfaceOrientation

/-!
# Induced orientation on controlled boundary charts

The pinned manifold library has no orientation API for manifolds with
boundary.  `ControlledRiemannianSurfaceOrientation` therefore records the
interior chart signs explicitly.  This file records the remaining local
geometric meaning of the induced boundary orientation: on the imaginary
axis of a right-half-plane chart, a positive chart is traversed in the
decreasing real-lift direction, while a negative chart is traversed in the
increasing direction.

This datum contains no integral, winding, Stokes, or area conclusion.  It is
invariant under changing a real lift by an integer constant and is the
controlled-chart form of the usual outward-first boundary convention.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Compatibility of a controlled surface orientation with the boundary
orientation induced by the outward-first convention.  The condition is
stated for every finite controlled partition so that it is independent of
the auxiliary partition later chosen for Stokes. -/
structure ControlledRiemannianInducedBoundaryOrientation
    (R : ControlledRiemannianSurfaceOrientation M)
    (boundary : UnitAddCircle → M) : Prop where
  chart_lift_orientation :
    ∀ (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
      (a b : ℝ) (lift : ℝ → ℝ),
      a < b →
      (∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
        chosenControlledHalfSpaceComplexChartDomain (P.center i)) →
      Continuous lift →
      (∀ y ∈ Set.Icc a b,
        ((lift y : ℝ) : UnitAddCircle) =
          controlledBoundaryChartParameter boundary P i y) →
      (R.chartSign (P.center i) = 1 ∧
          StrictAntiOn lift (Set.Icc a b)) ∨
        (R.chartSign (P.center i) = -1 ∧
          StrictMonoOn lift (Set.Icc a b))

#print axioms ControlledRiemannianInducedBoundaryOrientation

end

end GromovFilling
