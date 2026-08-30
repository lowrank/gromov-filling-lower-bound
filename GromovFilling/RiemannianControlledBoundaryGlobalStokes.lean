import GromovFilling.RiemannianControlledBoundaryAreaCancellation

/-!
# Global controlled-atlas weak Stokes

This file sums sign-weighted weak Stokes over a finite controlled boundary
atlas.  The partition-of-unity primitive errors cancel against canonical
Riemannian surface area, leaving only the signed sum of genuine boundary
chart actions.  Identifying that signed chart sum with one globally oriented
boundary parametrization is deliberately kept as the next geometric step.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

variable {M : Type uM} [PseudoEMetricSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Summing controlled-chart weak Stokes and cancelling the intrinsic
partition-of-unity primitive errors leaves exactly the negative signed sum
of the genuine imaginary-axis boundary actions. -/
theorem sum_integral_controlledBoundaryChartAreaSymplecticDensity_eq_neg_boundary
    [Nonempty M]
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P) (G : M → ι → ℂ)
    {CG : ℝ≥0} (hGLipschitz : LipschitzWith CG G) :
    (∑ i, ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
      -∑ i, O.chartSign i *
        ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  let D : ∀ i : P.ι, ControlledBoundaryChartWeakStokesData P i G :=
    fun i ↦ Classical.choice
      (nonempty_controlledBoundaryChartWeakStokesData P i G hGLipschitz)
  calc
    (∑ i, ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
      ∑ i, ((∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact
        (D i).integral_areaSymplecticDensity_eq_areaPrimitiveError_sub_signedBoundary_of_lipschitzWith
          O hGLipschitz
    _ = (∑ i, ∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        ∑ i, O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      rw [Finset.sum_sub_distrib]
    _ = 0 - ∑ i, O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      rw [sum_integral_controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero
        P O G hGLipschitz]
    _ = -∑ i, O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      rw [zero_sub]

#print axioms
  sum_integral_controlledBoundaryChartAreaSymplecticDensity_eq_neg_boundary

end

end GromovFilling
