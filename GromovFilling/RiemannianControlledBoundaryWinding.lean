import GromovFilling.RiemannianControlledBoundaryResonantAction

/-!
# Global boundary winding from local oriented chart changes of variables

The resonant-action layer needs one global signed winding identity.  This file
separates that identity from the local geometric input: each controlled chart
supplies a phase lift and the induced-boundary change-of-variables formula for
its partition function.  Finite additivity and the partition-of-unity theorem
then force the global winding to be `-2π`.

The remaining geometric obligation is deliberately local: construct these
change-of-variables identities from a conventional surface orientation and
its induced boundary orientation.
-/

open Bundle Filter Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance controlledBoundaryWindingEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Local phase lifts together with the chartwise change-of-variables identity
expressing the induced boundary orientation.  Unlike
`ControlledBoundaryAtlasBoundaryPhase`, this datum contains no global winding
claim. -/
structure ControlledBoundaryAtlasBoundaryPhaseLocalData
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P)
    (boundary : UnitAddCircle → M) where
  phase : P.ι → ℝ → ℝ
  phaseVelocity : P.ι → ℝ → ℝ
  hasDerivAt_phase_of_cutoff_ne_zero :
    ∀ i (y : ℝ), controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0 →
      HasDerivAt (phase i) (phaseVelocity i y) y
  chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero :
    ∀ i (y : ℝ), controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0 →
      (fun t : ℝ ↦
          halfSpaceComplexExtChart (P.center i) (t * Complex.I)) =ᶠ[nhds y]
        fun t : ℝ ↦ boundary (angleToUnitAddCircle (phase i t))
  chart_signed_winding_eq_boundary_partition :
    ∀ i, O.chartSign i *
        (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          phaseVelocity i y) =
      -(∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t)))

/-- Summing the local induced-boundary change-of-variables identities and
using that the controlled partition adds to one gives total winding `-2π`. -/
theorem ControlledBoundaryAtlasBoundaryPhaseLocalData.signed_weighted_winding
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (L : ControlledBoundaryAtlasBoundaryPhaseLocalData P O boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    (∑ i, O.chartSign i *
      ∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
        L.phaseVelocity i y) = -(2 * Real.pi) := by
  have hparameter :
      Continuous (fun t : ℝ ↦ boundary (angleToUnitAddCircle t)) :=
    hboundary.lipschitzWith.continuous.comp
      angleToUnitAddCircle_lipschitzWith.continuous
  have hintegrable (i : P.ι) :
      IntervalIntegrable
        (fun t : ℝ ↦ P.partition i (boundary (angleToUnitAddCircle t)))
        volume (-Real.pi) Real.pi := by
    exact ((P.contMDiff_partition i).continuous.comp hparameter).intervalIntegrable _ _
  have hsum :
      (∑ i, ∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t))) =
        ∫ t in -Real.pi..Real.pi,
          ∑ i, P.partition i (boundary (angleToUnitAddCircle t)) := by
    symm
    rw [intervalIntegral.integral_finset_sum]
    intro i _hi
    exact hintegrable i
  have hone :
      (∫ t in -Real.pi..Real.pi,
        ∑ i, P.partition i (boundary (angleToUnitAddCircle t))) =
        ∫ _t in -Real.pi..Real.pi, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact P.sum_partition_eq_one (boundary (angleToUnitAddCircle t))
  calc
    (∑ i, O.chartSign i *
      ∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
        L.phaseVelocity i y) =
        ∑ i, -(∫ t in -Real.pi..Real.pi,
          P.partition i (boundary (angleToUnitAddCircle t))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact L.chart_signed_winding_eq_boundary_partition i
    _ = -(∑ i, ∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t))) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ t in -Real.pi..Real.pi,
        ∑ i, P.partition i (boundary (angleToUnitAddCircle t))) := by
      rw [hsum]
    _ = -(∫ _t in -Real.pi..Real.pi, (1 : ℝ)) := by
      rw [hone]
    _ = -(2 * Real.pi) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
      ring

/-- Local phase data satisfying induced-boundary change of variables supplies
the global phase datum required by resonant Stokes. -/
def ControlledBoundaryAtlasBoundaryPhaseLocalData.toBoundaryPhase
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (L : ControlledBoundaryAtlasBoundaryPhaseLocalData P O boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ControlledBoundaryAtlasBoundaryPhase P O boundary where
  phase := L.phase
  phaseVelocity := L.phaseVelocity
  hasDerivAt_phase_of_cutoff_ne_zero :=
    L.hasDerivAt_phase_of_cutoff_ne_zero
  chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero :=
    L.chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero
  signed_weighted_winding := L.signed_weighted_winding hboundary

#print axioms ControlledBoundaryAtlasBoundaryPhaseLocalData
#print axioms
  ControlledBoundaryAtlasBoundaryPhaseLocalData.signed_weighted_winding
#print axioms ControlledBoundaryAtlasBoundaryPhaseLocalData.toBoundaryPhase

end

end GromovFilling
