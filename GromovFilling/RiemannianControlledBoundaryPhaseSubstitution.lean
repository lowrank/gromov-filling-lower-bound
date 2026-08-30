import GromovFilling.RiemannianControlledBoundaryWinding
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Boundary winding from pointwise chart substitutions

The local-to-global winding theorem only needs a chartwise change-of-variables
identity.  This file derives that identity from strictly more primitive data:
a compact phase interval, a differentiable real phase, its oriented endpoints,
and pointwise agreement of the chart cutoff with the boundary partition pulled
back by that phase.  Thus no integral or winding conclusion is stored in the
geometric substitution datum.

Constructing these pointwise substitutions from an ordinary surface
orientation and its induced boundary orientation remains the geometric step.
-/

open Bundle Filter Function Manifold MeasureTheory Set
open scoped Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance controlledBoundaryPhaseSubstitutionEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Pointwise boundary reparametrizations for every chart of one oriented
controlled atlas.  The phase interval runs from `chartSign * π` to its
negative; this is precisely the outward-first boundary convention for a
right-half-plane chart. -/
structure ControlledBoundaryAtlasBoundaryPhaseSubstitutionData
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P)
    (boundary : UnitAddCircle → M) where
  lower : P.ι → ℝ
  upper : P.ι → ℝ
  lower_lt_upper : ∀ i, lower i < upper i
  phase : P.ι → ℝ → ℝ
  phaseVelocity : P.ι → ℝ → ℝ
  hasDerivAt_phase :
    ∀ i y, y ∈ Icc (lower i) (upper i) →
      HasDerivAt (phase i) (phaseVelocity i y) y
  continuousOn_phaseVelocity :
    ∀ i, ContinuousOn (phaseVelocity i) (Icc (lower i) (upper i))
  support_cutoff_subset :
    ∀ i, support (fun y : ℝ ↦
      controlledBoundaryChartCutoff P i (y * Complex.I)) ⊆
        Ioc (lower i) (upper i)
  cutoff_eq_boundary_partition_on :
    ∀ i y, y ∈ Icc (lower i) (upper i) →
      controlledBoundaryChartCutoff P i (y * Complex.I) =
        P.partition i (boundary (angleToUnitAddCircle (phase i y)))
  chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero :
    ∀ i (y : ℝ), controlledBoundaryChartCutoff P i
        (y * Complex.I) ≠ 0 →
      (fun t : ℝ ↦
          halfSpaceComplexExtChart (P.center i) (t * Complex.I)) =ᶠ[nhds y]
        fun t : ℝ ↦ boundary (angleToUnitAddCircle (phase i t))
  phase_lower :
    ∀ i, phase i (lower i) = O.chartSign i * Real.pi
  phase_upper :
    ∀ i, phase i (upper i) = -(O.chartSign i * Real.pi)

/-- Pointwise phase substitution and the endpoint orientation imply the
chartwise induced-boundary change-of-variables identity. -/
theorem ControlledBoundaryAtlasBoundaryPhaseSubstitutionData.chart_signed_winding_eq_boundary_partition
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (S : ControlledBoundaryAtlasBoundaryPhaseSubstitutionData P O boundary)
    (hboundary : IsometricCircleBoundary boundary) (i : P.ι) :
    O.chartSign i *
        (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          S.phaseVelocity i y) =
      -(∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t))) := by
  let f : ℝ → ℝ := fun t ↦
    P.partition i (boundary (angleToUnitAddCircle t))
  let g : ℝ → ℝ := fun y ↦
    controlledBoundaryChartCutoff P i (y * Complex.I) *
      S.phaseVelocity i y
  have hf : Continuous f := by
    exact (P.contMDiff_partition i).continuous.comp
      (hboundary.lipschitzWith.continuous.comp
        continuous_angleToUnitAddCircle)
  have hgSupport : support g ⊆ Ioc (S.lower i) (S.upper i) := by
    intro y hy
    have hyCutoff :
        controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0 := by
      intro hyZero
      apply hy
      simp only [g, hyZero, zero_mul]
    exact S.support_cutoff_subset i hyCutoff
  have hglobal :
      (∫ y : ℝ, g y) = ∫ y in S.lower i..S.upper i, g y :=
    (intervalIntegral.integral_eq_integral_of_support_subset
      hgSupport).symm
  have hpointwise :
      (∫ y in S.lower i..S.upper i, g y) =
        ∫ y in S.lower i..S.upper i,
          (f ∘ S.phase i) y * S.phaseVelocity i y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (S.lower i) (S.upper i) := by
      simpa [Set.uIcc_of_le (S.lower_lt_upper i).le] using hy
    simp only [g, f, Function.comp_apply]
    rw [S.cutoff_eq_boundary_partition_on i y hyIcc]
  have hsubstitution :
      (∫ y in S.lower i..S.upper i,
          (f ∘ S.phase i) y * S.phaseVelocity i y) =
        ∫ t in S.phase i (S.lower i)..S.phase i (S.upper i), f t := by
    apply intervalIntegral.integral_comp_mul_deriv
    · intro y hy
      apply S.hasDerivAt_phase i y
      simpa [Set.uIcc_of_le (S.lower_lt_upper i).le] using hy
    · simpa [Set.uIcc_of_le (S.lower_lt_upper i).le] using
        S.continuousOn_phaseVelocity i
    · exact hf
  calc
    O.chartSign i *
        (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          S.phaseVelocity i y) =
        O.chartSign i * ∫ y : ℝ, g y := by rfl
    _ = O.chartSign i *
        ∫ y in S.lower i..S.upper i, g y := by rw [hglobal]
    _ = O.chartSign i *
        ∫ y in S.lower i..S.upper i,
          (f ∘ S.phase i) y * S.phaseVelocity i y := by rw [hpointwise]
    _ = O.chartSign i *
        ∫ t in S.phase i (S.lower i)..S.phase i (S.upper i), f t := by
      rw [hsubstitution]
    _ = -(∫ t in -Real.pi..Real.pi, f t) := by
      rw [S.phase_lower i, S.phase_upper i]
      rcases O.chartSign_eq_one_or_neg_one i with hi | hi
      · rw [hi]
        simp only [one_mul]
        rw [intervalIntegral.integral_symm]
      · rw [hi]
        simp only [neg_one_mul, neg_neg]
    _ = -(∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t))) := by rfl

/-- Pointwise chart substitutions supply the local phase datum used by the
finite-additivity winding theorem. -/
def ControlledBoundaryAtlasBoundaryPhaseSubstitutionData.toLocalData
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (S : ControlledBoundaryAtlasBoundaryPhaseSubstitutionData P O boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ControlledBoundaryAtlasBoundaryPhaseLocalData P O boundary where
  phase := S.phase
  phaseVelocity := S.phaseVelocity
  hasDerivAt_phase_of_cutoff_ne_zero i y hy := by
    apply S.hasDerivAt_phase i y
    have hyInterval := S.support_cutoff_subset i hy
    exact ⟨hyInterval.1.le, hyInterval.2⟩
  chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero :=
    S.chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero
  chart_signed_winding_eq_boundary_partition i :=
    S.chart_signed_winding_eq_boundary_partition hboundary i

#print axioms ControlledBoundaryAtlasBoundaryPhaseSubstitutionData
#print axioms
  ControlledBoundaryAtlasBoundaryPhaseSubstitutionData.chart_signed_winding_eq_boundary_partition
#print axioms ControlledBoundaryAtlasBoundaryPhaseSubstitutionData.toLocalData

end

end GromovFilling
