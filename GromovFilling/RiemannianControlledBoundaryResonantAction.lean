import GromovFilling.RiemannianControlledBoundaryGlobalStokes

/-!
# Resonant action from an oriented controlled boundary atlas

The global controlled-chart Stokes theorem leaves a signed finite sum of
imaginary-axis actions.  This file isolates the target-independent geometric
datum needed to identify that sum with the prescribed oriented boundary
circle.  Each chart axis has a real angular lift on the support of its
cutoff, and the signed cutoff-weighted angular velocities have total winding
`-2π`.  The sign is the boundary convention for a positively oriented right
half-plane chart.

For the finite resonant Fourier map, the primitive density along the explicit
boundary loop is constant.  Consequently the geometric winding identity is
enough to glue all local chart actions into the genuine finite resonant
boundary action.  No symplectic or Stokes identity is included in the
geometric datum itself.
-/

open Bundle Filter Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance controlledBoundaryResonantActionEuclideanFinrankTwo :
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

/-- Boundary-phase compatibility for an oriented controlled atlas.  The
angular lift is required only through its germ and derivative where the
corresponding cutoff is nonzero.  The final field is the target-independent
degree-one winding identity supplied by the induced boundary orientation. -/
structure ControlledBoundaryAtlasBoundaryPhase
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
  signed_weighted_winding :
    (∑ i, O.chartSign i *
      ∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
        phaseVelocity i y) = -(2 * Real.pi)

/-- Differentiating the explicit resonant boundary loop after a real angular
phase gives the phase velocity times the displayed resonant velocity. -/
theorem finiteComplexWeakLineDerivative_finiteResonantBoundaryCurve_comp
    (N : ℕ) (lam : ℝ) {phase : ℝ → ℝ} {phaseVelocity y : ℝ}
    (hphase : HasDerivAt phase phaseVelocity y) :
    finiteComplexWeakLineDerivative
        (fun t : ℝ ↦ finiteResonantBoundaryCurve N lam (phase t)) y 1 =
      phaseVelocity • finiteResonantBoundaryVelocity N lam (phase y) := by
  have hcomp : HasDerivAt
      (finiteResonantBoundaryCurve N lam ∘ phase)
      (phaseVelocity • finiteResonantBoundaryVelocity N lam (phase y)) y :=
    (hasDerivAt_finiteResonantBoundaryCurve N lam (phase y)).scomp y hphase
  change finiteComplexWeakLineDerivative
      (finiteResonantBoundaryCurve N lam ∘ phase) y 1 = _
  rw [finiteComplexWeakLineDerivative_eq_lineDeriv _
    hcomp.differentiableAt]
  have hline :=
    (hcomp.hasFDerivAt.hasLineDerivAt (1 : ℝ)).lineDeriv
  simpa only [Function.comp_apply, one_smul] using hline

/-- On the nonzero-cutoff germ of a boundary chart, the finite resonant
surface trace is the explicit resonant loop evaluated at the chart phase. -/
theorem ControlledBoundaryAtlasBoundaryPhase.finiteResonantProfileMap_chartAxis_eventuallyEq_curve
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) (i : P.ι) {y : ℝ}
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    (fun t : ℝ ↦
        finiteResonantProfileMap boundary N lam
          (halfSpaceComplexExtChart (P.center i) (t * Complex.I))) =ᶠ[nhds y]
      fun t : ℝ ↦ finiteResonantBoundaryCurve N lam (B.phase i t) := by
  filter_upwards
      [B.chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero i y hyCutoff]
      with t ht
  rw [ht, finiteResonantProfileMap_boundary_eq_curve
    hboundary N lam (B.phase i t)]

/-- A chart-local resonant action density is its cutoff-weighted phase
velocity times the constant primitive density of the resonant loop. -/
theorem ControlledBoundaryAtlasBoundaryPhase.controlledBoundaryChartActionDensity_finiteResonantProfileMap
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) (i : P.ι) (y : ℝ) :
    controlledBoundaryChartActionDensity P i
        (finiteResonantProfileMap boundary N lam) y =
      (controlledBoundaryChartCutoff P i (y * Complex.I) *
          B.phaseVelocity i y) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
  by_cases hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) = 0
  · simp [controlledBoundaryChartActionDensity, hyCutoff]
  · have htrace :=
      B.finiteResonantProfileMap_chartAxis_eventuallyEq_curve
        hboundary N lam i hyCutoff
    have hvalue := htrace.self_of_nhds
    have hderiv :
        finiteComplexWeakLineDerivative
            (fun t : ℝ ↦
              finiteResonantProfileMap boundary N lam
                (halfSpaceComplexExtChart (P.center i)
                  (t * Complex.I))) y 1 =
          B.phaseVelocity i y •
            finiteResonantBoundaryVelocity N lam (B.phase i y) := by
      calc
        finiteComplexWeakLineDerivative
            (fun t : ℝ ↦
              finiteResonantProfileMap boundary N lam
                (halfSpaceComplexExtChart (P.center i)
                  (t * Complex.I))) y 1 =
            finiteComplexWeakLineDerivative
              (fun t : ℝ ↦
                finiteResonantBoundaryCurve N lam (B.phase i t)) y 1 :=
          finiteComplexWeakLineDerivative_eq_of_eventuallyEq htrace
        _ = B.phaseVelocity i y •
              finiteResonantBoundaryVelocity N lam (B.phase i y) :=
          finiteComplexWeakLineDerivative_finiteResonantBoundaryCurve_comp
            N lam (B.hasDerivAt_phase_of_cutoff_ne_zero i y hyCutoff)
    unfold controlledBoundaryChartActionDensity
    rw [hvalue, hderiv, map_smul,
      standardComplexSymplecticPrimitive_resonantBoundary]
    simp only [smul_eq_mul]
    ring

/-- The integral of one chart action is its weighted angular winding times
the constant resonant primitive density. -/
theorem ControlledBoundaryAtlasBoundaryPhase.integral_controlledBoundaryChartActionDensity_finiteResonantProfileMap
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) (i : P.ι) :
    (∫ y : ℝ, controlledBoundaryChartActionDensity P i
        (finiteResonantProfileMap boundary N lam) y) =
      (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          B.phaseVelocity i y) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
  calc
    (∫ y : ℝ, controlledBoundaryChartActionDensity P i
        (finiteResonantProfileMap boundary N lam) y) =
      ∫ y : ℝ,
        (controlledBoundaryChartCutoff P i (y * Complex.I) *
          B.phaseVelocity i y) *
          ((1 / 2 : ℝ) * ∑ n : Fin N,
            (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦
          B.controlledBoundaryChartActionDensity_finiteResonantProfileMap
            hboundary N lam i y
    _ = (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          B.phaseVelocity i y) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
      rw [integral_mul_const]

/-- The full signed chart-action sum is the negative full winding times the
constant resonant primitive density. -/
theorem ControlledBoundaryAtlasBoundaryPhase.sum_integral_controlledBoundaryChartActionDensity_finiteResonantProfileMap
    [CompactSpace M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) :
    (∑ i, O.chartSign i *
      ∫ y : ℝ, controlledBoundaryChartActionDensity P i
        (finiteResonantProfileMap boundary N lam) y) =
      -(2 * Real.pi) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
  calc
    (∑ i, O.chartSign i *
      ∫ y : ℝ, controlledBoundaryChartActionDensity P i
        (finiteResonantProfileMap boundary N lam) y) =
      ∑ i, O.chartSign i *
        ((∫ y : ℝ,
            controlledBoundaryChartCutoff P i (y * Complex.I) *
              B.phaseVelocity i y) *
          ((1 / 2 : ℝ) * ∑ n : Fin N,
            (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [B.integral_controlledBoundaryChartActionDensity_finiteResonantProfileMap
          hboundary N lam i]
    _ = ∑ i,
        (O.chartSign i *
          ∫ y : ℝ,
            controlledBoundaryChartCutoff P i (y * Complex.I) *
              B.phaseVelocity i y) *
          ((1 / 2 : ℝ) * ∑ n : Fin N,
            (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, O.chartSign i *
          ∫ y : ℝ,
            controlledBoundaryChartCutoff P i (y * Complex.I) *
              B.phaseVelocity i y) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
      rw [Finset.sum_mul]
    _ = -(2 * Real.pi) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
      rw [B.signed_weighted_winding]

/-- The explicit finite resonant boundary action is the full angular period
times its constant primitive density. -/
theorem finiteResonantSymplecticBoundaryAction_eq_two_pi_mul
    (N : ℕ) (lam : ℝ) :
    finiteResonantSymplecticBoundaryAction N lam =
      (2 * Real.pi) *
        ((1 / 2 : ℝ) * ∑ n : Fin N,
          (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2) := by
  unfold finiteResonantSymplecticBoundaryAction
  simp_rw [standardComplexSymplecticPrimitive_resonantBoundary]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Global weak Stokes plus oriented phase gluing identifies the intrinsic
finite resonant surface integral with the genuine boundary action. -/
theorem ControlledBoundaryAtlasBoundaryPhase.integral_orientedFiniteResonantRiemannianSymplecticDensity_eq_boundaryAction
    [CompactSpace M] [Nonempty M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) :
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
        (Classical.choice inferInstance)
    (∫ x,
        orientedFiniteResonantRiemannianSymplecticDensity
          (modelWithCornersEuclideanHalfSpace 2)
          O.tangentOrientation boundary N lam x
        ∂riemannianSurfaceAreaMeasure
          (modelWithCornersEuclideanHalfSpace 2)) =
      finiteResonantSymplecticBoundaryAction N lam := by
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
      (Classical.choice inferInstance)
  obtain ⟨C, hG⟩ :=
    exists_lipschitzWith_finiteResonantProfileMap hboundary N lam
  have hstokes :=
    integral_orientedFiniteComplexRiemannianSymplecticDensity_eq_neg_boundary
      P O (finiteResonantProfileMap boundary N lam) hG
  change
    (∫ x,
        orientedFiniteResonantRiemannianSymplecticDensity
          (modelWithCornersEuclideanHalfSpace 2)
          O.tangentOrientation boundary N lam x
        ∂riemannianSurfaceAreaMeasure
          (modelWithCornersEuclideanHalfSpace 2)) =
      -∑ i, O.chartSign i *
        ∫ y : ℝ, controlledBoundaryChartActionDensity P i
          (finiteResonantProfileMap boundary N lam) y at hstokes
  rw [hstokes,
    B.sum_integral_controlledBoundaryChartActionDensity_finiteResonantProfileMap
      hboundary N lam,
    finiteResonantSymplecticBoundaryAction_eq_two_pi_mul]
  ring

#print axioms ControlledBoundaryAtlasBoundaryPhase
#print axioms
  finiteComplexWeakLineDerivative_finiteResonantBoundaryCurve_comp
#print axioms
  ControlledBoundaryAtlasBoundaryPhase.controlledBoundaryChartActionDensity_finiteResonantProfileMap
#print axioms
  ControlledBoundaryAtlasBoundaryPhase.sum_integral_controlledBoundaryChartActionDensity_finiteResonantProfileMap
#print axioms finiteResonantSymplecticBoundaryAction_eq_two_pi_mul
#print axioms
  ControlledBoundaryAtlasBoundaryPhase.integral_orientedFiniteResonantRiemannianSymplecticDensity_eq_boundaryAction

end

end GromovFilling
