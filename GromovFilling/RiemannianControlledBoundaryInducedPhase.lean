import GromovFilling.RiemannianControlledBoundaryACSubstitution
import GromovFilling.RiemannianControlledBoundaryAxisCoverage
import GromovFilling.RiemannianControlledBoundaryInducedOrientation
import GromovFilling.RiemannianControlledBoundaryWinding

/-!
# Boundary phases induced by a controlled surface orientation

This file constructs the local angular phases needed by controlled-atlas
Stokes.  A compact interval contains each chart cutoff support, the canonical
circle parameter has a Lipschitz real lift on that interval, and the induced
boundary orientation selects the direction of that lift.  Its endpoint span
is strictly shorter than one circle period.  Boundary-support coverage then
shows that the complementary phase arc carries zero partition weight, so
absolutely continuous substitution recovers one full oriented period.
-/

open Bundle Filter Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

/-- Scaling a real representative by one angular period and then converting
from radians recovers its unit-additive-circle class. -/
theorem angleToUnitAddCircle_two_pi_mul_eq_coe (r : ℝ) :
    angleToUnitAddCircle (2 * Real.pi * r) =
      ((r : ℝ) : UnitAddCircle) := by
  unfold angleToUnitAddCircle
  rw [show (2 * Real.pi * r : ℝ) / (2 * Real.pi) = r by
    field_simp [Real.pi_ne_zero]]

/-- Multiplying a real Lipschitz function by `2π` multiplies its Lipschitz
constant by the corresponding nonnegative real. -/
theorem lipschitzOnWith_two_pi_mul
    {s : Set ℝ} {lift : ℝ → ℝ} {C : ℝ≥0}
    (hlift : LipschitzOnWith C lift s) :
    LipschitzOnWith
      (⟨2 * Real.pi, (mul_pos (by norm_num) Real.pi_pos).le⟩ * C)
      (fun y : ℝ ↦ 2 * Real.pi * lift y) s := by
  have htwoPi : 0 < (2 * Real.pi : ℝ) :=
    mul_pos (by norm_num) Real.pi_pos
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hdist := hlift.dist_le_mul y hy z hz
  rw [Real.dist_eq, Real.dist_eq] at hdist ⊢
  calc
    |2 * Real.pi * lift y - 2 * Real.pi * lift z| =
        2 * Real.pi * |lift y - lift z| := by
      rw [← mul_sub, abs_mul, abs_of_pos htwoPi]
    _ ≤ 2 * Real.pi * ((C : ℝ) * |y - z|) :=
      mul_le_mul_of_nonneg_left hdist htwoPi.le
    _ = ((⟨2 * Real.pi, htwoPi.le⟩ * C : ℝ≥0) : ℝ) *
        |y - z| := by
      simp only [NNReal.coe_mul, NNReal.coe_mk]

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

/-- The local phase data constructed for one controlled boundary chart. -/
structure ControlledBoundaryChartInducedPhaseData
    (P : FiniteControlledBoundaryChartPartition M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (boundary : UnitAddCircle → M) (i : P.ι) where
  phase : ℝ → ℝ
  phaseVelocity : ℝ → ℝ
  ae_hasDerivAt_phase_of_cutoff_ne_zero :
    ∀ᵐ y : ℝ, controlledBoundaryChartCutoff P i
        (y * Complex.I) ≠ 0 →
      HasDerivAt phase (phaseVelocity y) y
  chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero :
    ∀ y : ℝ, controlledBoundaryChartCutoff P i
        (y * Complex.I) ≠ 0 →
      (fun t : ℝ ↦
          halfSpaceComplexExtChart (P.center i) (t * Complex.I)) =ᶠ[nhds y]
        fun t : ℝ ↦ boundary (angleToUnitAddCircle (phase t))
  chart_signed_winding_eq_boundary_partition :
    R.chartSign (P.center i) *
        (∫ y : ℝ, controlledBoundaryChartCutoff P i (y * Complex.I) *
          phaseVelocity y) =
      -(∫ t in -Real.pi..Real.pi,
        P.partition i (boundary (angleToUnitAddCircle t)))

/-- Every chart of a controlled partition has induced local phase data. -/
theorem nonempty_controlledBoundaryChartInducedPhaseData
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (H : ControlledRiemannianInducedBoundaryOrientation R boundary)
    (i : P.ι) :
    Nonempty (ControlledBoundaryChartInducedPhaseData P R boundary i) := by
  classical
  rcases all_zero_or_exists_controlledBoundaryChartAxisInterval P i with
      hzero | ⟨a, b, hab, hdomain, houtside⟩
  · refine ⟨{
      phase := fun _y ↦ 0
      phaseVelocity := fun _y ↦ 0
      ae_hasDerivAt_phase_of_cutoff_ne_zero := ?_
      chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero := ?_
      chart_signed_winding_eq_boundary_partition := ?_
    }⟩
    · exact Filter.Eventually.of_forall fun y hy ↦
        (hy (hzero y)).elim
    · intro y hy
      exact (hy (hzero y)).elim
    · have hpartitionZero :=
        boundary_partition_eq_zero_of_controlledBoundaryChartCutoff_axis_eq_zero
          boundary hboundary hboundaryRange P i hzero
      have hright : (∫ t in -Real.pi..Real.pi,
          P.partition i (boundary (angleToUnitAddCircle t))) = 0 := by
        apply intervalIntegral.integral_zero_ae
        exact Filter.Eventually.of_forall fun t _ht ↦
          hpartitionZero (angleToUnitAddCircle t)
      rw [hright]
      simp only [mul_zero, integral_zero, neg_zero]
  · obtain ⟨C, lift, hliftContinuous, hliftLipschitz,
        _hliftAbsolutelyContinuous, hliftProject, _hliftMonotone,
        hliftSpan⟩ :=
      exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_with_span_lt_one_on_Icc
        boundary hboundary hboundaryRange P i a b hab.le hdomain
    have horientation :=
      H.chart_lift_orientation P i a b lift hab hdomain
        hliftContinuous hliftProject
    let phase : ℝ → ℝ := fun y ↦ 2 * Real.pi * lift y
    let f : ℝ → ℝ := fun t ↦
      P.partition i (boundary (angleToUnitAddCircle t))
    let g : ℝ → ℝ := fun y ↦
      controlledBoundaryChartCutoff P i (y * Complex.I) * deriv phase y
    have htwoPi : 0 < (2 * Real.pi : ℝ) :=
      mul_pos (by norm_num) Real.pi_pos
    have hphaseLipschitzIcc : LipschitzOnWith
        (⟨2 * Real.pi, htwoPi.le⟩ * C) phase (Set.Icc a b) := by
      simpa only [phase] using lipschitzOnWith_two_pi_mul hliftLipschitz
    have hphaseLipschitzUIcc : LipschitzOnWith
        (⟨2 * Real.pi, htwoPi.le⟩ * C) phase (Set.uIcc a b) := by
      simpa only [Set.uIcc_of_le hab.le] using hphaseLipschitzIcc
    have hf : Continuous f := by
      exact (P.contMDiff_partition i).continuous.comp
        (hboundary.lipschitzWith.continuous.comp
          continuous_angleToUnitAddCircle)
    have hfBound (t : ℝ) : ‖f t‖₊ ≤ (1 : ℝ≥0) := by
      rw [Real.nnnorm_of_nonneg]
      · exact_mod_cast P.partition.le_one i
          (boundary (angleToUnitAddCircle t))
      · exact P.partition_nonneg i
          (boundary (angleToUnitAddCircle t))
    have hfPeriodic : Function.Periodic f (2 * Real.pi) := by
      intro t
      dsimp only [f]
      rw [angleToUnitAddCircle_add_two_pi]
    have hsupport : support g ⊆ Set.Ioc a b := by
      intro y hy
      have hyCutoff : controlledBoundaryChartCutoff P i
          (y * Complex.I) ≠ 0 := by
        intro hyZero
        apply hy
        simp only [g, hyZero, zero_mul]
      have hyOpen : y ∈ Set.Ioo a b := by
        by_contra hyInterval
        exact hyCutoff (houtside y hyInterval)
      exact ⟨hyOpen.1, hyOpen.2.le⟩
    have hglobal : (∫ y : ℝ, g y) = ∫ y in a..b, g y :=
      (intervalIntegral.integral_eq_integral_of_support_subset
        hsupport).symm
    have hcutoffEq (y : ℝ) (hy : y ∈ Set.Icc a b) :
        controlledBoundaryChartCutoff P i (y * Complex.I) =
          f (phase y) := by
      calc
        controlledBoundaryChartCutoff P i (y * Complex.I) =
            P.partition i
              (boundary
                (controlledBoundaryChartParameter boundary P i y)) :=
          controlledBoundaryChartCutoff_eq_boundary_partition_parameter_of_mem_controlledDomain
            boundary hboundaryRange P i y (hdomain y hy)
        _ = P.partition i
            (boundary (((lift y : ℝ) : UnitAddCircle))) := by
          rw [hliftProject y hy]
        _ = f (phase y) := by
          dsimp only [f, phase]
          rw [angleToUnitAddCircle_two_pi_mul_eq_coe]
    have hpointwise :
        (∫ y in a..b, g y) =
          ∫ y in a..b, f (phase y) * deriv phase y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Set.Icc a b := by
        simpa only [Set.uIcc_of_le hab.le] using hy
      simp only [g]
      rw [hcutoffEq y hyIcc]
    have hsubstitution :
        (∫ y in a..b, f (phase y) * deriv phase y) =
          ∫ t in phase a..phase b, f t :=
      intervalIntegral_comp_mul_deriv_of_lipschitzOnWith
        hphaseLipschitzUIcc hf hfBound
    have hlocal : (∫ y : ℝ, g y) =
        ∫ t in phase a..phase b, f t :=
      hglobal.trans (hpointwise.trans hsubstitution)
    have hwinding : R.chartSign (P.center i) * (∫ y : ℝ, g y) =
        -(∫ t in -Real.pi..Real.pi, f t) := by
      rcases horientation with ⟨hsign, hliftAnti⟩ |
          ⟨hsign, hliftMono⟩
      · have hliftBA : lift b < lift a :=
          hliftAnti (Set.left_mem_Icc.mpr hab.le)
            (Set.right_mem_Icc.mpr hab.le) hab
        have hliftAPeriod : lift a < lift b + 1 := by
          rw [abs_of_neg (sub_neg.mpr hliftBA)] at hliftSpan
          linarith
        have hphaseBA : phase b ≤ phase a := by
          dsimp only [phase]
          nlinarith [Real.pi_pos]
        have hphaseAPeriod : phase a ≤ phase b + 2 * Real.pi := by
          dsimp only [phase]
          nlinarith [Real.pi_pos]
        have hzeroUnused : ∀ t ∈ Set.Ioo (phase a)
            (phase b + 2 * Real.pi), f t = 0 := by
          intro t ht
          by_contra hft
          have hq : P.partition i
              (boundary (angleToUnitAddCircle t)) ≠ 0 := by
            simpa only [f] using hft
          obtain ⟨y, _hyDomain, hyParameter, hyCutoff⟩ :=
            exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
              boundary hboundary hboundaryRange P i
                (angleToUnitAddCircle t) hq
          have hyOpen : y ∈ Set.Ioo a b := by
            by_contra hyInterval
            exact hyCutoff (houtside y hyInterval)
          have hyIcc : y ∈ Set.Icc a b :=
            ⟨hyOpen.1.le, hyOpen.2.le⟩
          have hyLiftLower : lift b < lift y :=
            hliftAnti hyIcc (Set.right_mem_Icc.mpr hab.le) hyOpen.2
          have hyLiftUpper : lift y < lift a :=
            hliftAnti (Set.left_mem_Icc.mpr hab.le) hyIcc hyOpen.1
          let r : ℝ := t / (2 * Real.pi)
          have ht' := ht
          dsimp only [phase] at ht'
          have hrLower : lift a < r := by
            dsimp only [r]
            rw [lt_div_iff₀ htwoPi]
            nlinarith [ht'.1]
          have hrUpper : r < lift b + 1 := by
            dsimp only [r]
            rw [div_lt_iff₀ htwoPi]
            nlinarith [ht'.2]
          have hyIco : lift y ∈ Set.Ico (lift b) (lift b + 1) :=
            ⟨hyLiftLower.le,
              hyLiftUpper.trans hliftAPeriod⟩
          have hrIco : r ∈ Set.Ico (lift b) (lift b + 1) :=
            ⟨(hliftBA.trans hrLower).le, hrUpper⟩
          have hcoe : ((lift y : ℝ) : UnitAddCircle) =
              ((r : ℝ) : UnitAddCircle) := by
            calc
              ((lift y : ℝ) : UnitAddCircle) =
                  controlledBoundaryChartParameter boundary P i y :=
                hliftProject y hyIcc
              _ = angleToUnitAddCircle t := hyParameter
              _ = ((r : ℝ) : UnitAddCircle) := by rfl
          have hyr : lift y = r :=
            (AddCircle.coe_eq_coe_iff_of_mem_Ico
              (p := (1 : ℝ)) (a := lift b) hyIco hrIco).mp hcoe
          linarith
        have hfull : (∫ t in phase b..phase a, f t) =
            ∫ t in -Real.pi..Real.pi, f t := by
          have h := intervalIntegral_eq_periodic_of_eq_zero_on_complement
            hf hfPeriodic hphaseBA hphaseAPeriod hzeroUnused
            (s := -Real.pi)
          convert h using 1 <;> ring
        calc
          R.chartSign (P.center i) * (∫ y : ℝ, g y) =
              ∫ t in phase a..phase b, f t := by
            rw [hsign, one_mul, hlocal]
          _ = -(∫ t in phase b..phase a, f t) :=
            intervalIntegral.integral_symm (phase b) (phase a)
          _ = -(∫ t in -Real.pi..Real.pi, f t) := by rw [hfull]
      · have hliftAB : lift a < lift b :=
          hliftMono (Set.left_mem_Icc.mpr hab.le)
            (Set.right_mem_Icc.mpr hab.le) hab
        have hliftBPeriod : lift b < lift a + 1 := by
          rw [abs_of_pos (sub_pos.mpr hliftAB)] at hliftSpan
          linarith
        have hphaseAB : phase a ≤ phase b := by
          dsimp only [phase]
          nlinarith [Real.pi_pos]
        have hphaseBPeriod : phase b ≤ phase a + 2 * Real.pi := by
          dsimp only [phase]
          nlinarith [Real.pi_pos]
        have hzeroUnused : ∀ t ∈ Set.Ioo (phase b)
            (phase a + 2 * Real.pi), f t = 0 := by
          intro t ht
          by_contra hft
          have hq : P.partition i
              (boundary (angleToUnitAddCircle t)) ≠ 0 := by
            simpa only [f] using hft
          obtain ⟨y, _hyDomain, hyParameter, hyCutoff⟩ :=
            exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
              boundary hboundary hboundaryRange P i
                (angleToUnitAddCircle t) hq
          have hyOpen : y ∈ Set.Ioo a b := by
            by_contra hyInterval
            exact hyCutoff (houtside y hyInterval)
          have hyIcc : y ∈ Set.Icc a b :=
            ⟨hyOpen.1.le, hyOpen.2.le⟩
          have hyLiftLower : lift a < lift y :=
            hliftMono (Set.left_mem_Icc.mpr hab.le) hyIcc hyOpen.1
          have hyLiftUpper : lift y < lift b :=
            hliftMono hyIcc (Set.right_mem_Icc.mpr hab.le) hyOpen.2
          let r : ℝ := t / (2 * Real.pi)
          have ht' := ht
          dsimp only [phase] at ht'
          have hrLower : lift b < r := by
            dsimp only [r]
            rw [lt_div_iff₀ htwoPi]
            nlinarith [ht'.1]
          have hrUpper : r < lift a + 1 := by
            dsimp only [r]
            rw [div_lt_iff₀ htwoPi]
            nlinarith [ht'.2]
          have hyIco : lift y ∈ Set.Ico (lift a) (lift a + 1) :=
            ⟨hyLiftLower.le,
              hyLiftUpper.trans hliftBPeriod⟩
          have hrIco : r ∈ Set.Ico (lift a) (lift a + 1) :=
            ⟨(hliftAB.trans hrLower).le, hrUpper⟩
          have hcoe : ((lift y : ℝ) : UnitAddCircle) =
              ((r : ℝ) : UnitAddCircle) := by
            calc
              ((lift y : ℝ) : UnitAddCircle) =
                  controlledBoundaryChartParameter boundary P i y :=
                hliftProject y hyIcc
              _ = angleToUnitAddCircle t := hyParameter
              _ = ((r : ℝ) : UnitAddCircle) := by rfl
          have hyr : lift y = r :=
            (AddCircle.coe_eq_coe_iff_of_mem_Ico
              (p := (1 : ℝ)) (a := lift a) hyIco hrIco).mp hcoe
          linarith
        have hfull : (∫ t in phase a..phase b, f t) =
            ∫ t in -Real.pi..Real.pi, f t := by
          have h := intervalIntegral_eq_periodic_of_eq_zero_on_complement
            hf hfPeriodic hphaseAB hphaseBPeriod hzeroUnused
            (s := -Real.pi)
          convert h using 1 <;> ring
        calc
          R.chartSign (P.center i) * (∫ y : ℝ, g y) =
              -(∫ t in phase a..phase b, f t) := by
            rw [hsign, neg_one_mul, hlocal]
          _ = -(∫ t in -Real.pi..Real.pi, f t) := by rw [hfull]
    refine ⟨{
      phase := phase
      phaseVelocity := deriv phase
      ae_hasDerivAt_phase_of_cutoff_ne_zero := ?_
      chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero := ?_
      chart_signed_winding_eq_boundary_partition := ?_
    }⟩
    · filter_upwards
          [ae_hasDerivAt_deriv_of_lipschitzOnWith_uIcc
            hphaseLipschitzUIcc]
          with y hyPhase
      intro hyCutoff
      apply hyPhase
      rw [Set.uIcc_of_le hab.le]
      have hyOpen : y ∈ Set.Ioo a b := by
        by_contra hyInterval
        exact hyCutoff (houtside y hyInterval)
      exact ⟨hyOpen.1.le, hyOpen.2.le⟩
    · intro y hyCutoff
      have hyOpen : y ∈ Set.Ioo a b := by
        by_contra hyInterval
        exact hyCutoff (houtside y hyInterval)
      filter_upwards [isOpen_Ioo.mem_nhds hyOpen] with t ht
      have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
      calc
        halfSpaceComplexExtChart (P.center i) (t * Complex.I) =
            boundary (controlledBoundaryChartParameter boundary P i t) :=
          (boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
            boundary hboundaryRange P i t (hdomain t htIcc)).symm
        _ = boundary (((lift t : ℝ) : UnitAddCircle)) := by
          rw [hliftProject t htIcc]
        _ = boundary (angleToUnitAddCircle (phase t)) := by
          dsimp only [phase]
          rw [angleToUnitAddCircle_two_pi_mul_eq_coe]
    · simpa only [g, f] using hwinding

/-- Choosing the preceding chartwise data gives the local phase datum for
the whole finite controlled atlas. -/
theorem nonempty_controlledBoundaryAtlasBoundaryPhaseLocalData_of_inducedBoundaryOrientation
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (H : ControlledRiemannianInducedBoundaryOrientation R boundary) :
    Nonempty (ControlledBoundaryAtlasBoundaryPhaseLocalData P
      (R.toBoundaryAtlasOrientation P) boundary) := by
  classical
  let D : ∀ i : P.ι,
      ControlledBoundaryChartInducedPhaseData P R boundary i :=
    fun i ↦ Classical.choice
      (nonempty_controlledBoundaryChartInducedPhaseData
        boundary hboundary hboundaryRange P R H i)
  exact ⟨{
    phase := fun i ↦ (D i).phase
    phaseVelocity := fun i ↦ (D i).phaseVelocity
    ae_hasDerivAt_phase_of_cutoff_ne_zero := fun i ↦
      (D i).ae_hasDerivAt_phase_of_cutoff_ne_zero
    chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero := fun i ↦
      (D i).chartAxis_eventuallyEq_boundary_of_cutoff_ne_zero
    chart_signed_winding_eq_boundary_partition := fun i ↦ by
      simpa only [ControlledRiemannianSurfaceOrientation.toBoundaryAtlasOrientation]
        using (D i).chart_signed_winding_eq_boundary_partition
  }⟩

/-- An oriented controlled filling with the induced boundary convention has
the complete boundary-phase datum required by the nonlinear Stokes layer. -/
theorem nonempty_controlledBoundaryAtlasBoundaryPhase_of_inducedBoundaryOrientation
    [CompactSpace M]
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (H : ControlledRiemannianInducedBoundaryOrientation R boundary) :
    Nonempty (ControlledBoundaryAtlasBoundaryPhase P
      (R.toBoundaryAtlasOrientation P) boundary) := by
  obtain ⟨L⟩ :=
    nonempty_controlledBoundaryAtlasBoundaryPhaseLocalData_of_inducedBoundaryOrientation
      boundary hboundary hboundaryRange P R H
  exact ⟨L.toBoundaryPhase hboundary⟩

#print axioms angleToUnitAddCircle_two_pi_mul_eq_coe
#print axioms lipschitzOnWith_two_pi_mul
#print axioms ControlledBoundaryChartInducedPhaseData
#print axioms nonempty_controlledBoundaryChartInducedPhaseData
#print axioms
  nonempty_controlledBoundaryAtlasBoundaryPhaseLocalData_of_inducedBoundaryOrientation
#print axioms
  nonempty_controlledBoundaryAtlasBoundaryPhase_of_inducedBoundaryOrientation

end

end GromovFilling
