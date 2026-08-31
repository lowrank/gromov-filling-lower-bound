import GromovFilling.RiemannianControlledBoundaryAxisDomain
import Mathlib.Topology.Order.IntermediateValue

/-!
# Endpoint spans of injective additive-circle lifts

A continuous real lift whose projection to the unit additive circle is
injective on a closed interval cannot traverse a full period.  Otherwise the
intermediate value theorem would produce two interval points whose real
values differ by one and hence have the same circle projection.  Applying
this observation to a controlled boundary-chart axis gives the strict
endpoint span needed to expose an unused phase arc.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

/-- A continuous real lift with injective unit-circle projection on a closed
interval has endpoint displacement strictly smaller than one period. -/
theorem abs_sub_lt_one_of_continuousOn_of_injOn_unitAddCircle_projection
    {lift : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hliftContinuous : ContinuousOn lift (Set.Icc a b))
    (hprojectionInjective : Set.InjOn
      (fun y : ℝ ↦ ((lift y : ℝ) : UnitAddCircle)) (Set.Icc a b)) :
    |lift b - lift a| < 1 := by
  by_contra hspan
  have hspanLower : 1 ≤ |lift b - lift a| := le_of_not_gt hspan
  rcases le_total (lift a) (lift b) with hlift | hlift
  · have hdiff : 1 ≤ lift b - lift a := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hlift)] using hspanLower
    have htarget : lift a + 1 ∈ Set.Icc (lift a) (lift b) := by
      constructor <;> linarith
    obtain ⟨y, hy, hyLift⟩ :=
      intermediate_value_Icc hab hliftContinuous htarget
    have hprojection :
        ((lift y : ℝ) : UnitAddCircle) =
          ((lift a : ℝ) : UnitAddCircle) := by
      calc
        ((lift y : ℝ) : UnitAddCircle) =
            ((lift a + 1 : ℝ) : UnitAddCircle) :=
          congrArg (fun r : ℝ ↦ (r : UnitAddCircle)) hyLift
        _ = ((lift a : ℝ) : UnitAddCircle) :=
          AddCircle.coe_add_period (1 : ℝ) (lift a)
    have hya : y = a :=
      hprojectionInjective hy (Set.left_mem_Icc.mpr hab) hprojection
    rw [hya] at hyLift
    linarith
  · have hdiff : 1 ≤ lift a - lift b := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr hlift), neg_sub]
        using hspanLower
    have htarget : lift b + 1 ∈ Set.Icc (lift b) (lift a) := by
      constructor <;> linarith
    obtain ⟨y, hy, hyLift⟩ :=
      intermediate_value_Icc' hab hliftContinuous htarget
    have hprojection :
        ((lift y : ℝ) : UnitAddCircle) =
          ((lift b : ℝ) : UnitAddCircle) := by
      calc
        ((lift y : ℝ) : UnitAddCircle) =
            ((lift b + 1 : ℝ) : UnitAddCircle) :=
          congrArg (fun r : ℝ ↦ (r : UnitAddCircle)) hyLift
        _ = ((lift b : ℝ) : UnitAddCircle) :=
          AddCircle.coe_add_period (1 : ℝ) (lift b)
    have hyb : y = b :=
      hprojectionInjective hy (Set.right_mem_Icc.mpr hab) hprojection
    rw [hyb] at hyLift
    linarith

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- The Lipschitz real lift of a controlled boundary-chart parameter can be
chosen with endpoint displacement strictly smaller than one circle period. -/
theorem exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_with_span_lt_one_on_Icc
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (a b : ℝ) (hab : a ≤ b)
    (hdomain : ∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    ∃ C : ℝ≥0, ∃ lift : ℝ → ℝ,
      Continuous lift ∧
      LipschitzOnWith C lift (Set.Icc a b) ∧
      AbsolutelyContinuousOnInterval lift a b ∧
      (∀ y ∈ Set.Icc a b,
        ((lift y : ℝ) : UnitAddCircle) =
          controlledBoundaryChartParameter boundary P i y) ∧
      (StrictMonoOn lift (Set.Icc a b) ∨
        StrictAntiOn lift (Set.Icc a b)) ∧
      |lift b - lift a| < 1 := by
  obtain ⟨C, lift, hliftContinuous, hliftLipschitz,
      hliftAbsolutelyContinuous, hliftProject, hliftMonotone⟩ :=
    exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_of_mem_controlledDomain_on_Icc
      boundary hboundary hboundaryRange P i a b hab hdomain
  have hparameterInjective : Set.InjOn
      (controlledBoundaryChartParameter boundary P i) (Set.Icc a b) :=
    injOn_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i (Set.Icc a b) hdomain
  have hprojectionInjective : Set.InjOn
      (fun y : ℝ ↦ ((lift y : ℝ) : UnitAddCircle))
      (Set.Icc a b) := by
    intro y hy z hz hyz
    apply hparameterInjective hy hz
    calc
      controlledBoundaryChartParameter boundary P i y =
          ((lift y : ℝ) : UnitAddCircle) := (hliftProject y hy).symm
      _ = ((lift z : ℝ) : UnitAddCircle) := hyz
      _ = controlledBoundaryChartParameter boundary P i z :=
        hliftProject z hz
  have hliftSpan : |lift b - lift a| < 1 :=
    abs_sub_lt_one_of_continuousOn_of_injOn_unitAddCircle_projection
      hab hliftContinuous.continuousOn hprojectionInjective
  exact ⟨C, lift, hliftContinuous, hliftLipschitz,
    hliftAbsolutelyContinuous, hliftProject, hliftMonotone, hliftSpan⟩

#print axioms
  abs_sub_lt_one_of_continuousOn_of_injOn_unitAddCircle_projection
#print axioms
  exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_with_span_lt_one_on_Icc

end

end GromovFilling
