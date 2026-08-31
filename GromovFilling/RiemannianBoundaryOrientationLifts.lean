import GromovFilling.RiemannianControlledBoundaryAxisDomain
import GromovFilling.RadialProjection

/-!
# Real lifts for induced boundary orientations

The induced-boundary-orientation contract is phrased for every continuous real
lift of a controlled circle parameter.  This module isolates two elementary
facts needed to make that formulation independent of the chosen lift: equal
circle projections differ by a constant on a closed interval, and reversal of
the boundary parametrization negates the canonical controlled parameter.

The module contains no global orientation or nonlinear conclusion.
-/

open Bundle Function Manifold Metric Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianBoundaryOrientationLiftsEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Two continuous real lifts with the same additive-circle projection have
constant difference on a closed interval. -/
theorem real_circle_lifts_sub_eq_on_Icc
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : Continuous lift₁) (hlift₂ : Continuous lift₂)
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    lift₁ x - lift₂ x = lift₁ y - lift₂ y := by
  letI : PreconnectedSpace (Set.Icc a b) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hcont₁ : Continuous (fun z : Set.Icc a b ↦ lift₁ z.1) :=
    hlift₁.comp continuous_subtype_val
  have hcont₂ : Continuous (fun z : Set.Icc a b ↦ lift₂ z.1) :=
    hlift₂.comp continuous_subtype_val
  simpa using
    (real_circle_lifts_difference_eq
      (fun z : Set.Icc a b ↦ lift₁ z.1)
      (fun z : Set.Icc a b ↦ lift₂ z.1)
      hcont₁ hcont₂
      (fun z ↦ hproject z.1 z.2)
      ⟨x, hx⟩ ⟨y, hy⟩)

/-- Replacing a continuous real lift on `Icc` by another lift of the same
circle map preserves increasing direction. -/
theorem strictMonoOn_of_continuous_real_circle_lifts_on_Icc
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : Continuous lift₁) (hlift₂ : Continuous lift₂)
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    (hmono : StrictMonoOn lift₂ (Set.Icc a b)) :
    StrictMonoOn lift₁ (Set.Icc a b) := by
  intro x hx y hy hxy
  have hconstant : lift₁ x - lift₂ x = lift₁ y - lift₂ y :=
    real_circle_lifts_sub_eq_on_Icc hlift₁ hlift₂ hproject hx hy
  have hlt : lift₂ x < lift₂ y := hmono hx hy hxy
  linarith

/-- Replacing a continuous real lift on `Icc` by another lift of the same
circle map preserves decreasing direction. -/
theorem strictAntiOn_of_continuous_real_circle_lifts_on_Icc
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : Continuous lift₁) (hlift₂ : Continuous lift₂)
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    (hanti : StrictAntiOn lift₂ (Set.Icc a b)) :
    StrictAntiOn lift₁ (Set.Icc a b) := by
  intro x hx y hy hxy
  have hconstant : lift₁ x - lift₂ x = lift₁ y - lift₂ y :=
    real_circle_lifts_sub_eq_on_Icc hlift₁ hlift₂ hproject hx hy
  have hlt : lift₂ y < lift₂ x := hanti hx hy hxy
  linarith

/-- Reversing a boundary parametrization negates its canonical controlled
chart-axis parameter. -/
theorem controlledBoundaryChartParameter_reverseCircleBoundary
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyDomain : (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    controlledBoundaryChartParameter (reverseCircleBoundary boundary) P i y =
      -controlledBoundaryChartParameter boundary P i y := by
  have hreverseRange : Set.range (reverseCircleBoundary boundary) =
      (modelWithCornersEuclideanHalfSpace 2).boundary M :=
    (range_reverseCircleBoundary boundary).trans hboundaryRange
  apply neg_injective
  apply hboundary.injective
  calc
    boundary
        (-controlledBoundaryChartParameter (reverseCircleBoundary boundary) P i y) =
      reverseCircleBoundary boundary
        (controlledBoundaryChartParameter (reverseCircleBoundary boundary) P i y) := by
          rfl
    _ = halfSpaceComplexExtChart (P.center i) (y * Complex.I) :=
      boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
        (reverseCircleBoundary boundary) hreverseRange P i y hyDomain
    _ = boundary (controlledBoundaryChartParameter boundary P i y) :=
      (boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
        boundary hboundaryRange P i y hyDomain).symm
    _ = boundary (- -controlledBoundaryChartParameter boundary P i y) := by
      simp

#print axioms real_circle_lifts_sub_eq_on_Icc
#print axioms strictMonoOn_of_continuous_real_circle_lifts_on_Icc
#print axioms strictAntiOn_of_continuous_real_circle_lifts_on_Icc
#print axioms controlledBoundaryChartParameter_reverseCircleBoundary

end

end GromovFilling
