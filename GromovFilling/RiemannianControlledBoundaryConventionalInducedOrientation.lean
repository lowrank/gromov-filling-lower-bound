import GromovFilling.RiemannianControlledBoundaryConventionalDirectionGlobal
import GromovFilling.RiemannianControlledBoundaryInducedOrientation

/-!
# Induced boundary orientation from a conventional surface orientation

A compact conventionally oriented Riemannian surface determines one of the
two parameter-circle orientations.  The active-chart direction cover makes
the choice globally constant.  If the supplied boundary parametrization has
the outward-first direction, its controlled induced-boundary contract holds;
otherwise the contract holds after reversing the parameter circle.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianControlledBoundaryConventionalInducedOrientationEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- A compact conventionally oriented surface induces the controlled
outward-first boundary orientation for the supplied parameterization or for
its reversal. -/
theorem RiemannianSurfaceOrientation.controlledInducedBoundaryOrientation_or_reverse
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    ControlledRiemannianInducedBoundaryOrientation
        O.toControlledRiemannianSurfaceOrientation boundary ∨
      ControlledRiemannianInducedBoundaryOrientation
        O.toControlledRiemannianSurfaceOrientation
          (reverseCircleBoundary boundary) := by
  let P₀ : FiniteControlledBoundaryChartPartition M :=
    Classical.choice (nonempty_finiteControlledBoundaryChartPartition M)
  let ε : Bool :=
    (conventionalControlledBoundaryDirectionCoverData
      O boundary hboundary hboundaryRange P₀).glueContinuous
        hboundary hboundaryRange 0
  cases hε : ε with
  | false =>
      right
      refine ⟨?_⟩
      intro P i a b lift hab hdomain hliftContinuous hliftProject
      have hnegContinuous : Continuous (fun y : ℝ ↦ -lift y) :=
        hliftContinuous.neg
      have hnegProject : ∀ y ∈ Set.Icc a b,
          (((-lift y : ℝ) : UnitAddCircle)) =
            controlledBoundaryChartParameter boundary P i y := by
        intro y hy
        calc
          ((-lift y : ℝ) : UnitAddCircle) =
              -((lift y : ℝ) : UnitAddCircle) := AddCircle.coe_neg _
          _ = -controlledBoundaryChartParameter
                (reverseCircleBoundary boundary) P i y := by
              rw [hliftProject y hy]
          _ = -(-controlledBoundaryChartParameter boundary P i y) := by
              rw [controlledBoundaryChartParameter_reverseCircleBoundary
                boundary hboundary hboundaryRange P i y (hdomain y hy)]
          _ = controlledBoundaryChartParameter boundary P i y := by simp
      have hdirection :=
        strictMonoOn_or_strictAntiOn_ofContinuousProjectedLift
          boundary hboundaryRange P i a b hab hdomain
          (fun y : ℝ ↦ -lift y) hnegContinuous hnegProject
      let d : ControlledBoundaryLiftDirection
          (fun y : ℝ ↦ -lift y) (Set.Icc a b) :=
        ControlledBoundaryLiftDirection.ofOr hdirection
      let L : ControlledBoundaryAxisLift boundary P i := {
        a := a
        b := b
        hab := hab
        hdomain := hdomain
        lift := fun y ↦ -lift y
        continuous_lift := hnegContinuous
        project_lift := hnegProject
        direction := d
      }
      have hbit : L.outwardBit (O.controlledChartSign (P.center i)) = false := by
        calc
          L.outwardBit (O.controlledChartSign (P.center i)) =
              (conventionalControlledBoundaryDirectionCoverData
                O boundary hboundary hboundaryRange P₀).glueContinuous
                  hboundary hboundaryRange 0 :=
            L.outwardBit_eq_conventionalGlobalDirection
              O boundary hboundary hboundaryRange P₀ P i
          _ = ε := by rfl
          _ = false := hε
      have hdirectionBit :=
        (L.outwardBit_eq_false_iff
          (O.controlledChartSign (P.center i))
          (O.controlledChartSign_eq_one_or_neg_one (P.center i))).mp hbit
      have hdirectionBit' :
          (O.controlledChartSign (P.center i) = 1 ∧
              StrictMonoOn (fun y : ℝ ↦ -lift y) (Set.Icc a b)) ∨
            (O.controlledChartSign (P.center i) = -1 ∧
              StrictAntiOn (fun y : ℝ ↦ -lift y) (Set.Icc a b)) := by
        simpa only [L] using hdirectionBit
      change
        (O.controlledChartSign (P.center i) = 1 ∧
            StrictAntiOn lift (Set.Icc a b)) ∨
          (O.controlledChartSign (P.center i) = -1 ∧
            StrictMonoOn lift (Set.Icc a b))
      rcases hdirectionBit' with hpositive | hnegative
      · left
        refine ⟨hpositive.1, ?_⟩
        intro x hx y hy hxy
        have hlt := hpositive.2 hx hy hxy
        linarith
      · right
        refine ⟨hnegative.1, ?_⟩
        intro x hx y hy hxy
        have hlt := hnegative.2 hx hy hxy
        linarith
  | true =>
      left
      refine ⟨?_⟩
      intro P i a b lift hab hdomain hliftContinuous hliftProject
      have hdirection :=
        strictMonoOn_or_strictAntiOn_ofContinuousProjectedLift
          boundary hboundaryRange P i a b hab hdomain lift
          hliftContinuous hliftProject
      let d : ControlledBoundaryLiftDirection lift (Set.Icc a b) :=
        ControlledBoundaryLiftDirection.ofOr hdirection
      let L : ControlledBoundaryAxisLift boundary P i := {
        a := a
        b := b
        hab := hab
        hdomain := hdomain
        lift := lift
        continuous_lift := hliftContinuous
        project_lift := hliftProject
        direction := d
      }
      have hbit : L.outwardBit (O.controlledChartSign (P.center i)) = true := by
        calc
          L.outwardBit (O.controlledChartSign (P.center i)) =
              (conventionalControlledBoundaryDirectionCoverData
                O boundary hboundary hboundaryRange P₀).glueContinuous
                  hboundary hboundaryRange 0 :=
            L.outwardBit_eq_conventionalGlobalDirection
              O boundary hboundary hboundaryRange P₀ P i
          _ = ε := by rfl
          _ = true := hε
      have hdirectionBit :=
        (L.outwardBit_eq_true_iff
          (O.controlledChartSign (P.center i))
          (O.controlledChartSign_eq_one_or_neg_one (P.center i))).mp hbit
      change
        (O.controlledChartSign (P.center i) = 1 ∧
            StrictAntiOn lift (Set.Icc a b)) ∨
          (O.controlledChartSign (P.center i) = -1 ∧
            StrictMonoOn lift (Set.Icc a b))
      simpa only [L] using hdirectionBit

#print axioms
  RiemannianSurfaceOrientation.controlledInducedBoundaryOrientation_or_reverse

end

end GromovFilling
