import GromovFilling.RiemannianControlledBoundaryActiveCover
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Gluing local controlled-boundary directions

Every active chart in a finite controlled boundary partition has a controlled
axis interval and a real lift of its canonical boundary parameter with one
strict direction.  This file packages that local data and provides the
orientation-free topological descent step: any Boolean direction label that
agrees on active-chart overlaps glues to a locally constant, hence globally
constant, label on the parameter circle.

The conventional-orientation bridge is responsible only for proving the
overlap equality of its normalized labels.
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

/-- A Type-level witness for one of the two possible strict directions of a
real lift.  The strict-direction statements themselves are propositions, so
they cannot be used directly as the two Type arguments of `Sum`. -/
inductive ControlledBoundaryLiftDirection (lift : ℝ → ℝ) (s : Set ℝ) : Type where
  | mono (h : StrictMonoOn lift s) : ControlledBoundaryLiftDirection lift s
  | anti (h : StrictAntiOn lift s) : ControlledBoundaryLiftDirection lift s

/-- Boolean label of a stored lift direction. -/
def ControlledBoundaryLiftDirection.monoBit
    {lift : ℝ → ℝ} {s : Set ℝ} :
    ControlledBoundaryLiftDirection lift s → Bool
  | .mono _ => true
  | .anti _ => false

@[simp] theorem ControlledBoundaryLiftDirection.monoBit_mono
    {lift : ℝ → ℝ} {s : Set ℝ} (h : StrictMonoOn lift s) :
    (ControlledBoundaryLiftDirection.mono h).monoBit = true := rfl

@[simp] theorem ControlledBoundaryLiftDirection.monoBit_anti
    {lift : ℝ → ℝ} {s : Set ℝ} (h : StrictAntiOn lift s) :
    (ControlledBoundaryLiftDirection.anti h).monoBit = false := rfl

/-- A disjunctive strict-direction proof provides a nonempty Type-level
direction witness without eliminating a proposition into `Type`. -/
theorem nonempty_controlledBoundaryLiftDirection_of_or
    {lift : ℝ → ℝ} {s : Set ℝ}
    (h : StrictMonoOn lift s ∨ StrictAntiOn lift s) :
    Nonempty (ControlledBoundaryLiftDirection lift s) := by
  rcases h with hmono | hanti
  · exact ⟨ControlledBoundaryLiftDirection.mono hmono⟩
  · exact ⟨ControlledBoundaryLiftDirection.anti hanti⟩

/-- Select the Type-level direction witness supplied by a strict-direction
disjunction.  This is noncomputable only because the source disjunction is a
proposition. -/
noncomputable def ControlledBoundaryLiftDirection.ofOr
    {lift : ℝ → ℝ} {s : Set ℝ}
    (h : StrictMonoOn lift s ∨ StrictAntiOn lift s) :
    ControlledBoundaryLiftDirection lift s :=
  Classical.choice (nonempty_controlledBoundaryLiftDirection_of_or h)

/-- A controlled axis interval and a chosen real lift for one active boundary
chart.  `direction` records the only two possible strict directions without
making a classical Boolean decision about a proposition. -/
structure ControlledBoundaryActiveAxisLift
    (boundary : UnitAddCircle → M)
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.activeAxisCharts) where
  a : ℝ
  b : ℝ
  hab : a < b
  hdomain : ∀ y : ℝ, y ∈ Set.Icc a b → (y * Complex.I : ℂ) ∈
    chosenControlledHalfSpaceComplexChartDomain (P.center i.1)
  houtside : ∀ y : ℝ, y ∉ Set.Ioo a b →
    controlledBoundaryChartCutoff P i.1 (y * Complex.I) = 0
  lift : ℝ → ℝ
  continuous_lift : Continuous lift
  project_lift : ∀ y : ℝ, y ∈ Set.Icc a b →
    ((lift y : ℝ) : UnitAddCircle) =
      controlledBoundaryChartParameter boundary P i.1 y
  direction : ControlledBoundaryLiftDirection lift (Set.Icc a b)

/-- The Boolean encoding of an active axis lift's strict direction: `true`
means increasing and `false` means decreasing. -/
def ControlledBoundaryActiveAxisLift.monoBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i) : Bool :=
  L.direction.monoBit

/-- Every active controlled chart admits an interval lift with a definite
strict direction. -/
theorem nonempty_controlledBoundaryActiveAxisLift
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.activeAxisCharts) :
    Nonempty (ControlledBoundaryActiveAxisLift boundary P i) := by
  obtain ⟨a, b, hab, hdomain, houtside⟩ :=
    P.exists_axisInterval_of_active i
  obtain ⟨_C, lift, hliftContinuous, _hliftLipschitz,
      _hliftAbsolutelyContinuous, hliftProject, hliftDirection⟩ :=
    exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_of_mem_controlledDomain_on_Icc
      boundary hboundary hboundaryRange P i.1 a b hab.le hdomain
  let mk : ControlledBoundaryLiftDirection lift (Set.Icc a b) →
      ControlledBoundaryActiveAxisLift boundary P i := fun direction ↦ {
    a := a
    b := b
    hab := hab
    hdomain := hdomain
    houtside := houtside
    lift := lift
    continuous_lift := hliftContinuous
    project_lift := hliftProject
    direction := direction
  }
  rcases hliftDirection with hmono | hanti
  · exact ⟨mk (ControlledBoundaryLiftDirection.mono hmono)⟩
  · exact ⟨mk (ControlledBoundaryLiftDirection.anti hanti)⟩

/-- A collection of chartwise Boolean direction labels that agree wherever
their active boundary-chart sets overlap. -/
structure ControlledBoundaryDirectionCoverData
    (boundary : UnitAddCircle → M)
    (P : FiniteControlledBoundaryChartPartition M) where
  bit : P.activeAxisCharts → Bool
  overlap : ∀ (i j : P.activeAxisCharts) (q : UnitAddCircle),
    q ∈ controlledBoundaryChartActiveSet boundary P i.1 →
    q ∈ controlledBoundaryChartActiveSet boundary P j.1 →
    bit i = bit j

/-- The constant Boolean map on one active boundary-chart set. -/
def ControlledBoundaryDirectionCoverData.localMap
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    (D : ControlledBoundaryDirectionCoverData boundary P)
    (i : P.activeAxisCharts) :
    C(controlledBoundaryChartActiveSet boundary P i.1, Bool) :=
  ⟨fun _ ↦ D.bit i, continuous_const⟩

/-- Glue the compatible local Boolean labels along the open active-chart
cover of the parameter circle. -/
noncomputable def ControlledBoundaryDirectionCoverData.glueContinuous
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    {P : FiniteControlledBoundaryChartPartition M}
    (D : ControlledBoundaryDirectionCoverData boundary P) :
    C(UnitAddCircle, Bool) :=
  ContinuousMap.liftCover
    (fun i : P.activeAxisCharts ↦
      controlledBoundaryChartActiveSet boundary P i.1)
    D.localMap
    (by
      intro i j q hqi hqj
      change D.bit i = D.bit j
      exact D.overlap i j q hqi hqj)
    (exists_activeAxisChart_activeSet_mem_nhds
      boundary hboundary hboundaryRange P)

/-- The glued Boolean direction label is locally constant. -/
noncomputable def ControlledBoundaryDirectionCoverData.glueLocallyConstant
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    {P : FiniteControlledBoundaryChartPartition M}
    (D : ControlledBoundaryDirectionCoverData boundary P) :
    LocallyConstant UnitAddCircle Bool where
  toFun := D.glueContinuous hboundary hboundaryRange
  isLocallyConstant :=
    (IsLocallyConstant.iff_continuous _).mpr
      (D.glueContinuous hboundary hboundaryRange).continuous

/-- On every active chart set, the glued direction label is its defining
chartwise Boolean bit. -/
theorem ControlledBoundaryDirectionCoverData.glueContinuous_apply_eq_bit
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    {P : FiniteControlledBoundaryChartPartition M}
    (D : ControlledBoundaryDirectionCoverData boundary P)
    (i : P.activeAxisCharts) (q : UnitAddCircle)
    (hqi : q ∈ controlledBoundaryChartActiveSet boundary P i.1) :
    D.glueContinuous hboundary hboundaryRange q = D.bit i := by
  unfold ControlledBoundaryDirectionCoverData.glueContinuous
  rw [ContinuousMap.liftCover_coe
    (x := (⟨q, hqi⟩ : controlledBoundaryChartActiveSet boundary P i.1))]
  simp only [ControlledBoundaryDirectionCoverData.localMap]

/-- Compatible active-chart labels have the same glued value at every two
parameter-circle points. -/
theorem ControlledBoundaryDirectionCoverData.glueContinuous_apply_eq
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    {P : FiniteControlledBoundaryChartPartition M}
    (D : ControlledBoundaryDirectionCoverData boundary P)
    (q r : UnitAddCircle) :
    D.glueContinuous hboundary hboundaryRange q =
      D.glueContinuous hboundary hboundaryRange r := by
  exact LocallyConstant.apply_eq_of_preconnectedSpace
    (D.glueLocallyConstant hboundary hboundaryRange) q r

#print axioms ControlledBoundaryActiveAxisLift
#print axioms ControlledBoundaryActiveAxisLift.monoBit
#print axioms nonempty_controlledBoundaryActiveAxisLift
#print axioms ControlledBoundaryDirectionCoverData
#print axioms ControlledBoundaryDirectionCoverData.localMap
#print axioms ControlledBoundaryDirectionCoverData.glueContinuous
#print axioms ControlledBoundaryDirectionCoverData.glueLocallyConstant
#print axioms
  ControlledBoundaryDirectionCoverData.glueContinuous_apply_eq_bit
#print axioms ControlledBoundaryDirectionCoverData.glueContinuous_apply_eq

end

end GromovFilling
