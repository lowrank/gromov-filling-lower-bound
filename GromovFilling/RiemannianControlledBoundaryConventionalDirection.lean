import GromovFilling.RiemannianControlledBoundaryAxisLiftOverlap

/-!
# A conventional orientation's active boundary-direction cover

For one finite controlled boundary partition, choose a lift on every active
axis chart and label it by the outward-first Boolean determined by a
conventional surface orientation.  The mixed overlap bridge proves these
labels agree, so the existing topological cover machinery supplies a global
Boolean direction on the parameter circle.
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

/-- A fixed classical choice of a directed lift on each active chart of a
finite controlled boundary partition. -/
noncomputable def conventionalControlledBoundaryActiveAxisLift
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.activeAxisCharts) :
    ControlledBoundaryActiveAxisLift boundary P i :=
  Classical.choice
    (nonempty_controlledBoundaryActiveAxisLift
      boundary hboundary hboundaryRange P i)

/-- The compatible active-chart outward-first bits determined by one
conventional surface orientation. -/
noncomputable def conventionalControlledBoundaryDirectionCoverData
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) :
    ControlledBoundaryDirectionCoverData boundary P where
  bit := fun i ↦
    (conventionalControlledBoundaryActiveAxisLift
      boundary hboundary hboundaryRange P i).outwardBit
      (O.controlledChartSign (P.center i.1))
  overlap := by
    intro i j q hqi hqj
    exact ControlledBoundaryActiveAxisLift.outwardBit_eq_of_activeOverlap
      O boundary hboundary hboundaryRange P P i j
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P i)
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P j)
      q hqi hqj

/-- The bit stored in the conventional cover is definitionally the selected
active lift's outward-first bit. -/
@[simp] theorem conventionalControlledBoundaryDirectionCoverData_bit
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.activeAxisCharts) :
    (conventionalControlledBoundaryDirectionCoverData
      O boundary hboundary hboundaryRange P).bit i =
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P i).outwardBit
        (O.controlledChartSign (P.center i.1)) := rfl

#print axioms conventionalControlledBoundaryActiveAxisLift
#print axioms conventionalControlledBoundaryDirectionCoverData
#print axioms conventionalControlledBoundaryDirectionCoverData_bit

end

end GromovFilling
