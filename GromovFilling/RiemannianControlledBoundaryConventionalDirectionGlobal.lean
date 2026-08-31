import GromovFilling.RiemannianControlledBoundaryConventionalDirection

/-!
# Global conventional boundary direction

The compatible active-chart cover from a conventional surface orientation has
one global Boolean value.  Here that value is compared with every arbitrary
controlled chart lift, including a chart whose cutoff is inactive in its own
finite partition.
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

/-- Every arbitrary controlled axis lift has the global outward-first bit
glued from any fixed finite reference partition. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_conventionalGlobalDirection
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P₀ : FiniteControlledBoundaryChartPartition M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (L : ControlledBoundaryAxisLift boundary P i) :
    L.outwardBit (O.controlledChartSign (P.center i)) =
      (conventionalControlledBoundaryDirectionCoverData
        O boundary hboundary hboundaryRange P₀).glueContinuous
          hboundary hboundaryRange 0 := by
  let u : ℝ := (L.a + L.b) / 2
  have hu : u ∈ Set.Ioo L.a L.b := by
    dsimp only [u]
    constructor <;> linarith [L.hab]
  let q : UnitAddCircle :=
    controlledBoundaryChartParameter boundary P i u
  obtain ⟨j, hjNhds⟩ :=
    exists_activeAxisChart_activeSet_mem_nhds
      boundary hboundary hboundaryRange P₀ q
  have hqj : q ∈ controlledBoundaryChartActiveSet boundary P₀ j.1 :=
    mem_of_mem_nhds hjNhds
  let D : ControlledBoundaryDirectionCoverData boundary P₀ :=
    conventionalControlledBoundaryDirectionCoverData
      O boundary hboundary hboundaryRange P₀
  have hOverlap :
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P₀ j).toAxisLift.outwardBit
          (O.controlledChartSign (P₀.center j.1)) =
        L.outwardBit (O.controlledChartSign (P.center i)) :=
    ControlledBoundaryActiveAxisLift.toAxisLift_outwardBit_eq_of_axisLiftOverlap
      O boundary hboundary hboundaryRange P₀ j
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P₀ j)
      P i L q hqj u hu (by rfl)
  have hlocal : D.glueContinuous hboundary hboundaryRange q = D.bit j :=
    D.glueContinuous_apply_eq_bit hboundary hboundaryRange j q hqj
  have hglobal : D.glueContinuous hboundary hboundaryRange q =
      D.glueContinuous hboundary hboundaryRange 0 :=
    D.glueContinuous_apply_eq hboundary hboundaryRange q 0
  change L.outwardBit (O.controlledChartSign (P.center i)) =
    D.glueContinuous hboundary hboundaryRange 0
  calc
    L.outwardBit (O.controlledChartSign (P.center i)) =
        (conventionalControlledBoundaryActiveAxisLift
          boundary hboundary hboundaryRange P₀ j).toAxisLift.outwardBit
          (O.controlledChartSign (P₀.center j.1)) := hOverlap.symm
    _ = (conventionalControlledBoundaryActiveAxisLift
          boundary hboundary hboundaryRange P₀ j).outwardBit
          (O.controlledChartSign (P₀.center j.1)) :=
      (conventionalControlledBoundaryActiveAxisLift
        boundary hboundary hboundaryRange P₀ j).toAxisLift_outwardBit _
    _ = D.bit j := by
      simp only [D, conventionalControlledBoundaryDirectionCoverData_bit]
    _ = D.glueContinuous hboundary hboundaryRange q := hlocal.symm
    _ = D.glueContinuous hboundary hboundaryRange 0 := hglobal

#print axioms ControlledBoundaryAxisLift.outwardBit_eq_conventionalGlobalDirection

end

end GromovFilling
