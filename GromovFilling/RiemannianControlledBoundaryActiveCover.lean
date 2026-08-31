import GromovFilling.RiemannianControlledBoundaryAxisCoverage

/-!
# Active controlled boundary-chart covers

For a fixed finite controlled boundary partition, the nonzero loci of its
chart functions pull back along a boundary parametrization to an open cover
of the parameter circle.  Each active chart also has a single controlled
axis interval containing all of its nonzero trace.

This is the cover infrastructure needed to glue local boundary-direction
data.  It makes no orientation assertion.
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

/-- The indices of controlled chart cutoffs whose imaginary-axis trace is
not identically zero. -/
def FiniteControlledBoundaryChartPartition.activeAxisCharts
    (P : FiniteControlledBoundaryChartPartition M) : Type _ :=
  {i : P.ι // ∃ y : ℝ,
    controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0}

/-- The portion of the parameter circle on which one controlled chart is
active. -/
def controlledBoundaryChartActiveSet
    (boundary : UnitAddCircle → M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    Set UnitAddCircle :=
  {q | P.partition i (boundary q) ≠ 0}

/-- Each controlled chart's active parameter set is open whenever the
boundary parametrization is continuous. -/
theorem isOpen_controlledBoundaryChartActiveSet
    (boundary : UnitAddCircle → M) (hboundary : Continuous boundary)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    IsOpen (controlledBoundaryChartActiveSet boundary P i) := by
  change IsOpen
    ((fun q : UnitAddCircle ↦ P.partition i (boundary q)) ⁻¹'
      ({0}ᶜ : Set ℝ))
  exact isOpen_compl_singleton.preimage
    ((P.contMDiff_partition i).continuous.comp hboundary)

/-- Every parameter-circle point lies in the open active set of some chart
whose axis trace is nonzero. -/
theorem exists_activeAxisChart_activeSet_mem_nhds
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M)
    (q : UnitAddCircle) :
    ∃ i : P.activeAxisCharts,
      controlledBoundaryChartActiveSet boundary P i.1 ∈ 𝓝 q := by
  obtain ⟨i, hi⟩ := P.exists_partition_ne_zero (boundary q)
  obtain ⟨y, _hyDomain, _hyParameter, hyCutoff⟩ :=
    exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
      boundary hboundary hboundaryRange P i q hi
  refine ⟨⟨i, ⟨y, hyCutoff⟩⟩, ?_⟩
  apply (isOpen_controlledBoundaryChartActiveSet
    boundary hboundary.lipschitzWith.continuous P i).mem_nhds
  exact hi

/-- Every active chart has one closed real interval lying in its controlled
domain and containing every nonzero coordinate-cutoff value in its open
interior. -/
theorem FiniteControlledBoundaryChartPartition.exists_axisInterval_of_active
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.activeAxisCharts) :
    ∃ a b : ℝ, a < b ∧
      (∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
        chosenControlledHalfSpaceComplexChartDomain (P.center i.1)) ∧
      (∀ y ∉ Set.Ioo a b,
        controlledBoundaryChartCutoff P i.1 (y * Complex.I) = 0) := by
  rcases all_zero_or_exists_controlledBoundaryChartAxisInterval P i.1 with
      hzero | ⟨a, b, hab, hdomain, houtside⟩
  · obtain ⟨y, hy⟩ := i.2
    exact (hy (hzero y)).elim
  · exact ⟨a, b, hab, hdomain, houtside⟩

/-- A point of an active chart's parameter set has a controlled imaginary
axis coordinate for that chart. -/
theorem exists_axisCoordinate_of_mem_controlledBoundaryChartActiveSet
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (q : UnitAddCircle)
    (hq : q ∈ controlledBoundaryChartActiveSet boundary P i) :
    ∃ y : ℝ,
      (y * Complex.I : ℂ) ∈
        chosenControlledHalfSpaceComplexChartDomain (P.center i) ∧
      controlledBoundaryChartParameter boundary P i y = q ∧
      controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0 := by
  exact exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
    boundary hboundary hboundaryRange P i q hq

#print axioms FiniteControlledBoundaryChartPartition.activeAxisCharts
#print axioms controlledBoundaryChartActiveSet
#print axioms isOpen_controlledBoundaryChartActiveSet
#print axioms exists_activeAxisChart_activeSet_mem_nhds
#print axioms FiniteControlledBoundaryChartPartition.exists_axisInterval_of_active
#print axioms exists_axisCoordinate_of_mem_controlledBoundaryChartActiveSet

end

end GromovFilling
