import GromovFilling.RiemannianControlledBoundaryCutoff

/-!
# Lipschitz extensions of controlled boundary-chart maps

The half-plane weak-Stokes theorem expects a globally Lipschitz Euclidean
map.  A globally Lipschitz map on the surface becomes Lipschitz on each
controlled inverse chart, and finite-dimensional Kirszbraun extension then
continues that pullback to the whole complex plane.  The extension agrees on
the outer closed half-ball, which contains the cutoff support with a strict
annular margin and also retains the imaginary-axis boundary trace.
-/

open Bundle Function Manifold Metric Set
open scoped ContDiff Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- The open part of the outer controlled half-ball.  This is the region on
which equality of extensions gives equality of ordinary derivatives. -/
def controlledHalfSpaceOuterOpenHalfBall (x : M) : Set ℂ :=
  ball (controlledHalfSpaceComplexChartCenter x)
      (controlledHalfSpaceOuterRadius x) ∩
    complexRightOpenHalfPlane

theorem isOpen_complexRightOpenHalfPlane :
    IsOpen complexRightOpenHalfPlane := by
  simpa only [complexRightOpenHalfPlane] using
    isOpen_lt
      (continuous_const : Continuous (fun _ : ℂ ↦ (0 : ℝ)))
      Complex.continuous_re

theorem isOpen_controlledHalfSpaceOuterOpenHalfBall (x : M) :
    IsOpen (controlledHalfSpaceOuterOpenHalfBall x) :=
  isOpen_ball.inter isOpen_complexRightOpenHalfPlane

theorem controlledHalfSpaceOuterOpenHalfBall_subset_closed (x : M) :
    controlledHalfSpaceOuterOpenHalfBall x ⊆
      controlledHalfSpaceOuterClosedHalfBall x := by
  rintro z ⟨hzBall, hzRight⟩
  refine ⟨mem_closedBall.mpr (mem_ball.mp hzBall).le, ?_⟩
  change 0 ≤ z.re
  change 0 < z.re at hzRight
  exact hzRight.le

/-- The closed inner support half-ball lies strictly inside the open outer
half-ball away from the boundary axis. -/
theorem controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_outerOpen
    (x : M) :
    closedBall (controlledHalfSpaceComplexChartCenter x)
          (controlledHalfSpaceInnerRadius x) ∩
        complexRightOpenHalfPlane ⊆
      controlledHalfSpaceOuterOpenHalfBall x := by
  rintro z ⟨hzBall, hzRight⟩
  refine ⟨?_, hzRight⟩
  rw [mem_ball]
  exact lt_of_le_of_lt (mem_closedBall.mp hzBall)
    (controlledHalfSpaceInnerRadius_lt_outer x)

/-- Pulling a globally Lipschitz finite complex map back through a controlled
inverse boundary chart is Lipschitz on the outer closed half-ball. -/
theorem lipschitzOnWith_controlledBoundaryChartMap_outerClosedHalfBall
    {ι : Type uι} [Fintype ι]
    (G : M → ι → ℂ) {CG : ℝ≥0} (hG : LipschitzWith CG G) (x : M) :
    LipschitzOnWith
      (CG * (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x).C)
      (G ∘ halfSpaceComplexExtChart x)
      (controlledHalfSpaceOuterClosedHalfBall x) := by
  exact (hG.comp_lipschitzOnWith
    (lipschitzOnWith_controlledHalfSpaceComplexChart
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x))).mono
    (controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain x)

/-- Every controlled boundary-chart pullback of a globally Lipschitz finite
complex map has a global Lipschitz extension agreeing on the full outer
closed half-ball. -/
theorem exists_controlledBoundaryChartMapExtension
    {ι : Type uι} [Fintype ι]
    (G : M → ι → ℂ) {CG : ℝ≥0} (hG : LipschitzWith CG G) (x : M) :
    ∃ C : ℝ≥0, ∃ F : ℂ → ι → ℂ,
      LipschitzWith C F ∧
        EqOn F (G ∘ halfSpaceComplexExtChart x)
          (controlledHalfSpaceOuterClosedHalfBall x) := by
  obtain ⟨F, hF, hEq⟩ :=
    (lipschitzOnWith_controlledBoundaryChartMap_outerClosedHalfBall
      G hG x).extend_finite_dimension
  exact ⟨_, F, hF, hEq.symm⟩

#print axioms controlledHalfSpaceOuterOpenHalfBall_subset_closed
#print axioms
  controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_outerOpen
#print axioms
  lipschitzOnWith_controlledBoundaryChartMap_outerClosedHalfBall
#print axioms exists_controlledBoundaryChartMapExtension

end

end GromovFilling
