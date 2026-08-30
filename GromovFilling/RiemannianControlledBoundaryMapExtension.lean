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

/-- The closed inner support half-ball is contained in the controlled
interior chart domain away from the boundary axis.  This is the common
domain on which planar Rademacher can be transferred back to the surface. -/
theorem controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_chosenInteriorDomain
    (x : M) :
    closedBall (controlledHalfSpaceComplexChartCenter x)
          (controlledHalfSpaceInnerRadius x) ∩
        complexRightOpenHalfPlane ⊆
      chosenControlledInteriorComplexChartDomain
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr x := by
  rintro z ⟨hzBall, hzRight⟩
  rw [chosenControlledInteriorComplexChartDomain,
    controlledInteriorComplexChartDomain, controlledInteriorChartSet]
  refine ⟨?_, ?_⟩
  · rw [mem_ball]
    have hdist :
        dist (Complex.orthonormalBasisOneI.repr z)
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x) =
          dist z (controlledHalfSpaceComplexChartCenter x) := by
      simpa only [controlledHalfSpaceComplexChartCenter,
        LinearIsometryEquiv.apply_symm_apply] using
        Complex.orthonormalBasisOneI.repr.dist_map z
          (controlledHalfSpaceComplexChartCenter x)
    rw [hdist]
    exact lt_of_le_of_lt (mem_closedBall.mp hzBall)
      (half_lt_self
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) x).r_pos)
  · rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa only [complexRightOpenHalfPlane,
      Complex.orthonormalBasisOneI_repr_apply] using hzRight

/-- The nonzero part of a controlled cutoff in the open half-plane lies in
the controlled interior chart domain used by the canonical atlas. -/
theorem support_controlledBoundaryChartCutoff_inter_rightOpen_subset_chosenInteriorDomain
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    support (controlledBoundaryChartCutoff P i) ∩
        complexRightOpenHalfPlane ⊆
      chosenControlledInteriorComplexChartDomain
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr (P.center i) := by
  rintro z ⟨hzSupport, hzRight⟩
  apply
    controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_chosenInteriorDomain
      (P.center i)
  refine ⟨support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
    P i ⟨hzSupport, ?_⟩, hzRight⟩
  change 0 ≤ z.re
  change 0 < z.re at hzRight
  exact hzRight.le

/-- Hence a controlled cutoff vanishes at every open-half-plane point
outside its controlled interior chart domain. -/
theorem controlledBoundaryChartCutoff_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzDomain : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    controlledBoundaryChartCutoff P i z = 0 := by
  by_contra hz
  exact hzDomain
    (support_controlledBoundaryChartCutoff_inter_rightOpen_subset_chosenInteriorDomain
      P i ⟨hz, hzRight⟩)

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
  controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_chosenInteriorDomain
#print axioms
  support_controlledBoundaryChartCutoff_inter_rightOpen_subset_chosenInteriorDomain
#print axioms
  controlledBoundaryChartCutoff_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  lipschitzOnWith_controlledBoundaryChartMap_outerClosedHalfBall
#print axioms exists_controlledBoundaryChartMapExtension

end

end GromovFilling
