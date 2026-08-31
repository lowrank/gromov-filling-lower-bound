import GromovFilling.RiemannianControlledBoundaryAxisSupport

/-!
# Boundary-chart support is covered by the imaginary axis

A point in the controlled half-space chart maps to the manifold boundary
only when its complex coordinate has zero real part.  Consequently every
nonzero value of a controlled partition function on the boundary has a
controlled imaginary-axis coordinate.  This supplies the converse to the
axis-to-boundary identities and is the support bridge needed to remove the
unused arc in a local phase substitution.
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

/-- A coordinate in a half-space extended chart maps to a manifold-boundary
point only if it lies on the imaginary axis. -/
theorem eq_im_mul_I_of_mem_halfSpaceComplexExtChartDomain_of_image_mem_boundary
    (x : M) {z : ℂ}
    (hzDomain : z ∈ halfSpaceComplexExtChartDomain x)
    (hzBoundary : halfSpaceComplexExtChart x z ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary M) :
    z = z.im * Complex.I := by
  have hzRightClosed :=
    halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane x hzDomain
  change 0 ≤ z.re at hzRightClosed
  have hzRe : z.re = 0 := by
    by_contra hzRe
    have hzRePos : 0 < z.re :=
      lt_of_le_of_ne hzRightClosed hzRe.symm
    have hzRightOpen : z ∈ complexRightOpenHalfPlane := by
      exact hzRePos
    have hzImage : halfSpaceComplexExtChart x z ∈
        halfSpaceComplexExtChart x ''
          (halfSpaceComplexExtChartDomain x ∩
            complexRightOpenHalfPlane) :=
      ⟨z, ⟨hzDomain, hzRightOpen⟩, rfl⟩
    rw [image_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane x]
      at hzImage
    exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint
      (I := modelWithCornersEuclideanHalfSpace 2)
      (halfSpaceComplexExtChart x z)).mp hzBoundary hzImage.2
  apply Complex.ext
  · simpa only [Complex.mul_I_re, Complex.ofReal_im, neg_zero] using hzRe
  · simp only [Complex.mul_I_im, Complex.ofReal_re]

/-- Every nonzero boundary value of a controlled partition function is
realized by a controlled imaginary-axis coordinate, with the same canonical
circle parameter and a nonzero coordinate cutoff. -/
theorem exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (q : UnitAddCircle) (hq : P.partition i (boundary q) ≠ 0) :
    ∃ y : ℝ,
      (y * Complex.I : ℂ) ∈
        chosenControlledHalfSpaceComplexChartDomain (P.center i) ∧
      controlledBoundaryChartParameter boundary P i y = q ∧
      controlledBoundaryChartCutoff P i (y * Complex.I) ≠ 0 := by
  have hsupport : boundary q ∈ tsupport (P.partition i) :=
    subset_tsupport (P.partition i) hq
  have himage :=
    P.tsupport_partition_subset_controlledHalfSpace_image i hsupport
  obtain ⟨z, hzDomain, hzChart⟩ := himage
  have hzBoundary : halfSpaceComplexExtChart (P.center i) z ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
    rw [← hboundaryRange]
    exact ⟨q, hzChart.symm⟩
  have hzAxis : z = z.im * Complex.I :=
    eq_im_mul_I_of_mem_halfSpaceComplexExtChartDomain_of_image_mem_boundary
      (P.center i)
      (controlledHalfSpaceComplexChartDomain_subset_domain
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) (P.center i)) hzDomain)
      hzBoundary
  rw [hzAxis] at hzDomain hzChart
  have hparameter :
      controlledBoundaryChartParameter boundary P i z.im = q := by
    apply hboundary.injective
    calc
      boundary (controlledBoundaryChartParameter boundary P i z.im) =
          halfSpaceComplexExtChart (P.center i) (z.im * Complex.I) :=
        boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
          boundary hboundaryRange P i z.im hzDomain
      _ = boundary q := hzChart
  have hcutoff :
      controlledBoundaryChartCutoff P i (z.im * Complex.I) ≠ 0 := by
    rw [controlledBoundaryChartCutoff_eq_boundary_partition_parameter_of_mem_controlledDomain
      boundary hboundaryRange P i z.im hzDomain, hparameter]
    exact hq
  exact ⟨z.im, hzDomain, hparameter, hcutoff⟩

/-- If a controlled cutoff vanishes along its entire imaginary-axis trace,
then its partition function vanishes on the whole parametrized manifold
boundary. -/
theorem boundary_partition_eq_zero_of_controlledBoundaryChartCutoff_axis_eq_zero
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (hzero : ∀ y : ℝ,
      controlledBoundaryChartCutoff P i (y * Complex.I) = 0) :
    ∀ q : UnitAddCircle, P.partition i (boundary q) = 0 := by
  intro q
  by_contra hq
  obtain ⟨y, _hyDomain, _hyParameter, hyCutoff⟩ :=
    exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
      boundary hboundary hboundaryRange P i q hq
  exact hyCutoff (hzero y)

#print axioms
  eq_im_mul_I_of_mem_halfSpaceComplexExtChartDomain_of_image_mem_boundary
#print axioms
  exists_controlledBoundaryChartAxisCoordinate_of_partition_ne_zero
#print axioms
  boundary_partition_eq_zero_of_controlledBoundaryChartCutoff_axis_eq_zero

end

end GromovFilling
