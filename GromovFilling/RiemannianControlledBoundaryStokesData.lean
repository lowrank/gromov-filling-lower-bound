import GromovFilling.FiniteSymplecticPrimitiveTransition
import GromovFilling.RiemannianControlledBoundaryMapExtension

/-!
# Weak-Stokes data for controlled boundary charts

The controlled partition leaves enough chart annulus to extend both a cutoff
and a finite complex-valued surface map to globally Lipschitz Euclidean data.
This module packages those two extensions and applies the verified half-plane
weak-Stokes theorem to each chart.

This remains a local statement.  In particular, it does not assume a global
orientation convention or identify the sum of imaginary-axis traces with the
oriented boundary action of the surface.
-/

open Bundle Function Manifold MeasureTheory Metric Set
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

/-- The globally Lipschitz Euclidean extensions used to apply weak Stokes in
one controlled boundary chart. -/
structure ControlledBoundaryChartWeakStokesData
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    {ι : Type uι} [Fintype ι] (G : M → ι → ℂ) where
  cutoffConstant : ℝ≥0
  cutoff : ℂ → ℝ
  cutoff_lipschitz : LipschitzWith cutoffConstant cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_eq : EqOn cutoff (controlledBoundaryChartCutoff P i)
    complexRightClosedHalfPlane
  cutoff_nonneg : ∀ z, 0 ≤ cutoff z
  cutoff_le_one : ∀ z, cutoff z ≤ 1
  mapConstant : ℝ≥0
  chartMap : ℂ → ι → ℂ
  chartMap_lipschitz : LipschitzWith mapConstant chartMap
  chartMap_eq : EqOn chartMap
    (G ∘ halfSpaceComplexExtChart (P.center i))
    (controlledHalfSpaceOuterClosedHalfBall (P.center i))

/-- Every controlled chart and globally Lipschitz finite complex surface map
has the extension data required by half-plane weak Stokes. -/
theorem nonempty_controlledBoundaryChartWeakStokesData
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (G : M → ι → ℂ) {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    Nonempty (ControlledBoundaryChartWeakStokesData P i G) := by
  obtain ⟨Cρ, ρ, hρ, hρCompact, hρEq, hρNonneg, hρLe⟩ :=
    exists_controlledBoundaryChartCutoffExtension P i
  obtain ⟨CF, F, hF, hFEq⟩ :=
    exists_controlledBoundaryChartMapExtension G hG (P.center i)
  exact ⟨{
    cutoffConstant := Cρ
    cutoff := ρ
    cutoff_lipschitz := hρ
    cutoff_compact := hρCompact
    cutoff_eq := hρEq
    cutoff_nonneg := hρNonneg
    cutoff_le_one := hρLe
    mapConstant := CF
    chartMap := F
    chartMap_lipschitz := hF
    chartMap_eq := hFEq
  }⟩

/-- Every point of the imaginary axis belongs to the closed right
half-plane. -/
theorem real_mul_I_mem_complexRightClosedHalfPlane (y : ℝ) :
    (y * Complex.I : ℂ) ∈ complexRightClosedHalfPlane := by
  change 0 ≤ (y * Complex.I : ℂ).re
  simp

/-- The inner closed support half-ball is contained in the outer closed
half-ball, including on the boundary axis. -/
theorem controlledHalfSpaceInnerClosedBall_inter_rightClosed_subset_outerClosed
    (x : M) :
    closedBall (controlledHalfSpaceComplexChartCenter x)
          (controlledHalfSpaceInnerRadius x) ∩
        complexRightClosedHalfPlane ⊆
      controlledHalfSpaceOuterClosedHalfBall x := by
  rintro z ⟨hzBall, hzRight⟩
  refine ⟨?_, hzRight⟩
  rw [mem_closedBall] at hzBall ⊢
  exact hzBall.trans
    (controlledHalfSpaceInnerRadius_lt_outer x).le

/-- The extended cutoff has exactly the original chart cutoff on the
imaginary-axis boundary trace. -/
theorem ControlledBoundaryChartWeakStokesData.cutoff_on_imaginaryAxis
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) (y : ℝ) :
    D.cutoff (y * Complex.I) =
      controlledBoundaryChartCutoff P i (y * Complex.I) :=
  D.cutoff_eq (real_mul_I_mem_complexRightClosedHalfPlane y)

/-- Wherever the original controlled cutoff is nonzero in the closed
half-plane, the extended finite map agrees with the genuine chart pullback. -/
theorem ControlledBoundaryChartWeakStokesData.chartMap_eq_of_cutoff_ne_zero
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hzRight : z ∈ complexRightClosedHalfPlane)
    (hzCutoff : controlledBoundaryChartCutoff P i z ≠ 0) :
    D.chartMap z = G (halfSpaceComplexExtChart (P.center i) z) := by
  have hzInner : z ∈
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) :=
    support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
      P i ⟨hzCutoff, hzRight⟩
  have hzOuter : z ∈
      controlledHalfSpaceOuterClosedHalfBall (P.center i) :=
    controlledHalfSpaceInnerClosedBall_inter_rightClosed_subset_outerClosed
      (P.center i) ⟨hzInner, hzRight⟩
  simpa only [Function.comp_apply] using D.chartMap_eq hzOuter

/-- In the open half-plane part of the inverse-chart domain, the extended
cutoff agrees locally with the genuine partition function in surface
coordinates. -/
theorem ControlledBoundaryChartWeakStokesData.cutoff_eventuallyEq_partition
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hz : z ∈ halfSpaceComplexExtChartDomain (P.center i) ∩
      complexRightOpenHalfPlane) :
    D.cutoff =ᶠ[𝓝 z]
      P.partition i ∘ halfSpaceComplexExtChart (P.center i) := by
  filter_upwards
      [(isOpen_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
        (P.center i)).mem_nhds hz] with w hw
  rw [D.cutoff_eq
      (halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane
        (P.center i) hw.1),
    controlledBoundaryChartCutoff_eq_of_mem P i hw.1]
  rfl

/-- A nonzero cutoff point lies in the annular margin where the extended
finite map agrees locally with the genuine chart pullback. -/
theorem ControlledBoundaryChartWeakStokesData.chartMap_eventuallyEq_of_cutoff_ne_zero
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzCutoff : controlledBoundaryChartCutoff P i z ≠ 0) :
    D.chartMap =ᶠ[𝓝 z]
      G ∘ halfSpaceComplexExtChart (P.center i) := by
  have hzRightClosed : z ∈ complexRightClosedHalfPlane := by
    change 0 ≤ z.re
    change 0 < z.re at hzRight
    exact hzRight.le
  have hzInner : z ∈
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) :=
    support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
      P i ⟨hzCutoff, hzRightClosed⟩
  have hzOuter : z ∈
      controlledHalfSpaceOuterOpenHalfBall (P.center i) :=
    controlledHalfSpaceInnerClosedBall_inter_rightOpen_subset_outerOpen
      (P.center i) ⟨hzInner, hzRight⟩
  filter_upwards
      [(isOpen_controlledHalfSpaceOuterOpenHalfBall
        (P.center i)).mem_nhds hzOuter] with w hw
  exact D.chartMap_eq
    (controlledHalfSpaceOuterOpenHalfBall_subset_closed
      (P.center i) hw)

/-- Local equality of cutoff extensions gives equality of their ordinary
Fréchet derivatives at interior chart points. -/
theorem ControlledBoundaryChartWeakStokesData.fderiv_cutoff_eq_partition
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hz : z ∈ halfSpaceComplexExtChartDomain (P.center i) ∩
      complexRightOpenHalfPlane) :
    fderiv ℝ D.cutoff z =
      fderiv ℝ
        (P.partition i ∘ halfSpaceComplexExtChart (P.center i)) z :=
  (D.cutoff_eventuallyEq_partition hz).fderiv_eq

/-- Wherever the cutoff is nonzero, the derivative density of the extended
map is the derivative density of the genuine surface-map pullback. -/
theorem ControlledBoundaryChartWeakStokesData.finiteSymplecticFDerivDensity_eq_of_cutoff_ne_zero
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzCutoff : controlledBoundaryChartCutoff P i z ≠ 0) :
    finiteSymplecticFDerivDensity D.chartMap z =
      finiteSymplecticFDerivDensity
        (G ∘ halfSpaceComplexExtChart (P.center i)) z := by
  unfold finiteSymplecticFDerivDensity
  rw [(D.chartMap_eventuallyEq_of_cutoff_ne_zero
    hzRight hzCutoff).fderiv_eq]

/-- The packaged extensions satisfy localized weak Stokes on the complex
right half-plane, with the increasing-imaginary-axis boundary convention. -/
theorem ControlledBoundaryChartWeakStokesData.integral_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) :
    (∫ z in complexRightOpenHalfPlane,
        D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z) =
      (∫ z in complexRightOpenHalfPlane,
        finiteSymplecticFDerivPrimitiveError
          D.cutoff D.chartMap z) -
        ∫ y : ℝ,
          finiteComplexWeakBoundaryActionDensityComplex
            D.cutoff D.chartMap y :=
  integral_complexRightHalfPlane_cutoff_mul_finiteSymplecticFDerivDensity_eq
    D.cutoff_lipschitz D.cutoff_compact D.chartMap_lipschitz

#print axioms nonempty_controlledBoundaryChartWeakStokesData
#print axioms real_mul_I_mem_complexRightClosedHalfPlane
#print axioms
  controlledHalfSpaceInnerClosedBall_inter_rightClosed_subset_outerClosed
#print axioms
  ControlledBoundaryChartWeakStokesData.cutoff_on_imaginaryAxis
#print axioms
  ControlledBoundaryChartWeakStokesData.chartMap_eq_of_cutoff_ne_zero
#print axioms
  ControlledBoundaryChartWeakStokesData.cutoff_eventuallyEq_partition
#print axioms
  ControlledBoundaryChartWeakStokesData.chartMap_eventuallyEq_of_cutoff_ne_zero
#print axioms
  ControlledBoundaryChartWeakStokesData.fderiv_cutoff_eq_partition
#print axioms
  ControlledBoundaryChartWeakStokesData.finiteSymplecticFDerivDensity_eq_of_cutoff_ne_zero
#print axioms ControlledBoundaryChartWeakStokesData.integral_eq

end

end GromovFilling
