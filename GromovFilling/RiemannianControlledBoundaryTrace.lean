import GromovFilling.RiemannianControlledBoundaryStokesData

/-!
# Genuine boundary traces for controlled weak-Stokes charts

The globally Lipschitz map used by chartwise weak Stokes agrees with the
genuine surface-map pullback on a closed outer half-ball.  At a boundary
point this is not an ambient neighborhood, but its restriction to the
imaginary axis is a neighborhood in the axis parameter.  This module uses
that relative neighborhood to identify the weak line derivative and the
boundary action density with the genuine chart pullback.

The result is still chart-local.  It deliberately does not identify the
increasing imaginary-axis parameter with a globally chosen oriented boundary
parametrization.
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

/-- The coordinatewise weak line derivative only depends on the germ of the
finite complex-valued map at the base point. -/
theorem finiteComplexWeakLineDerivative_eq_of_eventuallyEq
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] {F H : E → ι → ℂ} {x p : E}
    (h : F =ᶠ[nhds x] H) :
    finiteComplexWeakLineDerivative F x p =
      finiteComplexWeakLineDerivative H x p := by
  funext j
  apply Complex.ext
  · change lineDeriv ℝ (fun y ↦ (F y j).re) x p =
      lineDeriv ℝ (fun y ↦ (H y j).re) x p
    exact (h.mono fun _y hy ↦
      congrArg (fun v : ι → ℂ ↦ (v j).re) hy).lineDeriv_eq
  · change lineDeriv ℝ (fun y ↦ (F y j).im) x p =
      lineDeriv ℝ (fun y ↦ (H y j).im) x p
    exact (h.mono fun _y hy ↦
      congrArg (fun v : ι → ℂ ↦ (v j).im) hy).lineDeriv_eq

/-- At a nonzero boundary cutoff point, the extended chart map and the
genuine chart pullback agree on a neighborhood in the imaginary-axis
parameter.  No ambient equality across the manifold boundary is asserted. -/
theorem ControlledBoundaryChartWeakStokesData.chartMap_imaginaryAxis_eventuallyEq_of_cutoff_ne_zero
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {y : ℝ}
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    (fun t : ℝ ↦ D.chartMap (t * Complex.I)) =ᶠ[nhds y]
      fun t : ℝ ↦
        G (halfSpaceComplexExtChart (P.center i) (t * Complex.I)) := by
  have hyInner : (y * Complex.I : ℂ) ∈
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) :=
    support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
      P i ⟨hyCutoff, real_mul_I_mem_complexRightClosedHalfPlane y⟩
  have hyOuter : (y * Complex.I : ℂ) ∈
      ball (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceOuterRadius (P.center i)) :=
    closedBall_subset_ball
      (controlledHalfSpaceInnerRadius_lt_outer (P.center i)) hyInner
  have haxis : Continuous (fun t : ℝ ↦ (t * Complex.I : ℂ)) :=
    Complex.continuous_ofReal.mul continuous_const
  have hball : ∀ᶠ t in nhds y,
      (t * Complex.I : ℂ) ∈
        ball (controlledHalfSpaceComplexChartCenter (P.center i))
          (controlledHalfSpaceOuterRadius (P.center i)) :=
    haxis.continuousAt.eventually_mem (isOpen_ball.mem_nhds hyOuter)
  filter_upwards [hball] with t ht
  simpa only [Function.comp_apply] using D.chartMap_eq
    ⟨ball_subset_closedBall ht,
      real_mul_I_mem_complexRightClosedHalfPlane t⟩

/-- The weak derivative of the extended map along the imaginary axis is the
weak derivative of the genuine chart pullback wherever the cutoff is
nonzero. -/
theorem ControlledBoundaryChartWeakStokesData.axisWeakLineDerivative_eq_of_cutoff_ne_zero
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {y : ℝ}
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    finiteComplexWeakLineDerivative
        (fun t : ℝ ↦ D.chartMap (t * Complex.I)) y 1 =
      finiteComplexWeakLineDerivative
        (fun t : ℝ ↦
          G (halfSpaceComplexExtChart (P.center i) (t * Complex.I))) y 1 :=
  finiteComplexWeakLineDerivative_eq_of_eventuallyEq
    (D.chartMap_imaginaryAxis_eventuallyEq_of_cutoff_ne_zero hyCutoff)

/-- The chart-local boundary action formed directly from the genuine surface
map and the original controlled cutoff.  Its sign follows the increasing
imaginary-axis parameter; global boundary orientation is a later datum. -/
def controlledBoundaryChartActionDensity
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    {ι : Type uι} [Fintype ι] (G : M → ι → ℂ) (y : ℝ) : ℝ :=
  controlledBoundaryChartCutoff P i (y * Complex.I) *
    standardComplexSymplecticPrimitive
      (G (halfSpaceComplexExtChart (P.center i) (y * Complex.I)))
      (finiteComplexWeakLineDerivative
        (fun t : ℝ ↦
          G (halfSpaceComplexExtChart (P.center i) (t * Complex.I))) y 1)

/-- The boundary density appearing in Euclidean weak Stokes is exactly the
genuine chart boundary-action density. -/
theorem ControlledBoundaryChartWeakStokesData.boundaryActionDensity_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) (y : ℝ) :
    finiteComplexWeakBoundaryActionDensityComplex
        D.cutoff D.chartMap y =
      controlledBoundaryChartActionDensity P i G y := by
  by_cases hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) = 0
  · simp only [finiteComplexWeakBoundaryActionDensityComplex,
      controlledBoundaryChartActionDensity,
      D.cutoff_on_imaginaryAxis, hyCutoff, zero_mul]
  · simp only [finiteComplexWeakBoundaryActionDensityComplex,
      controlledBoundaryChartActionDensity]
    rw [D.cutoff_on_imaginaryAxis,
      D.chartMap_eq_of_cutoff_ne_zero
        (real_mul_I_mem_complexRightClosedHalfPlane y) hyCutoff,
      D.axisWeakLineDerivative_eq_of_cutoff_ne_zero
        hyCutoff]

/-- Hence the boundary integral in Euclidean weak Stokes can be replaced by
the genuine chart boundary-action integral without any regularity
assumption beyond the packaged Lipschitz data. -/
theorem ControlledBoundaryChartWeakStokesData.integral_boundaryActionDensity_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) :
    (∫ y : ℝ, finiteComplexWeakBoundaryActionDensityComplex
        D.cutoff D.chartMap y) =
      ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦
    D.boundaryActionDensity_eq y

/-- The weighted chart symplectic density formed from the original cutoff and
the genuine surface-map pullback. -/
def controlledBoundaryChartSymplecticDensity
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    {ι : Type uι} [Fintype ι] (G : M → ι → ℂ) (z : ℂ) : ℝ :=
  controlledBoundaryChartCutoff P i z *
    finiteSymplecticFDerivDensity
      (G ∘ halfSpaceComplexExtChart (P.center i)) z

/-- On the open half-plane, the weighted derivative density of the extended
map equals the weighted density of the genuine chart pullback.  The zero
cutoff case removes any need to compare derivatives outside the support. -/
theorem ControlledBoundaryChartWeakStokesData.weightedSymplecticDensity_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane) :
    D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z =
      controlledBoundaryChartSymplecticDensity P i G z := by
  have hzRightClosed : z ∈ complexRightClosedHalfPlane := by
    change 0 ≤ z.re
    change 0 < z.re at hzRight
    exact hzRight.le
  rw [controlledBoundaryChartSymplecticDensity,
    D.cutoff_eq hzRightClosed]
  by_cases hzCutoff : controlledBoundaryChartCutoff P i z = 0
  · simp only [hzCutoff, zero_mul]
  · rw [D.finiteSymplecticFDerivDensity_eq_of_cutoff_ne_zero
      hzRight hzCutoff]

/-- The open-half-plane integral can therefore be written entirely with the
original controlled cutoff and genuine chart pullback. -/
theorem ControlledBoundaryChartWeakStokesData.integral_weightedSymplecticDensity_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) :
    (∫ z in complexRightOpenHalfPlane,
        D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartSymplecticDensity P i G z := by
  apply integral_congr_ae
  filter_upwards
      [ae_restrict_mem isOpen_complexRightOpenHalfPlane.measurableSet] with z hz
  exact D.weightedSymplecticDensity_eq hz

/-- Chartwise weak Stokes with both the volume density and boundary action
identified with the genuine surface-map pullback.  Only the primitive-error
term still uses the globally Lipschitz extensions. -/
theorem ControlledBoundaryChartWeakStokesData.integral_controlledBoundaryChartSymplecticDensity_eq
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) :
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartSymplecticDensity P i G z) =
      (∫ z in complexRightOpenHalfPlane,
        finiteSymplecticFDerivPrimitiveError
          D.cutoff D.chartMap z) -
        ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  rw [← D.integral_weightedSymplecticDensity_eq,
    ← D.integral_boundaryActionDensity_eq]
  exact D.integral_eq

#print axioms finiteComplexWeakLineDerivative_eq_of_eventuallyEq
#print axioms
  ControlledBoundaryChartWeakStokesData.chartMap_imaginaryAxis_eventuallyEq_of_cutoff_ne_zero
#print axioms
  ControlledBoundaryChartWeakStokesData.axisWeakLineDerivative_eq_of_cutoff_ne_zero
#print axioms controlledBoundaryChartActionDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.boundaryActionDensity_eq
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_boundaryActionDensity_eq
#print axioms controlledBoundaryChartSymplecticDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.weightedSymplecticDensity_eq
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_weightedSymplecticDensity_eq
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_controlledBoundaryChartSymplecticDensity_eq

end

end GromovFilling
