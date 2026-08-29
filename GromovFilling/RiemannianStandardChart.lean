import GromovFilling.RiemannianChartTransition
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Standard complex-chart interfaces for Riemannian area

This file instantiates the topological and differentiability hypotheses of
the chart-transition theorem for ordinary boundaryless complex charts.  It
also proves the local almost-everywhere measurability facts for the inverse
chart maps themselves.

Measurability of the intrinsic Jacobian densities is deliberately left as a
separate interface, as are charts modeled on a half-space at the boundary.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

/-- The target of an extended chart in the boundaryless complex model is a
measurable open subset of the complex plane. -/
theorem measurableSet_extChartAt_target_complex
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (x : M) :
    MeasurableSet (extChartAt 𝓘(ℝ, ℂ) x).target :=
  (isOpen_extChartAt_target x).measurableSet

/-- A standard inverse complex chart is almost everywhere measurable on its
own coordinate target. -/
theorem aemeasurable_extChartAt_symm_complex
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [ChartedSpace ℂ M] (x : M) :
    AEMeasurable (extChartAt 𝓘(ℝ, ℂ) x).symm
      (volume.restrict (extChartAt 𝓘(ℝ, ℂ) x).target) :=
  (continuousOn_extChartAt_symm x).aemeasurable
    (measurableSet_extChartAt_target_complex x)

/-- A standard inverse complex chart is manifold-differentiable at every
point of its coordinate target. -/
theorem mdifferentiableAt_extChartAt_symm_complex
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) 1 M] (x : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x).target) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (extChartAt 𝓘(ℝ, ℂ) x).symm z := by
  have h := mdifferentiableWithinAt_extChartAt_symm hz
  simpa only [ModelWithCorners.range_eq_univ,
    mdifferentiableWithinAt_univ] using h

/-- The ordinary coordinate change from the chart at `x'` to the chart at
`x`. -/
def complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) : ℂ → ℂ :=
  extChartAt 𝓘(ℝ, ℂ) x ∘ (extChartAt 𝓘(ℝ, ℂ) x').symm

/-- The maximal source on which the coordinate change from `x'` to `x` is a
partial equivalence. -/
def complexExtCoordChangeSource
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) : Set ℂ :=
  ((extChartAt 𝓘(ℝ, ℂ) x').symm ≫
    extChartAt 𝓘(ℝ, ℂ) x).source

/-- The source of an ordinary complex coordinate change is open. -/
theorem isOpen_complexExtCoordChangeSource
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) : IsOpen (complexExtCoordChangeSource x x') := by
  rw [complexExtCoordChangeSource, ext_coord_change_source]
  simpa only [modelWithCornersSelf_coe, Set.image_id] using
    ((chartAt ℂ x').symm ≫ₕ chartAt ℂ x).open_source

/-- The source of an ordinary complex coordinate change is measurable. -/
theorem measurableSet_complexExtCoordChangeSource
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) : MeasurableSet (complexExtCoordChangeSource x x') :=
  (isOpen_complexExtCoordChangeSource x x').measurableSet

/-- An ordinary complex coordinate change is injective on its maximal
source. -/
theorem injOn_complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) :
    Set.InjOn (complexExtCoordChange x x')
      (complexExtCoordChangeSource x x') :=
  (((extChartAt 𝓘(ℝ, ℂ) x').symm ≫
    extChartAt 𝓘(ℝ, ℂ) x)).injOn

/-- The image of a coordinate-change source is exactly the source of the
reverse coordinate change. -/
theorem image_complexExtCoordChangeSource
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) :
    complexExtCoordChange x x' '' complexExtCoordChangeSource x x' =
      complexExtCoordChangeSource x' x := by
  exact (((extChartAt 𝓘(ℝ, ℂ) x').symm ≫
    extChartAt 𝓘(ℝ, ℂ) x)).image_source_eq_target

/-- A complex coordinate change is continuously differentiable on its
maximal source. -/
theorem contDiffOn_complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) 1 M] (x x' : M) :
    ContDiffOn ℝ 1 (complexExtCoordChange x x')
      (complexExtCoordChangeSource x x') :=
  contDiffOn_ext_coord_change x x'

/-- A complex coordinate change is differentiable at every point of its
maximal source. -/
theorem differentiableAt_complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) 1 M] (x x' : M) {z : ℂ}
    (hz : z ∈ complexExtCoordChangeSource x x') :
    DifferentiableAt ℝ (complexExtCoordChange x x') z := by
  exact ((contDiffOn_complexExtCoordChange x x' z hz).differentiableWithinAt
      one_ne_zero).differentiableAt
    ((isOpen_complexExtCoordChangeSource x x').mem_nhds hz)

/-- A complex coordinate change is almost everywhere measurable on its
maximal source. -/
theorem aemeasurable_complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℝ, ℂ) 1 M] (x x' : M) :
    AEMeasurable (complexExtCoordChange x x')
      (volume.restrict (complexExtCoordChangeSource x x')) :=
  (contDiffOn_complexExtCoordChange x x').continuousOn.aemeasurable
    (measurableSet_complexExtCoordChangeSource x x')

/-- On the coordinate-change source, applying the old inverse chart after
the transition recovers the new inverse chart. -/
theorem extChartAt_symm_comp_complexExtCoordChange
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (x x' : M) {z : ℂ}
    (hz : z ∈ complexExtCoordChangeSource x x') :
    (extChartAt 𝓘(ℝ, ℂ) x).symm (complexExtCoordChange x x' z) =
      (extChartAt 𝓘(ℝ, ℂ) x').symm z := by
  change z ∈ ((extChartAt 𝓘(ℝ, ℂ) x').symm ≫
    extChartAt 𝓘(ℝ, ℂ) x).source at hz
  change (extChartAt 𝓘(ℝ, ℂ) x).symm
      ((extChartAt 𝓘(ℝ, ℂ) x)
        ((extChartAt 𝓘(ℝ, ℂ) x').symm z)) =
    (extChartAt 𝓘(ℝ, ℂ) x').symm z
  exact (extChartAt 𝓘(ℝ, ℂ) x).left_inv hz.2

end

end GromovFilling
