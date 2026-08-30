import GromovFilling.ComplexHalfPlaneWeakStokes
import GromovFilling.RiemannianInteriorChart

/-!
# Complex coordinates for two-dimensional manifold-with-boundary charts

Mathlib models a two-dimensional manifold with boundary on the Euclidean
half-space whose zeroth coordinate is nonnegative.  The standard complex
orthonormal basis identifies this model exactly with the closed complex
right half-plane.  This file packages the inverse extended chart in those
complex coordinates and records the basic domain, image, smoothness, and
injectivity facts needed by chartwise weak Stokes.
-/

open Bundle Function Manifold Set
open scoped Manifold

namespace GromovFilling

noncomputable section

/-- The closed complex right half-plane underlying Mathlib's two-dimensional
manifold-with-boundary model. -/
def complexRightClosedHalfPlane : Set ℂ :=
  {z | 0 ≤ z.re}

/-- The coordinate domain of the inverse extended chart, expressed in the
standard complex orthonormal coordinates. -/
def halfSpaceComplexExtChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) : Set ℂ :=
  Complex.orthonormalBasisOneI.repr ⁻¹'
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target

/-- The inverse extended chart in standard complex coordinates. -/
def halfSpaceComplexExtChart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) : ℂ → M :=
  (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm ∘
    Complex.orthonormalBasisOneI.repr

@[simp] theorem mem_halfSpaceComplexExtChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) (z : ℂ) :
    z ∈ halfSpaceComplexExtChartDomain x ↔
      Complex.orthonormalBasisOneI.repr z ∈
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target :=
  Iff.rfl

/-- Every boundary-chart coordinate lies in the closed right half-plane. -/
theorem halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    halfSpaceComplexExtChartDomain x ⊆ complexRightClosedHalfPlane := by
  intro z hz
  have hzrange : Complex.orthonormalBasisOneI.repr z ∈
      Set.range (modelWithCornersEuclideanHalfSpace 2) :=
    extChartAt_target_subset_range x hz
  rw [range_modelWithCornersEuclideanHalfSpace] at hzrange
  simpa [complexRightClosedHalfPlane,
    Complex.orthonormalBasisOneI_repr_apply] using hzrange

/-- The complex inverse chart is continuous on its coordinate domain. -/
theorem continuousOn_halfSpaceComplexExtChart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    ContinuousOn (halfSpaceComplexExtChart x)
      (halfSpaceComplexExtChartDomain x) := by
  apply (continuousOn_extChartAt_symm x).comp
    Complex.orthonormalBasisOneI.repr.continuous.continuousOn
  intro z hz
  exact hz

/-- The complex inverse chart is manifold-smooth on its coordinate domain. -/
theorem contMDiffOn_halfSpaceComplexExtChart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] (x : M) :
    ContMDiffOn 𝓘(ℝ, ℂ) (modelWithCornersEuclideanHalfSpace 2) 1
      (halfSpaceComplexExtChart x) (halfSpaceComplexExtChartDomain x) := by
  apply (contMDiffOn_extChartAt_symm x).comp
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn
  intro z hz
  exact hz

/-- The inverse chart is injective on its complex coordinate domain. -/
theorem injOn_halfSpaceComplexExtChart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    Set.InjOn (halfSpaceComplexExtChart x)
      (halfSpaceComplexExtChartDomain x) := by
  intro z hz w hw hzw
  apply Complex.orthonormalBasisOneI.repr.injective
  exact (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm.injOn
    hz hw hzw

/-- The complex inverse-chart domain maps onto the full ordinary chart
source, including both interior and boundary points. -/
theorem image_halfSpaceComplexExtChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    halfSpaceComplexExtChart x '' halfSpaceComplexExtChartDomain x =
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).source := by
  rw [halfSpaceComplexExtChart, halfSpaceComplexExtChartDomain,
    Set.image_comp,
    Set.image_preimage_eq _
      Complex.orthonormalBasisOneI.repr.surjective,
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm_image_target_eq_source]

#print axioms halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane
#print axioms continuousOn_halfSpaceComplexExtChart
#print axioms contMDiffOn_halfSpaceComplexExtChart
#print axioms injOn_halfSpaceComplexExtChart
#print axioms image_halfSpaceComplexExtChartDomain

end

end GromovFilling
