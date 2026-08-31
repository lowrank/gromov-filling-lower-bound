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

open Bundle Filter Function Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

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

/-- The interior of an extended-chart target is exactly the part of that
target lying in the interior of the model range.  Extended-chart targets
need not be open for manifolds with boundary, so this relative-interior
identity is the correct bridge to ordinary open coordinate domains. -/
theorem interior_extChartAt_target_eq_inter_interior_range
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    interior (extChartAt I x).target =
      (extChartAt I x).target ∩ interior (Set.range I) := by
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨interior_subset hy,
      interior_mono (extChartAt_target_subset_range x) hy⟩
  · rintro y ⟨hyTarget, hyInterior⟩
    exact (extChartAt_target_eventuallyEq_of_mem hyTarget).symm.mem_interior
      hyInterior

@[simp] theorem mem_halfSpaceComplexExtChartDomain
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) (z : ℂ) :
    z ∈ halfSpaceComplexExtChartDomain x ↔
      Complex.orthonormalBasisOneI.repr z ∈
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target :=
  Iff.rfl

/-- The positive-real-part piece of a half-space extended-chart domain is
precisely its ordinary open interior complex chart domain. -/
theorem halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane =
      interiorComplexExtChartDomain
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr x := by
  ext z
  simp only [halfSpaceComplexExtChartDomain,
    complexRightOpenHalfPlane, interiorComplexExtChartDomain,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
    interior_extChartAt_target_eq_inter_interior_range,
    interior_range_modelWithCornersEuclideanHalfSpace,
    Complex.orthonormalBasisOneI_repr_apply]
  rfl

/-- The interior part of a half-space complex chart domain is open in the
ambient complex plane. -/
theorem isOpen_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] (x : M) :
    IsOpen
      (halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane) := by
  rw [halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane]
  exact isOpen_interiorComplexExtChartDomain
    (modelWithCornersEuclideanHalfSpace 2)
    Complex.orthonormalBasisOneI.repr x

/-- On the positive-real-part piece, the half-space inverse chart is an
ordinary manifold-differentiable interior parametrization. -/
theorem mdifferentiableAt_halfSpaceComplexExtChart
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (x : M) {z : ℂ}
    (hz : z ∈
      halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane) :
    MDifferentiableAt 𝓘(ℝ, ℂ)
      (modelWithCornersEuclideanHalfSpace 2)
      (halfSpaceComplexExtChart x) z := by
  rw [halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane] at hz
  simpa only [halfSpaceComplexExtChart, interiorComplexExtChart] using
    mdifferentiableAt_interiorComplexExtChart
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr x hz

/-- On the interior of a half-space chart, the derivative of the inverse
chart factors through the canonical tangent-bundle trivialization at the
chart center. -/
theorem mfderiv_halfSpaceComplexExtChart_eq_symmL_comp
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (x : M) {z : ℂ}
    (hz : z ∈ halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane) :
    mfderiv 𝓘(ℝ, ℂ) (modelWithCornersEuclideanHalfSpace 2)
        (halfSpaceComplexExtChart x) z =
      ((trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x).symmL ℝ
          (halfSpaceComplexExtChart x z)).comp
        Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toContinuousLinearMap := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  have htarget : e z ∈ (extChartAt I x).target := by
    change Complex.orthonormalBasisOneI.repr z ∈ (extChartAt I x).target
    exact (mem_halfSpaceComplexExtChartDomain x z).mp hz.1
  have hinterior : e z ∈ interior (Set.range I) := by
    change Complex.orthonormalBasisOneI.repr z ∈
      interior (Set.range (modelWithCornersEuclideanHalfSpace 2))
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    simpa [complexRightOpenHalfPlane,
      Complex.orthonormalBasisOneI_repr_apply] using hz.2
  have hrange : Set.range I ∈ 𝓝 (e z) :=
    mem_of_superset (isOpen_interior.mem_nhds hinterior) interior_subset
  have hsource :
      halfSpaceComplexExtChart x z ∈
        (chartAt (EuclideanHalfSpace 2) x).source := by
    change (extChartAt I x).symm (e z) ∈
      (chartAt (EuclideanHalfSpace 2) x).source
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target htarget
  have hinv :
      MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
        (extChartAt I x).symm (e z) :=
    (mdifferentiableWithinAt_extChartAt_symm (I := I) htarget).mdifferentiableAt
      hrange
  have htriv :
      (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace I) x).symmL ℝ (halfSpaceComplexExtChart x z) =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
          (extChartAt I x).symm (e z) := by
    calc
      _ = mfderiv[Set.range I] (extChartAt I x).symm
          (extChartAt I x (halfSpaceComplexExtChart x z)) :=
        TangentBundle.symmL_trivializationAt (I := I) hsource
      _ = mfderiv[Set.range I] (extChartAt I x).symm (e z) := by
        rw [show extChartAt I x (halfSpaceComplexExtChart x z) = e z by
          change extChartAt I x ((extChartAt I x).symm (e z)) = e z
          exact (extChartAt I x).right_inv htarget]
      _ = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
          (extChartAt I x).symm (e z) :=
        mfderivWithin_of_mem_nhds hrange
  change mfderiv 𝓘(ℝ, ℂ) I ((extChartAt I x).symm ∘ e) z =
    ((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace I) x).symmL ℝ
        (halfSpaceComplexExtChart x z)).comp e.toContinuousLinearMap
  calc
    _ = (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I
          (extChartAt I x).symm (e z)).comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) e z) :=
      mfderiv_comp z hinv e.mdifferentiableAt
    _ = _ := by
      rw [e.mfderiv_eq, ← htriv]

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

/-- The positive-real-part coordinate piece maps exactly onto the manifold
interior lying in the chosen boundary-chart source. -/
theorem image_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M] (x : M) :
    halfSpaceComplexExtChart x ''
        (halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane) =
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).source ∩
        (modelWithCornersEuclideanHalfSpace 2).interior M := by
  rw [halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane]
  simpa only [halfSpaceComplexExtChart, interiorComplexExtChart,
    extChartAt_source] using
    image_interiorComplexExtChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr x

#print axioms interior_extChartAt_target_eq_inter_interior_range
#print axioms halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
#print axioms isOpen_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
#print axioms mdifferentiableAt_halfSpaceComplexExtChart
#print axioms mfderiv_halfSpaceComplexExtChart_eq_symmL_comp
#print axioms halfSpaceComplexExtChartDomain_subset_rightClosedHalfPlane
#print axioms continuousOn_halfSpaceComplexExtChart
#print axioms contMDiffOn_halfSpaceComplexExtChart
#print axioms injOn_halfSpaceComplexExtChart
#print axioms image_halfSpaceComplexExtChartDomain
#print axioms
  image_halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane

end

end GromovFilling
