import GromovFilling.RiemannianSurfaceOrientation
import GromovFilling.RiemannianHalfSpaceChartControl
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local transport of conventional surface orientations

This module transports a conventional surface orientation through the
canonical tangent-bundle trivialization on one controlled half-space chart.
It contains no chart-sign construction, boundary-direction convention,
Stokes datum, or area conclusion.
-/

open Bundle Function Manifold Metric Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

local instance riemannianSurfaceOrientationTransportEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]

/-- A point of the chosen controlled half-space coordinate domain, viewed in
the ordinary source of the extended chart. -/
def chosenControlledHalfSpaceChartSourcePoint
    (x : M)
    (z : {z : ℂ // z ∈ chosenControlledHalfSpaceComplexChartDomain x}) :
    (chartAt (EuclideanHalfSpace 2) x).source :=
  ⟨halfSpaceComplexExtChart x z.1, by
    have hzDomain : z.1 ∈ halfSpaceComplexExtChartDomain x :=
      controlledHalfSpaceComplexChartDomain_subset_domain
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) x)
        (by
          simpa only [chosenControlledHalfSpaceComplexChartDomain] using
            z.property)
    have hzTarget :
        Complex.orthonormalBasisOneI.repr z.1 ∈
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target :=
      (mem_halfSpaceComplexExtChartDomain x z.1).mp hzDomain
    simpa only [halfSpaceComplexExtChart, Function.comp_apply, extChartAt_source] using
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).map_target
        hzTarget⟩

/-- The orientation at a chart-source point, transported into the fixed
tangent-bundle trivialization based at `x`. -/
def RiemannianSurfaceOrientation.trivializedOrientationAt
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (x : M) (y : (chartAt (EuclideanHalfSpace 2) x).source) :
    Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  Orientation.map (Fin 2)
    ((trivializationAt (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x)
      .continuousLinearEquivAt ℝ (y : M)
        (by
          simpa only [TangentBundle.trivializationAt_baseSet] using
            y.property)).toLinearEquiv
    (O.orientation (y : M))

/-- In a chosen controlled half-space chart, a conventional surface
orientation has one constant trivialized value, including at the chart
center. -/
theorem RiemannianSurfaceOrientation
    .trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceComplexChartDomain
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (x : M) {z : ℂ}
    (hz : z ∈ chosenControlledHalfSpaceComplexChartDomain x) :
    RiemannianSurfaceOrientation.trivializedOrientationAt O x
        (chosenControlledHalfSpaceChartSourcePoint x ⟨z, hz⟩) =
      RiemannianSurfaceOrientation.trivializedOrientationAt O x
        ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let c := chosenInteriorChartControl I x
  let D : Set ℂ := chosenControlledHalfSpaceComplexChartDomain x
  have hconvex : Convex ℝ D := by
    change Convex ℝ
      (Complex.orthonormalBasisOneI.repr ⁻¹' controlledHalfSpaceChartSet c)
    exact (convex_controlledHalfSpaceChartSet c).linear_preimage
      Complex.orthonormalBasisOneI.repr.toLinearEquiv.toLinearMap
  letI : PreconnectedSpace D :=
    Subtype.preconnectedSpace hconvex.isPreconnected
  have hDsubset : D ⊆ halfSpaceComplexExtChartDomain x := by
    intro w hw
    change w ∈ controlledHalfSpaceComplexChartDomain c at hw
    exact controlledHalfSpaceComplexChartDomain_subset_domain c hw
  have hmaps : Set.MapsTo (halfSpaceComplexExtChart x) D
      (chartAt (EuclideanHalfSpace 2) x).source := by
    intro w hw
    have hwTarget :
        Complex.orthonormalBasisOneI.repr w ∈ (extChartAt I x).target :=
      (mem_halfSpaceComplexExtChartDomain x w).mp (hDsubset hw)
    simpa only [halfSpaceComplexExtChart, Function.comp_apply, extChartAt_source] using
      (extChartAt I x).map_target hwTarget
  let g : D → (chartAt (EuclideanHalfSpace 2) x).source :=
    hmaps.restrict (halfSpaceComplexExtChart x) D
      (chartAt (EuclideanHalfSpace 2) x).source
  have hcontD : ContinuousOn (halfSpaceComplexExtChart x) D :=
    (continuousOn_halfSpaceComplexExtChart x).mono hDsubset
  have hg : Continuous g := by
    simpa only [g] using hcontD.mapsToRestrict hmaps
  have hpre : IsPreconnected (Set.range g) :=
    isPreconnected_range hg
  let z₀ : ℂ :=
    Complex.orthonormalBasisOneI.repr.symm (extChartAt I x x)
  have hz₀ : z₀ ∈ D := by
    change Complex.orthonormalBasisOneI.repr z₀ ∈
      ball (extChartAt I x x) c.r ∩ Set.range I
    rw [show Complex.orthonormalBasisOneI.repr z₀ = extChartAt I x x by
      simp only [z₀, LinearIsometryEquiv.apply_symm_apply]]
    exact ⟨mem_ball_self c.r_pos,
      extChartAt_target_subset_range x (mem_extChartAt_target x)⟩
  have hchart₀ : halfSpaceComplexExtChart x z₀ = x := by
    change (extChartAt I x).symm
      (Complex.orthonormalBasisOneI.repr z₀) = x
    rw [show Complex.orthonormalBasisOneI.repr z₀ = extChartAt I x x by
      simp only [z₀, LinearIsometryEquiv.apply_symm_apply]]
    exact (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hgz :
      g ⟨z, hz⟩ =
        chosenControlledHalfSpaceChartSourcePoint x ⟨z, hz⟩ := by
    apply Subtype.ext
    change halfSpaceComplexExtChart x z = halfSpaceComplexExtChart x z
    rfl
  have hg₀ :
      g ⟨z₀, hz₀⟩ =
        (⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ :
          (chartAt (EuclideanHalfSpace 2) x).source) := by
    apply Subtype.ext
    change halfSpaceComplexExtChart x z₀ = x
    exact hchart₀
  have htransport :=
    (O.isLocallyConstant x).apply_eq_of_isPreconnected
      (s := Set.range g) hpre
      ⟨⟨z, hz⟩, rfl⟩
      ⟨⟨z₀, hz₀⟩, rfl⟩
  change
    RiemannianSurfaceOrientation.trivializedOrientationAt O x
        (g ⟨z, hz⟩) =
      RiemannianSurfaceOrientation.trivializedOrientationAt O x
        (g ⟨z₀, hz₀⟩) at htransport
  rw [hgz, hg₀] at htransport
  exact htransport

/-- A point in the image of a chosen controlled half-space chart has a
chart-source witness whose conventional orientation is the chart-center
orientation. -/
theorem RiemannianSurfaceOrientation
    .exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (x p : M)
    (hp : p ∈ halfSpaceComplexExtChart x ''
      chosenControlledHalfSpaceComplexChartDomain x) :
    ∃ hpx : p ∈ (chartAt (EuclideanHalfSpace 2) x).source,
      RiemannianSurfaceOrientation.trivializedOrientationAt O x ⟨p, hpx⟩ =
        RiemannianSurfaceOrientation.trivializedOrientationAt O x
          ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ := by
  rcases hp with ⟨z, hz, hpz⟩
  have hpx : p ∈ (chartAt (EuclideanHalfSpace 2) x).source := by
    rw [← hpz]
    exact (chosenControlledHalfSpaceChartSourcePoint x ⟨z, hz⟩).property
  refine ⟨hpx, ?_⟩
  have hpoint :
      (⟨p, hpx⟩ : (chartAt (EuclideanHalfSpace 2) x).source) =
        chosenControlledHalfSpaceChartSourcePoint x ⟨z, hz⟩ := by
    apply Subtype.ext
    exact hpz.symm
  rw [hpoint]
  exact O
    .trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceComplexChartDomain
      x hz

#print axioms chosenControlledHalfSpaceChartSourcePoint
#print axioms RiemannianSurfaceOrientation.trivializedOrientationAt
#print axioms
  RiemannianSurfaceOrientation
    .trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceComplexChartDomain
#print axioms
  RiemannianSurfaceOrientation
    .exists_trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceImage

end

end GromovFilling
