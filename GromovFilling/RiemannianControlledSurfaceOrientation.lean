import GromovFilling.RiemannianControlledBoundaryOrientation

/-!
# A controlled-chart presentation of surface orientation

Mathlib's pinned manifold library does not yet provide an orientation structure
for manifolds with boundary.  This file records the corresponding geometric
datum at the canonical controlled charts used by the project: one global
tangent-plane orientation and a compatible sign for every controlled inverse
chart.  Restricting those choices to any finite controlled partition produces
the chart-orientation datum used by the Stokes layer.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

local instance controlledSurfaceOrientationEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- A controlled-chart presentation of an orientation on a Riemannian surface
with boundary.  The sign is chosen for every canonical controlled chart, not
for one particular finite partition. -/
structure ControlledRiemannianSurfaceOrientation (M : Type uM)
    [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)] where
  tangentOrientation : RiemannianTangentPlaneOrientation
    (modelWithCornersEuclideanHalfSpace 2) M
  chartSign : M → ℝ
  chartSign_eq_one_or_neg_one :
    ∀ x, chartSign x = 1 ∨ chartSign x = -1
  chartSign_mul_jacobian_eq_abs :
    ∀ x z,
      z ∈ halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane →
        chartSign x *
            orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) tangentOrientation
              (halfSpaceComplexExtChart x) z =
          |orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) tangentOrientation
              (halfSpaceComplexExtChart x) z|

/-- Restrict a global controlled surface orientation to the finite charts in
a controlled boundary partition. -/
def ControlledRiemannianSurfaceOrientation.toBoundaryAtlasOrientation
    (R : ControlledRiemannianSurfaceOrientation M)
    (P : FiniteControlledBoundaryChartPartition M) :
    ControlledBoundaryAtlasOrientation P where
  tangentOrientation := R.tangentOrientation
  chartSign i := R.chartSign (P.center i)
  chartSign_eq_one_or_neg_one i :=
    R.chartSign_eq_one_or_neg_one (P.center i)
  chartSign_mul_jacobian_eq_abs i z hz :=
    R.chartSign_mul_jacobian_eq_abs (P.center i) z hz

#print axioms ControlledRiemannianSurfaceOrientation
#print axioms
  ControlledRiemannianSurfaceOrientation.toBoundaryAtlasOrientation

end

end GromovFilling
