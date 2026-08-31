import GromovFilling.OrientedRiemannianDensity
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Conventional orientations of smooth surfaces

The pinned manifold library provides tangent-bundle trivializations and
linear-algebra orientations, but no bundled orientation of a manifold with
boundary.  This module records the standard geometric datum: after transport
into any canonical tangent-bundle trivialization, the tangent orientation is
locally constant.  It deliberately mentions neither controlled chart signs,
boundary parametrizations, Stokes data, nor an area conclusion.
-/

open Bundle Manifold
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

/-- A conventional orientation of a smooth two-manifold: a tangent-plane
orientation that is locally constant in every canonical tangent-bundle
trivialization. -/
structure RiemannianSurfaceOrientation
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [Fact (Module.finrank ℝ E = 2)] where
  orientation : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin 2)
  isLocallyConstant :
    ∀ x : M,
      IsLocallyConstant (fun y : (chartAt H x).source ↦
        Orientation.map (Fin 2)
          ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ
            (y : M)
            (by simpa only [TangentBundle.trivializationAt_baseSet] using
              y.property)).toLinearEquiv
          (orientation (y : M)))

/-- Forgetting local coherence leaves the fiberwise orientation used by the
intrinsic Riemannian density layer. -/
def RiemannianSurfaceOrientation.toTangentPlaneOrientation
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] [Fact (Module.finrank ℝ E = 2)]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (O : RiemannianSurfaceOrientation I M) :
    RiemannianTangentPlaneOrientation I M where
  orientation := O.orientation

#print axioms RiemannianSurfaceOrientation
#print axioms RiemannianSurfaceOrientation.toTangentPlaneOrientation

end

end GromovFilling
