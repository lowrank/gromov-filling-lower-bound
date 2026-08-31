import GromovFilling.OrientationAreaForm
import GromovFilling.RiemannianControlledSurfaceOrientation
import GromovFilling.RiemannianSurfaceOrientationTransport

/-!
# From a conventional surface orientation to controlled chart signs

The ordinary orientation datum is locally constant in every tangent-bundle
trivialization.  This module fixes the standard complex coordinate orientation
and records the corresponding `±1` sign at each canonical half-space chart
center.  Subsequent lemmas identify these signs with the signed Riemannian
chart Jacobians on the selected controlled interior domains.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

local instance surfaceOrientationConversionEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- The orientation of the half-space coordinate plane obtained from the
standard complex orthonormal basis. -/
def halfSpaceComplexCoordinateOrientation :
    Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  Orientation.map (Fin 2)
    Complex.orthonormalBasisOneI.repr.toLinearEquiv
    Complex.orthonormalBasisOneI.toBasis.orientation

/-- The sign of a conventional surface orientation in the canonical tangent
trivialization based at a half-space chart center. -/
def RiemannianSurfaceOrientation.controlledChartSign
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (x : M) : ℝ := by
  classical
  exact if RiemannianSurfaceOrientation.trivializedOrientationAt O x
      ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
        halfSpaceComplexCoordinateOrientation
    then 1 else -1

/-- A center sign is always one of the two orientation signs. -/
theorem RiemannianSurfaceOrientation.controlledChartSign_eq_one_or_neg_one
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (x : M) :
    O.controlledChartSign x = 1 ∨ O.controlledChartSign x = -1 := by
  classical
  by_cases h : RiemannianSurfaceOrientation.trivializedOrientationAt O x
      ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
        halfSpaceComplexCoordinateOrientation
  · left
    simp only [RiemannianSurfaceOrientation.controlledChartSign, h, if_pos]
  · right
    simp only [RiemannianSurfaceOrientation.controlledChartSign, h, if_neg]

/-- Transporting an orientation through two linear equivalences is the same
as transporting it through their composite. -/
private theorem orientation_map_trans
    {E F G : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    [AddCommMonoid G] [Module ℝ G]
    (e : E ≃ₗ[ℝ] F) (f : F ≃ₗ[ℝ] G)
    (o : Orientation ℝ E (Fin 2)) :
    Orientation.map (Fin 2) (e.trans f) o =
      Orientation.map (Fin 2) f (Orientation.map (Fin 2) e o) := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

#print axioms halfSpaceComplexCoordinateOrientation
#print axioms RiemannianSurfaceOrientation.controlledChartSign
#print axioms RiemannianSurfaceOrientation.controlledChartSign_eq_one_or_neg_one

end

end GromovFilling
