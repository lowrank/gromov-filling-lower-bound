import GromovFilling.RiemannianSurfaceOrientationTransport
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Conventional orientation transport across chart overlaps

The canonical tangent-bundle trivializations based at two chart centers have
a coordinate change on their overlap.  A conventional surface orientation
transports through that coordinate change.  This records the local linear
fact needed later to compare chart signs with the determinant of a boundary
chart transition; it contains no boundary-direction or global conclusion.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

local instance riemannianSurfaceOrientationOverlapEuclideanFinrankTwo :
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

/-- On an ordinary chart overlap, the coordinate change between the two
canonical tangent-bundle trivializations is the tangent-coordinate change. -/
theorem trivialization_coordChange_apply_eq_tangentCoordChange
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b p : M)
    (hpa : p ∈ (chartAt (EuclideanHalfSpace 2) a).source)
    (hpb : p ∈ (chartAt (EuclideanHalfSpace 2) b).source)
    (v : EuclideanSpace ℝ (Fin 2)) :
    ((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
      (trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b) p) v =
      tangentCoordChange (modelWithCornersEuclideanHalfSpace 2) a b p v := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  have hbase : p ∈ (trivializationAt E (TangentSpace I) a).baseSet ∩
      (trivializationAt E (TangentSpace I) b).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using ⟨hpa, hpb⟩
  change ((trivializationAt E (TangentSpace I) a).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b) p) v =
    (tangentBundleCore I M).coordChange
      (achart (EuclideanHalfSpace 2) a)
      (achart (EuclideanHalfSpace 2) b) p v
  exact Bundle.VectorBundleCore.trivializationAt_coordChange_eq
    (Z := tangentBundleCore I M) hbase v

/-- The canonical tangent-coordinate change carries a conventional
orientation expressed in the trivialization based at one chart center to its
expression in the trivialization based at the other center. -/
theorem RiemannianSurfaceOrientation.trivializedOrientationAt_coordChange
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b p : M)
    (hpa : p ∈ (chartAt (EuclideanHalfSpace 2) a).source)
    (hpb : p ∈ (chartAt (EuclideanHalfSpace 2) b).source) :
    Orientation.map (Fin 2)
      ((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b) p).toLinearEquiv
      (RiemannianSurfaceOrientation.trivializedOrientationAt O a ⟨p, hpa⟩) =
        RiemannianSurfaceOrientation.trivializedOrientationAt O b ⟨p, hpb⟩ := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let E := EuclideanSpace ℝ (Fin 2)
  let ta : TangentSpace I p ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hpa)
  let tb : TangentSpace I p ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) b).continuousLinearEquivAt ℝ p
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hpb)
  let e : E ≃L[ℝ] E :=
    (trivializationAt E (TangentSpace I) a).coordChangeL ℝ
      (trivializationAt E (TangentSpace I) b) p
  have hbase : p ∈ (trivializationAt E (TangentSpace I) a).baseSet ∩
      (trivializationAt E (TangentSpace I) b).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using ⟨hpa, hpb⟩
  have hcoord : e = ta.symm.trans tb := by
    symm
    simpa only [ta, tb, e] using
      Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
        (trivializationAt E (TangentSpace I) a)
        (trivializationAt E (TangentSpace I) b) hbase
  have hcancel : ta.toLinearEquiv.trans (ta.symm.trans tb).toLinearEquiv =
      tb.toLinearEquiv := by
    ext v
    simp
  change Orientation.map (Fin 2) e.toLinearEquiv
      (Orientation.map (Fin 2) ta.toLinearEquiv (O.orientation p)) =
    Orientation.map (Fin 2) tb.toLinearEquiv (O.orientation p)
  rw [hcoord]
  calc
    Orientation.map (Fin 2) (ta.symm.trans tb).toLinearEquiv
        (Orientation.map (Fin 2) ta.toLinearEquiv (O.orientation p)) =
      Orientation.map (Fin 2)
        (ta.toLinearEquiv.trans (ta.symm.trans tb).toLinearEquiv)
        (O.orientation p) :=
      (orientation_map_trans ta.toLinearEquiv
        (ta.symm.trans tb).toLinearEquiv (O.orientation p)).symm
    _ = Orientation.map (Fin 2) tb.toLinearEquiv (O.orientation p) := by
      rw [hcancel]

/-- If the local trivialized orientations are identified with their chart
centers, the tangent-coordinate change transports those center orientations
as well. -/
theorem RiemannianSurfaceOrientation.center_trivializedOrientationAt_coordChange
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b p : M)
    (hpa : p ∈ (chartAt (EuclideanHalfSpace 2) a).source)
    (hpb : p ∈ (chartAt (EuclideanHalfSpace 2) b).source)
    (hA : RiemannianSurfaceOrientation.trivializedOrientationAt O a ⟨p, hpa⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩)
    (hB : RiemannianSurfaceOrientation.trivializedOrientationAt O b ⟨p, hpb⟩ =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩) :
    Orientation.map (Fin 2)
      ((trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) a).coordChangeL ℝ
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) b) p).toLinearEquiv
      (RiemannianSurfaceOrientation.trivializedOrientationAt O a
        ⟨a, mem_chart_source (EuclideanHalfSpace 2) a⟩) =
      RiemannianSurfaceOrientation.trivializedOrientationAt O b
        ⟨b, mem_chart_source (EuclideanHalfSpace 2) b⟩ := by
  rw [← hA, ← hB]
  exact O.trivializedOrientationAt_coordChange a b p hpa hpb

#print axioms trivialization_coordChange_apply_eq_tangentCoordChange
#print axioms
  RiemannianSurfaceOrientation.trivializedOrientationAt_coordChange
#print axioms
  RiemannianSurfaceOrientation.center_trivializedOrientationAt_coordChange

end

end GromovFilling
