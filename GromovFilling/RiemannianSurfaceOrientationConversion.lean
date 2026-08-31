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
    simp [RiemannianSurfaceOrientation.controlledChartSign, h]

/-- A positive controlled chart sign means that the conventional orientation
at the chart center agrees with the standard half-space coordinate
orientation. -/
theorem RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (x : M)
    (hsign : O.controlledChartSign x = 1) :
    RiemannianSurfaceOrientation.trivializedOrientationAt O x
      ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
      halfSpaceComplexCoordinateOrientation := by
  classical
  by_contra h
  have hsignNeg : O.controlledChartSign x = -1 := by
    change (if RiemannianSurfaceOrientation.trivializedOrientationAt O x
        ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
          halfSpaceComplexCoordinateOrientation then 1 else -1) = -1
    simp [h]
  rw [hsignNeg] at hsign
  norm_num at hsign

/-- A negative controlled chart sign means that the conventional orientation
at the chart center is the negative of the standard half-space coordinate
orientation. -/
theorem RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (x : M)
    (hsign : O.controlledChartSign x = -1) :
    RiemannianSurfaceOrientation.trivializedOrientationAt O x
      ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
      -halfSpaceComplexCoordinateOrientation := by
  classical
  have hne : RiemannianSurfaceOrientation.trivializedOrientationAt O x
      ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ ≠
        halfSpaceComplexCoordinateOrientation := by
    intro h
    have hsignPos : O.controlledChartSign x = 1 := by
      change (if RiemannianSurfaceOrientation.trivializedOrientationAt O x
          ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩ =
            halfSpaceComplexCoordinateOrientation then 1 else -1) = 1
      simp [h]
    rw [hsignPos] at hsign
    norm_num at hsign
  rcases Orientation.eq_or_eq_neg
      (RiemannianSurfaceOrientation.trivializedOrientationAt O x
        ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩)
      halfSpaceComplexCoordinateOrientation (by simp) with h | h
  · exact (hne h).elim
  · exact h

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

/-- A conventional orientation gives the `±1` sign required by every
controlled half-space chart on its selected controlled interior domain. -/
def RiemannianSurfaceOrientation.toControlledRiemannianSurfaceOrientation
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) :
    ControlledRiemannianSurfaceOrientation M where
  tangentOrientation := O.toTangentPlaneOrientation
    (modelWithCornersEuclideanHalfSpace 2) M
  chartSign := O.controlledChartSign
  chartSign_eq_one_or_neg_one :=
    O.controlledChartSign_eq_one_or_neg_one
  chartSign_mul_jacobian_eq_abs := by
    classical
    intro x z hz
    let e : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
    have hzControlled : z ∈ chosenControlledHalfSpaceComplexChartDomain x :=
      chosenControlledInteriorComplexChartDomain_subset_chosenControlledHalfSpaceComplexChartDomain
        x hz
    have hzDeriv : z ∈
        halfSpaceComplexExtChartDomain x ∩ complexRightOpenHalfPlane := by
      rw [halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane]
      exact controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
        (chosenInteriorChartControl (modelWithCornersEuclideanHalfSpace 2) x) hz
    let y : (chartAt (EuclideanHalfSpace 2) x).source :=
      chosenControlledHalfSpaceChartSourcePoint x ⟨z, hzControlled⟩
    have hy : (y : M) = halfSpaceComplexExtChart x z := rfl
    have hyBase : (y : M) ∈
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using y.property
    let t : TangentSpace (modelWithCornersEuclideanHalfSpace 2) (y : M) ≃L[ℝ]
        EuclideanSpace ℝ (Fin 2) :=
      (trivializationAt (EuclideanSpace ℝ (Fin 2))
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x).continuousLinearEquivAt ℝ
          (y : M) hyBase
    let q : ℂ ≃L[ℝ]
        TangentSpace (modelWithCornersEuclideanHalfSpace 2) (y : M) :=
      e.trans t.symm
    let o0 : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
      RiemannianSurfaceOrientation.trivializedOrientationAt O x
        ⟨x, mem_chart_source (EuclideanHalfSpace 2) x⟩
    have htransport :
        Orientation.map (Fin 2) t.toLinearEquiv (O.orientation (y : M)) = o0 := by
      have h := RiemannianSurfaceOrientation.trivializedOrientationAt_eq_center_of_mem_chosenControlledHalfSpaceComplexChartDomain
        O x hzControlled
      change Orientation.map (Fin 2) t.toLinearEquiv (O.orientation (y : M)) = o0 at h
      exact h
    have hsymm :
        (t.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ]
          TangentSpace (modelWithCornersEuclideanHalfSpace 2) (y : M)) =
          (trivializationAt (EuclideanSpace ℝ (Fin 2))
            (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x).symmL ℝ (y : M) := by
      dsimp only [t]
      exact Trivialization.symm_continuousLinearEquivAt_eq'
        (trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x) hyBase
    have hqtrans : q.toLinearEquiv.trans t.toLinearEquiv = e.toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change t (q v) = e v
      simp [q]
    have hqderiv : q.toContinuousLinearMap =
        mfderiv 𝓘(ℝ, ℂ) (modelWithCornersEuclideanHalfSpace 2)
          (halfSpaceComplexExtChart x) z := by
      rw [mfderiv_halfSpaceComplexExtChart_eq_symmL_comp x hzDeriv]
      ext v
      change t.symm (e v) =
        ((trivializationAt (EuclideanSpace ℝ (Fin 2))
          (TangentSpace (modelWithCornersEuclideanHalfSpace 2)) x).symmL ℝ
            (halfSpaceComplexExtChart x z)) (e v)
      simpa only [hy] using
        congrArg (fun L ↦ L (e v)) hsymm
    letI : Fact (Module.finrank ℝ
        (TangentSpace (modelWithCornersEuclideanHalfSpace 2)
          (halfSpaceComplexExtChart x z)) = 2) :=
      ⟨tangentSpace_finrank_eq_two
        (modelWithCornersEuclideanHalfSpace 2)
        (halfSpaceComplexExtChart x z)⟩
    have hJacobian :
        orientedRiemannianChartJacobian
          (modelWithCornersEuclideanHalfSpace 2)
          (O.toTangentPlaneOrientation
            (modelWithCornersEuclideanHalfSpace 2) M)
          (halfSpaceComplexExtChart x) z =
        (O.orientation (y : M)).areaForm
          (q (Complex.orthonormalBasisOneI 0))
          (q (Complex.orthonormalBasisOneI 1)) := by
      change (O.orientation (halfSpaceComplexExtChart x z)).areaForm
          (mfderiv 𝓘(ℝ, ℂ) (modelWithCornersEuclideanHalfSpace 2)
            (halfSpaceComplexExtChart x) z
            (orientedComplexTangentOrthonormalBasis z 0))
          (mfderiv 𝓘(ℝ, ℂ) (modelWithCornersEuclideanHalfSpace 2)
            (halfSpaceComplexExtChart x) z
            (orientedComplexTangentOrthonormalBasis z 1)) =
        (O.orientation (y : M)).areaForm
          (q (Complex.orthonormalBasisOneI 0))
          (q (Complex.orthonormalBasisOneI 1))
      rw [← hqderiv]
      simp only [orientedComplexTangentOrthonormalBasis_apply]
    by_cases hcenter : o0 = halfSpaceComplexCoordinateOrientation
    · have hlocal :
          Orientation.map (Fin 2) q.toLinearEquiv
              Complex.orthonormalBasisOneI.toBasis.orientation =
            O.orientation (y : M) := by
        apply (Orientation.map (Fin 2) t.toLinearEquiv).injective
        calc
          Orientation.map (Fin 2) t.toLinearEquiv
              (Orientation.map (Fin 2) q.toLinearEquiv
                Complex.orthonormalBasisOneI.toBasis.orientation) =
              Orientation.map (Fin 2)
                (q.toLinearEquiv.trans t.toLinearEquiv)
                Complex.orthonormalBasisOneI.toBasis.orientation :=
            (orientation_map_trans q.toLinearEquiv t.toLinearEquiv
              Complex.orthonormalBasisOneI.toBasis.orientation).symm
          _ = Orientation.map (Fin 2) e.toLinearEquiv
                Complex.orthonormalBasisOneI.toBasis.orientation := by
            rw [hqtrans]
          _ = halfSpaceComplexCoordinateOrientation := rfl
          _ = o0 := hcenter.symm
          _ = Orientation.map (Fin 2) t.toLinearEquiv
                (O.orientation (y : M)) := htransport.symm
      have hpositive : 0 <
          orientedRiemannianChartJacobian
            (modelWithCornersEuclideanHalfSpace 2)
            (O.toTangentPlaneOrientation
              (modelWithCornersEuclideanHalfSpace 2) M)
            (halfSpaceComplexExtChart x) z := by
        rw [hJacobian]
        exact orientation_map_eq_areaForm_pos
          Complex.orthonormalBasisOneI (O.orientation (y : M)) q hlocal
      have hsign : O.controlledChartSign x = 1 := by
        change (if o0 = halfSpaceComplexCoordinateOrientation then 1 else -1) = 1
        simp [hcenter]
      rw [hsign, one_mul, abs_of_pos hpositive]
    · have hcenterNeg : o0 = -halfSpaceComplexCoordinateOrientation := by
        rcases Orientation.eq_or_eq_neg o0 halfSpaceComplexCoordinateOrientation (by simp) with
            h | h
        · exact (hcenter h).elim
        · exact h
      have hlocal :
          Orientation.map (Fin 2) q.toLinearEquiv
              Complex.orthonormalBasisOneI.toBasis.orientation =
            -O.orientation (y : M) := by
        apply (Orientation.map (Fin 2) t.toLinearEquiv).injective
        calc
          Orientation.map (Fin 2) t.toLinearEquiv
              (Orientation.map (Fin 2) q.toLinearEquiv
                Complex.orthonormalBasisOneI.toBasis.orientation) =
              Orientation.map (Fin 2)
                (q.toLinearEquiv.trans t.toLinearEquiv)
                Complex.orthonormalBasisOneI.toBasis.orientation :=
            (orientation_map_trans q.toLinearEquiv t.toLinearEquiv
              Complex.orthonormalBasisOneI.toBasis.orientation).symm
          _ = Orientation.map (Fin 2) e.toLinearEquiv
                Complex.orthonormalBasisOneI.toBasis.orientation := by
            rw [hqtrans]
          _ = halfSpaceComplexCoordinateOrientation := rfl
          _ = -o0 := by
            calc
              halfSpaceComplexCoordinateOrientation =
                  -(-halfSpaceComplexCoordinateOrientation) :=
                (neg_neg halfSpaceComplexCoordinateOrientation).symm
              _ = -o0 := congrArg (fun w ↦ -w) hcenterNeg.symm
          _ = -(Orientation.map (Fin 2) t.toLinearEquiv
                (O.orientation (y : M))) := by rw [htransport]
          _ = Orientation.map (Fin 2) t.toLinearEquiv
                (-O.orientation (y : M)) := by
            rw [Orientation.map_neg]
      have hnegative :
          orientedRiemannianChartJacobian
            (modelWithCornersEuclideanHalfSpace 2)
            (O.toTangentPlaneOrientation
              (modelWithCornersEuclideanHalfSpace 2) M)
            (halfSpaceComplexExtChart x) z < 0 := by
        rw [hJacobian]
        exact orientation_map_eq_neg_areaForm_neg
          Complex.orthonormalBasisOneI (O.orientation (y : M)) q hlocal
      have hsign : O.controlledChartSign x = -1 := by
        change (if o0 = halfSpaceComplexCoordinateOrientation then 1 else -1) = -1
        simp [hcenter]
      rw [hsign, neg_one_mul, abs_of_neg hnegative]

#print axioms halfSpaceComplexCoordinateOrientation
#print axioms RiemannianSurfaceOrientation.controlledChartSign
#print axioms RiemannianSurfaceOrientation.controlledChartSign_eq_one_or_neg_one
#print axioms RiemannianSurfaceOrientation.centerOrientation_eq_coordinateOrientation_of_controlledChartSign_eq_one
#print axioms RiemannianSurfaceOrientation.centerOrientation_eq_neg_coordinateOrientation_of_controlledChartSign_eq_neg_one
#print axioms RiemannianSurfaceOrientation.toControlledRiemannianSurfaceOrientation

end

end GromovFilling
