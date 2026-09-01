import GromovFilling.RiemannianControlledBoundaryCenterOverlap
import GromovFilling.RiemannianControlledBoundaryTransitionDirection

/-!
# Center-parameter adapters for oriented boundary transitions

Equality of two canonical center parameters gives the concrete source point
and selected-chart image witnesses needed to apply the local oriented
transition-direction lemmas.  This module keeps that boundary bookkeeping
separate from the orientation-free center-overlap interval API.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianControlledBoundaryTransitionCenterDirectionEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Equality of selected center parameters supplies an axis source point and
selected-chart image witnesses for the corresponding transition. -/
private theorem transition_source_axis_images_of_centerParameter_eq
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (a b : M) (u v : ℝ)
    (hu : (u * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain a)
    (hv : (v * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain b)
    (hparameter : controlledBoundaryCenterParameter boundary a u =
      controlledBoundaryCenterParameter boundary b v) :
    Complex.orthonormalBasisOneI.repr (u * Complex.I) ∈
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source ∧
      Complex.orthonormalBasisOneI.repr (u * Complex.I) 0 = 0 ∧
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm
          (Complex.orthonormalBasisOneI.repr (u * Complex.I)) ∈
        halfSpaceComplexExtChart a ''
          chosenControlledHalfSpaceComplexChartDomain a ∧
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm
          (Complex.orthonormalBasisOneI.repr (u * Complex.I)) ∈
        halfSpaceComplexExtChart b ''
          chosenControlledHalfSpaceComplexChartDomain b := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let z : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (u * Complex.I)
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  obtain ⟨hz, hzApply⟩ :=
    centerParameter_eq_transition_source_and_apply
      boundary hboundaryRange a b u v hu hv hparameter
  change z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source at hz
  change T z = Complex.orthonormalBasisOneI.repr (v * Complex.I) at hzApply
  have hzAxis : z 0 = 0 := by
    simp [z, Complex.orthonormalBasisOneI_repr_apply,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self]
  have hzSplit : z ∈ (extChartAt I a).target ∧
      (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  have hAImage : (extChartAt I a).symm z ∈
      halfSpaceComplexExtChart a ''
        chosenControlledHalfSpaceComplexChartDomain a := by
    refine ⟨u * Complex.I, hu, ?_⟩
    change (extChartAt I a).symm
        (Complex.orthonormalBasisOneI.repr (u * Complex.I)) =
      (extChartAt I a).symm z
    rw [z]
  have hBImage : (extChartAt I a).symm z ∈
      halfSpaceComplexExtChart b ''
        chosenControlledHalfSpaceComplexChartDomain b := by
    refine ⟨v * Complex.I, hv, ?_⟩
    change (extChartAt I b).symm
        (Complex.orthonormalBasisOneI.repr (v * Complex.I)) =
      (extChartAt I a).symm z
    rw [← hzApply]
    simpa only [T, Function.comp_apply] using
      (extChartAt I b).left_inv hzSplit.2
  simpa only [I, z] using ⟨hz, hzAxis, hAImage, hBImage⟩

/-- Equal conventional controlled-chart signs make the transition between
equal center parameters strictly increasing on a short axis interval. -/
theorem exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (a b : M) (u v : ℝ)
    (hu : (u * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain a)
    (hv : (v * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain b)
    (hparameter : controlledBoundaryCenterParameter boundary a u =
      controlledBoundaryCenterParameter boundary b v)
    (hsign : O.controlledChartSign a = O.controlledChartSign b) :
    ∃ r : ℝ, 0 < r ∧ StrictMonoOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
            t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  obtain ⟨hz, hzAxis, hAImage, hBImage⟩ :=
    transition_source_axis_images_of_centerParameter_eq
      boundary hboundaryRange a b u v hu hv hparameter
  exact exists_axis_interval_strictMonoOn_of_controlledChartSign_eq
    O a b hz hzAxis hAImage hBImage hsign

/-- Opposite conventional controlled-chart signs make the transition between
equal center parameters strictly decreasing on a short axis interval. -/
theorem exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (a b : M) (u v : ℝ)
    (hu : (u * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain a)
    (hv : (v * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain b)
    (hparameter : controlledBoundaryCenterParameter boundary a u =
      controlledBoundaryCenterParameter boundary b v)
    (hsign : O.controlledChartSign a = -O.controlledChartSign b) :
    ∃ r : ℝ, 0 < r ∧ StrictAntiOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
            t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  obtain ⟨hz, hzAxis, hAImage, hBImage⟩ :=
    transition_source_axis_images_of_centerParameter_eq
      boundary hboundaryRange a b u v hu hv hparameter
  exact exists_axis_interval_strictAntiOn_of_controlledChartSign_eq_neg
    O a b hz hzAxis hAImage hBImage hsign

#print axioms
  exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
#print axioms
  exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg

end

end GromovFilling
