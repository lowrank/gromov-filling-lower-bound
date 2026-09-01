import GromovFilling.RiemannianControlledBoundaryAxisDomain
import GromovFilling.RiemannianHalfSpaceChartTransitionControlledAxis

/-!
# Controlled boundary-chart overlaps from canonical center parameters

When two selected controlled half-space charts represent the same boundary
point through their canonical center parameters, their extended-chart
transition is defined at the first axis coordinate and maps it to the second
one.  This packages the bookkeeping which turns equality in the abstract
circle parameter into the concrete overlap data needed by transition and
orientation lemmas.

The follow-up interval theorem retains the quantitative controlled-domain
margins on both sides of the overlap.  It contains no orientation assertion.
-/

open Bundle Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

universe uM

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- An extended-chart transition between two boundary-axis coordinates
preserves their canonical center parameter.  No orientation or boundary-range
hypothesis is needed: both parameters are the set-theoretic inverse applied
to the same manifold point. -/
theorem controlledBoundaryCenterParameter_eq_of_transition_axis
    (boundary : UnitAddCircle → M) (a b : M)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (himageAxis :
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm) z) 0 = 0) :
    controlledBoundaryCenterParameter boundary a (z 1) =
      controlledBoundaryCenterParameter boundary b
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm) z) 1 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  change z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source at hz
  change (T z) 0 = 0 at himageAxis
  change controlledBoundaryCenterParameter boundary a (z 1) =
    controlledBoundaryCenterParameter boundary b ((T z) 1)
  have hzComplex : Complex.orthonormalBasisOneI.repr
      ((z 1) * Complex.I) = z := by
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    constructor
    · simpa [Complex.orthonormalBasisOneI_repr_apply] using hzAxis.symm
    · simp [Complex.orthonormalBasisOneI_repr_apply]
  have himageComplex : Complex.orthonormalBasisOneI.repr
      (((T z) 1) * Complex.I) = T z := by
    apply PiLp.ext
    rw [Fin.forall_fin_two]
    constructor
    · simpa [Complex.orthonormalBasisOneI_repr_apply] using himageAxis.symm
    · simp [Complex.orthonormalBasisOneI_repr_apply]
  have hzSplit : z ∈ (extChartAt I a).target ∧
      (extChartAt I a).symm z ∈ (extChartAt I b).source := by
    simpa only [PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  have hchart : halfSpaceComplexExtChart a ((z 1) * Complex.I) =
      halfSpaceComplexExtChart b (((T z) 1) * Complex.I) := by
    calc
      halfSpaceComplexExtChart a ((z 1) * Complex.I) =
          (extChartAt I a).symm z := by
        change (extChartAt I a).symm
          (Complex.orthonormalBasisOneI.repr ((z 1) * Complex.I)) =
            (extChartAt I a).symm z
        rw [hzComplex]
      _ = (extChartAt I b).symm (T z) := by
        symm
        simpa only [T, Function.comp_apply] using
          (extChartAt I b).left_inv hzSplit.2
      _ = halfSpaceComplexExtChart b (((T z) 1) * Complex.I) := by
        change (extChartAt I b).symm (T z) =
          (extChartAt I b).symm
            (Complex.orthonormalBasisOneI.repr ((T z 1) * Complex.I))
        rw [himageComplex]
  unfold controlledBoundaryCenterParameter
  exact congrArg (Function.invFun boundary) hchart

/-- Equal canonical center parameters force the associated extended-chart
transition to be defined at the first coordinate and to map it to the second
coordinate. -/
theorem centerParameter_eq_transition_source_and_apply
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
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (Complex.orthonormalBasisOneI.repr (u * Complex.I)) =
          Complex.orthonormalBasisOneI.repr (v * Complex.I) := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let z : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (u * Complex.I)
  let w : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (v * Complex.I)
  have huFull : (u * Complex.I : ℂ) ∈ halfSpaceComplexExtChartDomain a :=
    controlledHalfSpaceComplexChartDomain_subset_domain
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) a) hu
  have hvFull : (v * Complex.I : ℂ) ∈ halfSpaceComplexExtChartDomain b :=
    controlledHalfSpaceComplexChartDomain_subset_domain
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) b) hv
  have hzTarget : z ∈ (extChartAt I a).target := by
    simpa only [z, mem_halfSpaceComplexExtChartDomain] using huFull
  have hwTarget : w ∈ (extChartAt I b).target := by
    simpa only [w, mem_halfSpaceComplexExtChartDomain] using hvFull
  have hpoint : halfSpaceComplexExtChart a (u * Complex.I) =
      halfSpaceComplexExtChart b (v * Complex.I) := by
    calc
      halfSpaceComplexExtChart a (u * Complex.I) =
          boundary (controlledBoundaryCenterParameter boundary a u) :=
        (boundary_controlledBoundaryCenterParameter_of_mem_controlledDomain
          boundary hboundaryRange a u hu).symm
      _ = boundary (controlledBoundaryCenterParameter boundary b v) :=
        congrArg boundary hparameter
      _ = halfSpaceComplexExtChart b (v * Complex.I) :=
        boundary_controlledBoundaryCenterParameter_of_mem_controlledDomain
          boundary hboundaryRange b v hv
  have hpoint' : (extChartAt I a).symm z = (extChartAt I b).symm w := by
    simpa only [I, z, w, halfSpaceComplexExtChart, Function.comp_apply] using
      hpoint
  have hsourceB : (extChartAt I b).symm w ∈ (extChartAt I b).source :=
    (extChartAt I b).map_target hwTarget
  have hzSource : z ∈ ((extChartAt I a).symm ≫ extChartAt I b).source := by
    simp only [PartialEquiv.trans_source, PartialEquiv.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
    refine ⟨hzTarget, ?_⟩
    rw [hpoint']
    exact hsourceB
  refine ⟨by simpa only [I, z] using hzSource, ?_⟩
  change (extChartAt I b) ((extChartAt I a).symm z) = w
  rw [hpoint']
  exact (extChartAt I b).right_inv hwTarget

/-- At two selected controlled chart coordinates with the same canonical
boundary parameter, both controlled domains contain a common short
boundary-axis interval under their transition. -/
theorem exists_commonControlledAxisInterval_of_centerParameter_eq
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
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
      Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ) ∈
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source ∧
      Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ) ∈
          controlledHalfSpaceChartSet
            (chosenInteriorChartControl
              (modelWithCornersEuclideanHalfSpace 2) a) ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ))) ∈
          controlledHalfSpaceChartSet
            (chosenInteriorChartControl
              (modelWithCornersEuclideanHalfSpace 2) b) ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ))) 0 = 0 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let ca : InteriorChartControl I a := chosenInteriorChartControl I a
  let cb : InteriorChartControl I b := chosenInteriorChartControl I b
  let z : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (u * Complex.I)
  obtain ⟨hzSource, hzApply⟩ :=
    centerParameter_eq_transition_source_and_apply
      boundary hboundaryRange a b u v hu hv hparameter
  have hzAxis : z 0 = 0 := by
    simp only [z, Complex.orthonormalBasisOneI_repr_apply,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self]
  have hzA : z ∈ controlledHalfSpaceChartSet ca := by
    simpa only [I, ca, z, chosenControlledHalfSpaceComplexChartDomain,
      controlledHalfSpaceComplexChartDomain, Set.mem_preimage] using hu
  have hzB : (extChartAt I b ∘ (extChartAt I a).symm) z ∈
      controlledHalfSpaceChartSet cb := by
    rw [hzApply]
    simpa only [I, cb, z, chosenControlledHalfSpaceComplexChartDomain,
      controlledHalfSpaceComplexChartDomain, Set.mem_preimage] using hv
  simpa only [I, ca, cb, z] using
    exists_commonControlledAxisInterval a b ca cb hzSource hzAxis hzA hzB

/-- The common controlled axis interval obtained from two equal center
parameters carries equality of the canonical center parameters at every
point of the interval. -/
theorem exists_commonControlledAxisInterval_with_centerParameter_eq
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
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
      Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ) ∈
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source ∧
      Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ) ∈
          controlledHalfSpaceChartSet
            (chosenInteriorChartControl
              (modelWithCornersEuclideanHalfSpace 2) a) ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ))) ∈
          controlledHalfSpaceChartSet
            (chosenInteriorChartControl
              (modelWithCornersEuclideanHalfSpace 2) b) ∧
      ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ))) 0 = 0 ∧
      controlledBoundaryCenterParameter boundary a
        ((Complex.orthonormalBasisOneI.repr (u * Complex.I) +
          t • EuclideanSpace.single 1 (1 : ℝ)) 1) =
        controlledBoundaryCenterParameter boundary b
          (((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
            (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
              t • EuclideanSpace.single 1 (1 : ℝ))) 1) := by
  obtain ⟨r, hr, hinterval⟩ :=
    exists_commonControlledAxisInterval_of_centerParameter_eq
      boundary hboundaryRange a b u v hu hv hparameter
  refine ⟨r, hr, ?_⟩
  intro t ht
  obtain ⟨hsource, hA, hB, haxis⟩ := hinterval t ht
  have hsourceAxis :
      (Complex.orthonormalBasisOneI.repr (u * Complex.I) +
        t • EuclideanSpace.single 1 (1 : ℝ)) 0 = 0 := by
    simp [Complex.orthonormalBasisOneI_repr_apply,
      PiLp.add_apply, PiLp.smul_apply]
  refine ⟨hsource, hA, hB, haxis, ?_⟩
  exact controlledBoundaryCenterParameter_eq_of_transition_axis
    boundary a b hsource hsourceAxis haxis

#print axioms centerParameter_eq_transition_source_and_apply
#print axioms exists_commonControlledAxisInterval_of_centerParameter_eq
#print axioms controlledBoundaryCenterParameter_eq_of_transition_axis
#print axioms exists_commonControlledAxisInterval_with_centerParameter_eq

end

end GromovFilling
