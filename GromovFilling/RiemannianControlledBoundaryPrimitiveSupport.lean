import GromovFilling.RiemannianControlledBoundaryPrimitive

/-!
# Support of controlled boundary-chart primitive errors

The intrinsic primitive-error density is local in its cutoff: outside the
closed support of that cutoff, the manifold differential vanishes.  For a
controlled boundary partition, subordination then confines the density to
the corresponding controlled interior-chart image.

These support facts are independent of the integration and
partition-of-unity cancellation arguments in
`RiemannianControlledBoundaryAreaCancellation`.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped Bundle ContDiff Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

local instance controlledBoundaryPrimitiveSupportEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- Outside the closed support of a real function, its Riemannian manifold
differential vanishes. -/
theorem riemannianRealMFDeriv_eq_zero_of_notMem_tsupport
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (ρ : M → ℝ) (x : M) (hx : x ∉ tsupport ρ) :
    riemannianRealMFDeriv I ρ x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hx
  have hzero : mfderiv I (modelWithCornersSelf ℝ ℝ) ρ x = 0 := by
    calc
      mfderiv I (modelWithCornersSelf ℝ ℝ) ρ x =
          mfderiv I (modelWithCornersSelf ℝ ℝ)
            (fun _ : M ↦ (0 : ℝ)) x :=
        hx.mfderiv_eq
      _ = 0 := mfderiv_const
  unfold riemannianRealMFDeriv
  rw [hzero]
  simp

/-- Consequently, the intrinsic oriented primitive-error density is
supported inside the closed support of its cutoff. -/
theorem orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero_of_notMem_tsupport
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : M → ℝ) (G : M → ι → ℂ) (x : M)
    (hx : x ∉ tsupport ρ) :
    orientedFiniteComplexRiemannianPrimitiveErrorDensity
      I o ρ G x = 0 := by
  unfold orientedFiniteComplexRiemannianPrimitiveErrorDensity
  rw [riemannianRealMFDeriv_eq_zero_of_notMem_tsupport I ρ x hx]
  simp

/-- Support form of the preceding vanishing statement. -/
theorem support_orientedFiniteComplexRiemannianPrimitiveErrorDensity_subset
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : M → ℝ) (G : M → ι → ℂ) :
    support (fun x ↦
      orientedFiniteComplexRiemannianPrimitiveErrorDensity I o ρ G x) ⊆
        tsupport ρ := by
  intro x hx
  by_contra hxt
  exact hx
    (orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero_of_notMem_tsupport
      I o ρ G x hxt)

/-- The intrinsic primitive error of one controlled cutoff vanishes at every
interior point outside that cutoff's controlled chart image.  Only the
tangent-plane orientation is needed; chart signs enter later when the local
identities are converted to unsigned surface area. -/
theorem FiniteControlledBoundaryChartPartition.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
    {M : Type uM} [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {ι : Type uι} [Fintype ι] [Finite ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (i : P.ι)
    (G : M → ι → ℂ) (x : M)
    (hxInterior : x ∈
      (modelWithCornersEuclideanHalfSpace 2).interior M)
    (hxImage : x ∉
      interiorComplexExtChart
          (modelWithCornersEuclideanHalfSpace 2)
          Complex.orthonormalBasisOneI.repr (P.center i) ''
        chosenControlledInteriorComplexChartDomain
          (modelWithCornersEuclideanHalfSpace 2)
          Complex.orthonormalBasisOneI.repr (P.center i)) :
    orientedFiniteComplexRiemannianPrimitiveErrorDensity
      (modelWithCornersEuclideanHalfSpace 2) o
      (P.partition i) G x = 0 := by
  by_contra hxne
  have hxsupport : x ∈ support (fun y ↦
      orientedFiniteComplexRiemannianPrimitiveErrorDensity
        (modelWithCornersEuclideanHalfSpace 2) o
        (P.partition i) G y) := hxne
  have hxtsupport : x ∈ tsupport (P.partition i) :=
    support_orientedFiniteComplexRiemannianPrimitiveErrorDensity_subset
      (modelWithCornersEuclideanHalfSpace 2) o
      (P.partition i) G hxsupport
  apply hxImage
  rw [chosenControlledInteriorComplexChartDomain,
    image_controlledInteriorComplexChartDomain]
  exact ⟨P.controlledSubordinate i hxtsupport, hxInterior⟩

/-- On the actual inverse-chart domain, the intrinsic primitive error
vanishes outside the chosen controlled interior domain containing the cutoff
support. -/
theorem orientedFiniteComplexRiemannianPrimitiveErrorDensity_comp_halfSpaceChart_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {M : Type uM} [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {ι : Type uι} [Fintype ι] [Finite ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzDomain : z ∈ halfSpaceComplexExtChartDomain (P.center i))
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzControlled : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    orientedFiniteComplexRiemannianPrimitiveErrorDensity
      (modelWithCornersEuclideanHalfSpace 2) o
      (P.partition i) G (halfSpaceComplexExtChart (P.center i) z) = 0 := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e := Complex.orthonormalBasisOneI.repr
  let F : ℂ → M := interiorComplexExtChart I e (P.center i)
  let s : Set ℂ :=
    chosenControlledInteriorComplexChartDomain I e (P.center i)
  have hzFull : z ∈ interiorComplexExtChartDomain I e (P.center i) := by
    rw [← halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane]
    exact ⟨hzDomain, hzRight⟩
  have hsSubsetFull : s ⊆
      interiorComplexExtChartDomain I e (P.center i) := by
    exact controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
      I e (chosenInteriorChartControl I (P.center i))
  have hzInterior : F z ∈ I.interior M := by
    have hzImage :
        interiorComplexExtChart I e (P.center i) z ∈
          interiorComplexExtChart I e (P.center i) ''
            interiorComplexExtChartDomain I e (P.center i) :=
      ⟨z, hzFull, rfl⟩
    rw [image_interiorComplexExtChartDomain I e (P.center i)] at hzImage
    simpa only [F] using hzImage.2
  have hzNotS : z ∉ s := by
    simpa only [s, I, e] using hzControlled
  have hzNotImage : F z ∉ F '' s := by
    rintro ⟨w, hw, hwz⟩
    have hwFull := hsSubsetFull hw
    have hzw : z = w :=
      injOn_interiorComplexExtChart I e (P.center i)
        hzFull hwFull hwz.symm
    exact hzNotS (hzw ▸ hw)
  have hzero :=
    P.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
      o i G (F z) hzInterior
        (by simpa only [F, s, I, e] using hzNotImage)
  simpa only [F, I, e, halfSpaceComplexExtChart,
    interiorComplexExtChart] using hzero

/-- The genuine signed controlled-chart primitive density vanishes in the
open half-plane outside the chosen controlled interior domain containing its
cutoff support. -/
theorem controlledBoundaryChartPrimitiveErrorDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {M : Type uM} [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {ι : Type uι} [Fintype ι] [Finite ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzControlled : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    controlledBoundaryChartPrimitiveErrorDensity P o i G z = 0 := by
  classical
  by_cases hzDomain : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · rw [controlledBoundaryChartPrimitiveErrorDensity, if_pos hzDomain,
      orientedFiniteComplexRiemannianPrimitiveErrorDensity_comp_halfSpaceChart_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P o i G hzDomain hzRight hzControlled,
      mul_zero]
  · simp only [controlledBoundaryChartPrimitiveErrorDensity, if_neg hzDomain]

#print axioms riemannianRealMFDeriv_eq_zero_of_notMem_tsupport
#print axioms
  orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero_of_notMem_tsupport
#print axioms
  support_orientedFiniteComplexRiemannianPrimitiveErrorDensity_subset
#print axioms
  FiniteControlledBoundaryChartPartition.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
#print axioms
  orientedFiniteComplexRiemannianPrimitiveErrorDensity_comp_halfSpaceChart_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  controlledBoundaryChartPrimitiveErrorDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain

end

end GromovFilling
