import GromovFilling.RiemannianChartAreaLocality
import GromovFilling.RiemannianChartIntegral
import GromovFilling.RiemannianControlledBoundaryInteriorAtlas
import GromovFilling.RiemannianControlledBoundaryOrientation

/-!
# Cancellation of controlled boundary-chart primitive errors

This file globalizes the primitive-error term in oriented chartwise weak
Stokes.  Compactly supported Euclidean extension data supplies integrability;
subordination confines each intrinsic error to its controlled chart; canonical
chart-area locality transfers its planar integral to surface area; and the
finite partition-of-unity derivative identity cancels the resulting surface
integrals exactly.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

local instance controlledBoundaryAreaCancellationEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- The complex-coordinate weak primitive error is integrable whenever its
cutoff is compactly supported Lipschitz and its finite complex map is
Lipschitz. -/
theorem integrable_finiteComplexWeakPrimitiveErrorComplex
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (finiteComplexWeakPrimitiveErrorComplex ρ F) := by
  let e : (ℝ × ℝ) ≃L[ℝ] ℂ := complexOfRealProd
  have hρe : LipschitzWith
      (Cρ * ‖e.toContinuousLinearMap‖₊) (ρ ∘ e) :=
    hρ.comp e.lipschitz
  have hFe : LipschitzWith
      (CF * ‖e.toContinuousLinearMap‖₊) (F ∘ e) :=
    hF.comp e.lipschitz
  have hρeCompact : HasCompactSupport (ρ ∘ e) :=
    hρCompact.comp_homeomorph e.toHomeomorph
  have hprod : Integrable
      (finiteComplexWeakPrimitiveError (ρ ∘ e) (F ∘ e)) :=
    integrable_finiteComplexWeakPrimitiveError hρe hρeCompact hFe
  have hcomp : Integrable
      (finiteComplexWeakPrimitiveErrorComplex ρ F ∘ e) := by
    apply hprod.congr
    filter_upwards with p
    exact finiteComplexWeakPrimitiveError_comp_complexOfRealProd ρ F p
  have hcomp' : Integrable
      (finiteComplexWeakPrimitiveErrorComplex ρ F ∘
        Complex.measurableEquivRealProd.symm) := by
    simpa only [e, complexOfRealProd, Complex.measurableEquivRealProd] using hcomp
  exact
    (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).1 hcomp'

/-- The Fréchet-derivative representative of the same Lipschitz primitive
error is integrable as well. -/
theorem integrable_finiteSymplecticFDerivPrimitiveError
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (finiteSymplecticFDerivPrimitiveError ρ F) := by
  have hweak :=
    integrable_finiteComplexWeakPrimitiveErrorComplex
      hρ hρCompact hF
  apply hweak.congr
  filter_upwards [hρ.ae_differentiableAt (μ := volume),
    hF.ae_differentiableAt (μ := volume)] with z hρz hFz
  exact finiteComplexWeakPrimitiveErrorComplex_eq_fderiv
    ρ F z hρz hFz

/-- Weak-Stokes extension data therefore provides an integrable planar
Fréchet primitive error. -/
theorem ControlledBoundaryChartWeakStokesData.integrable_primitiveError
    {M : Type uM} [PseudoEMetricSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) :
    Integrable
      (finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap) :=
  integrable_finiteSymplecticFDerivPrimitiveError
    D.cutoff_lipschitz D.cutoff_compact D.chartMap_lipschitz

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
interior point outside that cutoff's controlled chart image. -/
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
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
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
      (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
      (P.partition i) G x = 0 := by
  by_contra hxne
  have hxsupport : x ∈ support (fun y ↦
      orientedFiniteComplexRiemannianPrimitiveErrorDensity
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (P.partition i) G y) := hxne
  have hxtsupport : x ∈ tsupport (P.partition i) :=
    support_orientedFiniteComplexRiemannianPrimitiveErrorDensity_subset
      (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
      (P.partition i) G hxsupport
  apply hxImage
  rw [chosenControlledInteriorComplexChartDomain,
    image_controlledInteriorComplexChartDomain]
  exact ⟨P.controlledSubordinate i hxtsupport, hxInterior⟩

/-- Integrable finite intrinsic primitive errors cancel after integration
against any common measure. -/
theorem sum_integral_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero
    {E H M ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [MeasurableSpace M] [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    [Fintype κ]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : κ → M → ℝ) (G : M → ι → ℂ) (μ : Measure M)
    (hρ : ∀ j, MDifferentiable I (modelWithCornersSelf ℝ ℝ) (ρ j))
    (hsum : ∀ x, ∑ j, ρ j x = 1)
    (hint : ∀ j, Integrable (fun x ↦
      orientedFiniteComplexRiemannianPrimitiveErrorDensity
        I o (ρ j) G x) μ) :
    (∑ j, ∫ x,
      orientedFiniteComplexRiemannianPrimitiveErrorDensity
        I o (ρ j) G x ∂μ) = 0 := by
  calc
    (∑ j, ∫ x,
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          I o (ρ j) G x ∂μ) =
        ∫ x, ∑ j,
          orientedFiniteComplexRiemannianPrimitiveErrorDensity
            I o (ρ j) G x ∂μ := by
      symm
      rw [integral_finset_sum Finset.univ]
      intro j _hj
      exact hint j
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with x
      exact sum_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero
        I o ρ G x (fun j ↦ hρ j x) hsum

variable {M : Type uM} [PseudoEMetricSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- The signed chart-area primitive error is integrable on the open
half-plane. -/
theorem ControlledBoundaryChartWeakStokesData.integrable_areaPrimitiveErrorDensity
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (O : ControlledBoundaryAtlasOrientation P)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) (modelWithCornersSelf ℝ ℂ)
      (fun x ↦ G x j)) :
    Integrable (controlledBoundaryChartAreaPrimitiveErrorDensity P O i G)
      (volume.restrict complexRightOpenHalfPlane) := by
  have hraw : Integrable
      (finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap)
      (volume.restrict complexRightOpenHalfPlane) :=
    D.integrable_primitiveError.mono_measure Measure.restrict_le_self
  have hsigned : Integrable (fun z ↦ O.chartSign i *
      finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z)
      (volume.restrict complexRightOpenHalfPlane) :=
    hraw.const_mul (O.chartSign i)
  apply hsigned.congr
  filter_upwards
      [ae_restrict_mem isOpen_complexRightOpenHalfPlane.measurableSet] with z hz
  calc
    O.chartSign i *
        finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z =
      O.chartSign i *
        controlledBoundaryChartPrimitiveErrorDensity
          P O.tangentOrientation i G z := by
        rw [D.primitiveError_eq_chartDensity O.tangentOrientation hG hz]
    _ = controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z :=
      O.chartSign_mul_primitiveErrorDensity_eq_area i G hz

/-- The extension-based primitive error vanishes in the open half-plane
outside the controlled interior domain containing the cutoff support. -/
theorem ControlledBoundaryChartWeakStokesData.primitiveError_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzControlled : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z = 0 := by
  have hzRightClosed : z ∈ complexRightClosedHalfPlane := by
    change 0 ≤ z.re
    change 0 < z.re at hzRight
    exact hzRight.le
  have hcutoff : D.cutoff z = 0 := by
    rw [D.cutoff_eq hzRightClosed,
      controlledBoundaryChartCutoff_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P i hzRight hzControlled]
  exact finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
    D.cutoff D.chartMap z D.cutoff_nonneg hcutoff

/-- The canonical primitive-error chart density has the same controlled
interior support. -/
theorem controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzControlled : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z = 0 := by
  classical
  by_cases hzDomain : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · let I := modelWithCornersEuclideanHalfSpace 2
    let e := Complex.orthonormalBasisOneI.repr
    let F : ℂ → M := interiorComplexExtChart I e (P.center i)
    let s : Set ℂ :=
      chosenControlledInteriorComplexChartDomain I e (P.center i)
    have hzFull : z ∈ interiorComplexExtChartDomain I e (P.center i) := by
      rw [← halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane]
      exact ⟨hzDomain, hzRight⟩
    have hsSubsetFull : s ⊆
        interiorComplexExtChartDomain I e (P.center i) := by
      exact
        controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
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
        O i G (F z) hzInterior
          (by simpa only [F, s, I, e] using hzNotImage)
    rw [controlledBoundaryChartAreaPrimitiveErrorDensity, if_pos hzDomain]
    rw [show orientedFiniteComplexRiemannianPrimitiveErrorDensity
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (P.partition i) G
        (halfSpaceComplexExtChart (P.center i) z) = 0 by
      simpa only [F, I, e, halfSpaceComplexExtChart,
        interiorComplexExtChart] using hzero,
      mul_zero]
  · simp only [controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_neg hzDomain]

/-- For Lipschitz data, the signed extension-based primitive-error integral
is the canonical chart-area primitive-error integral.  Rademacher is used
only on the controlled interior support. -/
theorem ControlledBoundaryChartWeakStokesData.chartSign_mul_integral_primitiveError_eq_area_of_lipschitzWith
    [Nonempty M]
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (O : ControlledBoundaryAtlasOrientation P)
    {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    O.chartSign i *
        (∫ z in complexRightOpenHalfPlane,
          finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z := by
  let s : Set ℂ :=
    chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)
  have hsMeas : MeasurableSet s := by
    exact (isOpen_controlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) (P.center i))).measurableSet
  have hGdiff : ∀ᵐ z ∂volume.restrict s, ∀ j : ι,
      MDifferentiableAt
        (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
        (fun x ↦ G x j)
        (halfSpaceComplexExtChart (P.center i) z) := by
    simpa only [s] using
      (P.ae_mdifferentiableAt_comp_halfSpace_of_lipschitzWith
        (Classical.choice inferInstance) G hG i)
  rw [← integral_const_mul]
  apply integral_congr_ae
  rw [Filter.EventuallyEq,
    ae_restrict_iff' (μ := volume)
      isOpen_complexRightOpenHalfPlane.measurableSet]
  rw [ae_restrict_iff' (μ := volume) hsMeas] at hGdiff
  filter_upwards [hGdiff] with z hGz hzRight
  by_cases hz : z ∈ s
  · calc
      O.chartSign i *
          finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z =
        O.chartSign i *
          controlledBoundaryChartPrimitiveErrorDensity
            P O.tangentOrientation i G z := by
          rw [D.primitiveError_eq_chartDensity_of_mdifferentiableAt
            O.tangentOrientation (hGz hz) hzRight]
      _ = controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z :=
        O.chartSign_mul_primitiveErrorDensity_eq_area i G hzRight
  · rw [D.primitiveError_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        hzRight (by simpa only [s] using hz),
      controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P O i G hzRight (by simpa only [s] using hz),
      mul_zero]

/-- Fully genuine chart-local weak Stokes for a Lipschitz finite complex map.
All manifold differentiability inputs are discharged almost everywhere by
the controlled-domain Rademacher theorem. -/
theorem ControlledBoundaryChartWeakStokesData.integral_areaSymplecticDensity_eq_areaPrimitiveError_sub_signedBoundary_of_lipschitzWith
    [Nonempty M]
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (O : ControlledBoundaryAtlasOrientation P)
    {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
      (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  calc
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        O.chartSign i *
          (∫ z in complexRightOpenHalfPlane,
            controlledBoundaryChartSymplecticDensity P i G z) :=
      (O.chartSign_mul_integral_symplecticDensity_eq_area_of_lipschitzWith
        i G hG).symm
    _ = O.chartSign i *
        ((∫ z in complexRightOpenHalfPlane,
            finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z) -
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y) := by
      rw [D.integral_controlledBoundaryChartSymplecticDensity_eq]
    _ = O.chartSign i *
          (∫ z in complexRightOpenHalfPlane,
            finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      ring
    _ = (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      rw [D.chartSign_mul_integral_primitiveError_eq_area_of_lipschitzWith
        O hG]

/-- One chart-area primitive-error integral is exactly the integral of its
intrinsic density against canonical Riemannian surface area.  Lipschitz
regularity supplies the coordinatewise manifold differentiability needed
for the chart identity almost everywhere by Rademacher.  The conclusion also
records the integrability needed for finite summation. -/
theorem ControlledBoundaryChartWeakStokesData.integrable_and_integral_areaPrimitiveErrorDensity_eq_surface
    [Nonempty M]
    [Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M)]
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (O : ControlledBoundaryAtlasOrientation P)
    {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    let q : M → ℝ := fun x ↦
      orientedFiniteComplexRiemannianPrimitiveErrorDensity
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (P.partition i) G x
    let μ := riemannianSurfaceAreaMeasure
      (modelWithCornersEuclideanHalfSpace 2)
    Integrable q μ ∧
      (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) =
        ∫ x, q x ∂μ := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e := Complex.orthonormalBasisOneI.repr
  let F : ℂ → M := interiorComplexExtChart I e (P.center i)
  let sFull : Set ℂ := interiorComplexExtChartDomain I e (P.center i)
  let s : Set ℂ :=
    chosenControlledInteriorComplexChartDomain I e (P.center i)
  let U : Set M := F '' s
  let q : M → ℝ := fun x ↦
    orientedFiniteComplexRiemannianPrimitiveErrorDensity
      I O.tangentOrientation (P.partition i) G x
  let μ : Measure M := riemannianSurfaceAreaMeasure I
  let A : ControlledInteriorAtlas I M :=
    P.toControlledInteriorAtlas (Classical.choice inferInstance)
  let k : ℕ := (Fintype.equivFin P.ι i : Fin (Fintype.card P.ι))
  have hsMeas : MeasurableSet s := by
    exact (isOpen_controlledInteriorComplexChartDomain I e
      (chosenInteriorChartControl I (P.center i))).measurableSet
  have hsFullMeas : MeasurableSet sFull :=
    (isOpen_interiorComplexExtChartDomain I e (P.center i)).measurableSet
  have hsSubsetFull : s ⊆ sFull := by
    exact controlledInteriorComplexChartDomain_subset_interiorComplexExtChartDomain
      I e (chosenInteriorChartControl I (P.center i))
  have hsFullEq : sFull =
      halfSpaceComplexExtChartDomain (P.center i) ∩
        complexRightOpenHalfPlane := by
    exact (halfSpaceComplexExtChartDomain_inter_rightOpenHalfPlane
      (P.center i)).symm
  have hsSubsetRight : s ⊆ complexRightOpenHalfPlane := by
    intro z hz
    have hzFull : z ∈ sFull := hsSubsetFull hz
    rw [hsFullEq] at hzFull
    exact hzFull.2
  have hFcont : ContinuousOn F s := by
    exact (continuousOn_interiorComplexExtChart I e (P.center i)).mono
      hsSubsetFull
  have hFinj : Set.InjOn F s := by
    exact (injOn_interiorComplexExtChart I e (P.center i)).mono
      hsSubsetFull
  have hDensity : AEMeasurable (riemannianChartDensity I F)
      (volume.restrict s) := by
    exact aemeasurable_riemannianChartDensity_of_contMDiffOn
      I F s
      (isOpen_controlledInteriorComplexChartDomain I e
        (chosenInteriorChartControl I (P.center i)))
      ((contMDiffOn_interiorComplexExtChart I e (P.center i)).mono
        hsSubsetFull)
  have hGdiff : ∀ᵐ z ∂volume.restrict s, ∀ j : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x j) (F z) := by
    simpa only [s, F, I, halfSpaceComplexExtChart,
      interiorComplexExtChart] using
      (P.ae_mdifferentiableAt_comp_halfSpace_of_lipschitzWith
        (Classical.choice inferInstance) G hG i)
  have hrawS : Integrable
      (finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap)
      (volume.restrict s) :=
    D.integrable_primitiveError.mono_measure Measure.restrict_le_self
  have hsignedS : Integrable (fun z ↦ O.chartSign i *
      finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z)
      (volume.restrict s) :=
    hrawS.const_mul (O.chartSign i)
  have hareaS : Integrable
      (controlledBoundaryChartAreaPrimitiveErrorDensity P O i G)
      (volume.restrict s) := by
    apply hsignedS.congr
    filter_upwards [ae_restrict_mem hsMeas, hGdiff] with z hz hGz
    have hzRight : z ∈ complexRightOpenHalfPlane := hsSubsetRight hz
    calc
      O.chartSign i *
          finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z =
        O.chartSign i *
          controlledBoundaryChartPrimitiveErrorDensity
            P O.tangentOrientation i G z := by
          rw [D.primitiveError_eq_chartDensity_of_mdifferentiableAt
            O.tangentOrientation hGz hzRight]
      _ = controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z :=
        O.chartSign_mul_primitiveErrorDensity_eq_area i G hzRight
  have hweightedS : Integrable (fun z ↦
      (riemannianChartDensity I F z).toReal * q (F z))
      (volume.restrict s) := by
    apply hareaS.congr
    filter_upwards [ae_restrict_mem hsMeas] with z hz
    have hzFull : z ∈ sFull := hsSubsetFull hz
    rw [hsFullEq] at hzFull
    simp only [controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_pos hzFull.1, q, F, I, e, halfSpaceComplexExtChart,
      interiorComplexExtChart]
  have hqChart : Integrable q
      (riemannianChartAreaMeasure I F s) :=
    integrable_riemannianChartAreaMeasure_real_of_integrable_weighted
      I F s hsMeas hFcont hFinj hDensity q hweightedS
  have hlocality : μ.restrict U =
      riemannianChartAreaMeasure I F s := by
    have h := riemannianSurfaceAreaMeasure_restrict_chart_image I A k
    simpa only [μ, U, F, s, A, k,
      FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_parametrization,
      FiniteControlledBoundaryChartPartition.toControlledInteriorAtlas_domain]
      using h
  have hμInterior : ∀ᵐ x ∂μ, x ∈ I.interior M := by
    change ∀ᵐ x ∂riemannianSurfaceAreaMeasure I,
      x ∈ I.interior M
    rw [← riemannianSurfaceAreaMeasure_restrict_interior I]
    exact ae_restrict_mem (I.isOpen_interior one_ne_zero).measurableSet
  have hqzero : ∀ᵐ x ∂μ, x ∉ U → q x = 0 := by
    filter_upwards [hμInterior] with x hxInterior hxU
    exact P.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
      O i G x hxInterior (by simpa only [U, F, s, I, e] using hxU)
  have hqU : IntegrableOn q U μ := by
    change Integrable q (μ.restrict U)
    rw [hlocality]
    exact hqChart
  have hqGlobal : Integrable q μ := by
    have hqUniv : IntegrableOn q Set.univ μ :=
      hqU.of_ae_diff_eq_zero nullMeasurableSet_univ (by
        filter_upwards [hqzero] with x hx hxDiff
        exact hx hxDiff.2)
    simpa only [integrableOn_univ] using hqUniv
  have hfullToS :
      (∫ z in sFull,
          (riemannianChartDensity I F z).toReal * q (F z)) =
        ∫ z in s,
          (riemannianChartDensity I F z).toReal * q (F z) := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hsFullMeas hsSubsetFull
    rintro z ⟨hzFull, hzs⟩
    have hzInterior : F z ∈ I.interior M := by
      have hzImage :
          interiorComplexExtChart I e (P.center i) z ∈
            interiorComplexExtChart I e (P.center i) ''
              interiorComplexExtChartDomain I e (P.center i) :=
        ⟨z, hzFull, rfl⟩
      rw [image_interiorComplexExtChartDomain I e (P.center i)] at hzImage
      simpa only [F] using hzImage.2
    have hzNotImage : F z ∉ U := by
      rintro ⟨w, hw, hwz⟩
      have hwFull : w ∈ sFull := hsSubsetFull hw
      have hzw : z = w :=
        injOn_interiorComplexExtChart I e (P.center i)
          hzFull hwFull hwz.symm
      exact hzs (hzw ▸ hw)
    have hqzero : q (F z) = 0 := by
      simpa only [q] using
        P.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
          O i G (F z) hzInterior
            (by simpa only [U, F, s, I, e] using hzNotImage)
    rw [hqzero, mul_zero]
  have hrightToFull :
      (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) =
        ∫ z in sFull,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      isOpen_complexRightOpenHalfPlane.measurableSet
      (by rw [hsFullEq]; exact inter_subset_right)
    rintro z ⟨hzRight, hzNotFull⟩
    have hzNotDomain : z ∉ halfSpaceComplexExtChartDomain (P.center i) := by
      intro hzDomain
      exact hzNotFull (hsFullEq.symm ▸ ⟨hzDomain, hzRight⟩)
    simp only [controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_neg hzNotDomain]
  have hfullArea :
      (∫ z in sFull,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) =
        ∫ z in sFull,
          (riemannianChartDensity I F z).toReal * q (F z) := by
    apply setIntegral_congr_fun hsFullMeas
    intro z hz
    rw [hsFullEq] at hz
    simp only [controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_pos hz.1, q, F, I, e, halfSpaceComplexExtChart,
      interiorComplexExtChart]
  refine ⟨hqGlobal, ?_⟩
  calc
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) =
        ∫ z in sFull,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z :=
      hrightToFull
    _ = ∫ z in sFull,
          (riemannianChartDensity I F z).toReal * q (F z) := hfullArea
    _ = ∫ z in s,
          (riemannianChartDensity I F z).toReal * q (F z) := hfullToS
    _ = ∫ x, q x ∂riemannianChartAreaMeasure I F s := by
      symm
      exact integral_riemannianChartAreaMeasure_real
        I F s (hFcont.aemeasurable hsMeas) hDensity q
          hqChart.aestronglyMeasurable
    _ = ∫ x, q x ∂μ.restrict U := by rw [hlocality]
    _ = ∫ x, q x ∂μ :=
      setIntegral_eq_integral_of_ae_compl_eq_zero hqzero

/-- The finite sum of all oriented chart-area primitive errors vanishes
exactly.  This is the global partition-of-unity cancellation required after
sign-weighted local weak Stokes. -/
theorem sum_integral_controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero
    [Nonempty M]
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P) (G : M → ι → ℂ)
    {CG : ℝ≥0} (hGLipschitz : LipschitzWith CG G) :
    (∑ i, ∫ z in complexRightOpenHalfPlane,
      controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) = 0 := by
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
      (Classical.choice inferInstance)
  let D : ∀ i : P.ι, ControlledBoundaryChartWeakStokesData P i G :=
    fun i ↦ Classical.choice
      (nonempty_controlledBoundaryChartWeakStokesData P i G hGLipschitz)
  have htransfer (i : P.ι) :=
    (D i).integrable_and_integral_areaPrimitiveErrorDensity_eq_surface
      O hGLipschitz
  calc
    (∑ i, ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) =
      ∑ i, ∫ x,
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
          (P.partition i) G x
          ∂riemannianSurfaceAreaMeasure
            (modelWithCornersEuclideanHalfSpace 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (htransfer i).2
    _ = 0 :=
      sum_integral_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (fun i ↦ P.partition i) G
        (riemannianSurfaceAreaMeasure
          (modelWithCornersEuclideanHalfSpace 2))
        (fun i ↦ (P.contMDiff_partition i).mdifferentiable (by simp))
        P.sum_partition_eq_one
        (fun i ↦ (htransfer i).1)

#print axioms integrable_finiteComplexWeakPrimitiveErrorComplex
#print axioms integrable_finiteSymplecticFDerivPrimitiveError
#print axioms ControlledBoundaryChartWeakStokesData.integrable_primitiveError
#print axioms riemannianRealMFDeriv_eq_zero_of_notMem_tsupport
#print axioms
  orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero_of_notMem_tsupport
#print axioms
  support_orientedFiniteComplexRiemannianPrimitiveErrorDensity_subset
#print axioms
  FiniteControlledBoundaryChartPartition.primitiveErrorDensity_eq_zero_of_interior_of_not_mem_image
#print axioms
  sum_integral_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero
#print axioms
  ControlledBoundaryChartWeakStokesData.integrable_areaPrimitiveErrorDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.primitiveError_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  ControlledBoundaryChartWeakStokesData.chartSign_mul_integral_primitiveError_eq_area_of_lipschitzWith
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_areaSymplecticDensity_eq_areaPrimitiveError_sub_signedBoundary_of_lipschitzWith
#print axioms
  ControlledBoundaryChartWeakStokesData.integrable_and_integral_areaPrimitiveErrorDensity_eq_surface
#print axioms
  sum_integral_controlledBoundaryChartAreaPrimitiveErrorDensity_eq_zero

end

end GromovFilling
