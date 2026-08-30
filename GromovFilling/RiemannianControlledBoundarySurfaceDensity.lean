import GromovFilling.RiemannianControlledBoundaryAreaCancellation

/-!
# Intrinsic surface integration for controlled symplectic densities

The global controlled-chart Stokes theorem initially leaves its interior
term as a finite sum of planar chart integrals.  This module transfers each
such integral to canonical Riemannian surface area.  The partition of unity
then identifies their sum with the integral of the intrinsic signed
symplectic density.

No boundary parametrization or comass estimate is used here.  Those remain
separate downstream obligations.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped BigOperators Bundle ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

local instance controlledBoundarySurfaceDensityEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- The complex-coordinate weak symplectic density is integrable after
multiplication by a compactly supported Lipschitz cutoff. -/
theorem integrable_cutoff_mul_finiteComplexWeakSymplecticDensityComplex
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (fun z ↦
      ρ z * finiteComplexWeakSymplecticDensityComplex F z) := by
  let e : (ℝ × ℝ) ≃L[ℝ] ℂ := complexOfRealProd
  have hρe : LipschitzWith
      (Cρ * ‖e.toContinuousLinearMap‖₊) (ρ ∘ e) :=
    hρ.comp e.lipschitz
  have hFe : LipschitzWith
      (CF * ‖e.toContinuousLinearMap‖₊) (F ∘ e) :=
    hF.comp e.lipschitz
  have hρeCompact : HasCompactSupport (ρ ∘ e) :=
    hρCompact.comp_homeomorph e.toHomeomorph
  have hprod : Integrable (fun p : ℝ × ℝ ↦
      (ρ ∘ e) p * finiteComplexWeakSymplecticDensity (F ∘ e) p) :=
    integrable_cutoff_mul_finiteComplexWeakSymplecticDensity
      hρe hρeCompact hFe
  have hcomp : Integrable
      ((fun z ↦ ρ z * finiteComplexWeakSymplecticDensityComplex F z) ∘ e) := by
    apply hprod.congr
    filter_upwards with p
    simp only [Function.comp_apply]
    rw [finiteComplexWeakSymplecticDensity_comp_complexOfRealProd]
  have hcomp' : Integrable
      ((fun z ↦ ρ z * finiteComplexWeakSymplecticDensityComplex F z) ∘
        Complex.measurableEquivRealProd.symm) := by
    simpa only [e, complexOfRealProd, Complex.measurableEquivRealProd] using hcomp
  exact
    (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).1 hcomp'

/-- The Fréchet representative of the same cutoff-weighted symplectic
density is integrable. -/
theorem integrable_cutoff_mul_finiteSymplecticFDerivDensity
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    Integrable (fun z ↦ ρ z * finiteSymplecticFDerivDensity F z) := by
  have hweak :=
    integrable_cutoff_mul_finiteComplexWeakSymplecticDensityComplex
      hρ hρCompact hF
  apply hweak.congr
  filter_upwards [hF.ae_differentiableAt (μ := volume)] with z hFz
  rw [finiteComplexWeakSymplecticDensityComplex_eq_fderiv F z hFz]

/-- Weak-Stokes extension data supplies an integrable cutoff-weighted
Fréchet symplectic density. -/
theorem ControlledBoundaryChartWeakStokesData.integrable_weightedSymplecticDensity
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
    Integrable (fun z ↦
      D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z) :=
  integrable_cutoff_mul_finiteSymplecticFDerivDensity
    D.cutoff_lipschitz D.cutoff_compact D.chartMap_lipschitz

/-- One chart-area symplectic integral is exactly the integral of the
partition-weighted intrinsic signed density against canonical Riemannian
surface area.  The result also records the integrability needed for finite
summation. -/
theorem ControlledBoundaryChartWeakStokesData.integrable_and_integral_areaSymplecticDensity_eq_surface
    {M : Type uM} [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
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
      P.partition i x *
        orientedFiniteComplexRiemannianSymplecticDensity
          (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation G x
    let μ := riemannianSurfaceAreaMeasure
      (modelWithCornersEuclideanHalfSpace 2)
    Integrable q μ ∧
      (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        ∫ x, q x ∂μ := by
  let I := modelWithCornersEuclideanHalfSpace 2
  let e := Complex.orthonormalBasisOneI.repr
  let F : ℂ → M := interiorComplexExtChart I e (P.center i)
  let sFull : Set ℂ := interiorComplexExtChartDomain I e (P.center i)
  let s : Set ℂ :=
    chosenControlledInteriorComplexChartDomain I e (P.center i)
  let U : Set M := F '' s
  let q : M → ℝ := fun x ↦
    P.partition i x *
      orientedFiniteComplexRiemannianSymplecticDensity
        I O.tangentOrientation G x
  let μ := riemannianSurfaceAreaMeasure I
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
  have hrawS : Integrable (fun z ↦
      D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z)
      (volume.restrict s) :=
    D.integrable_weightedSymplecticDensity.mono_measure
      Measure.restrict_le_self
  have hsignedS : Integrable (fun z ↦ O.chartSign i *
      (D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z))
      (volume.restrict s) :=
    hrawS.const_mul (O.chartSign i)
  have hareaS : Integrable
      (controlledBoundaryChartAreaSymplecticDensity P O i G)
      (volume.restrict s) := by
    apply hsignedS.congr
    filter_upwards [ae_restrict_mem hsMeas, hGdiff] with z hz hGz
    have hzRight : z ∈ complexRightOpenHalfPlane := hsSubsetRight hz
    calc
      O.chartSign i *
          (D.cutoff z * finiteSymplecticFDerivDensity D.chartMap z) =
        O.chartSign i * controlledBoundaryChartSymplecticDensity P i G z := by
          rw [D.weightedSymplecticDensity_eq hzRight]
      _ = controlledBoundaryChartAreaSymplecticDensity P O i G z :=
        O.chartSign_mul_symplecticDensity_eq_area_of_mdifferentiableAt
          i G hGz hzRight
  have hweightedS : Integrable (fun z ↦
      (riemannianChartDensity I F z).toReal * q (F z))
      (volume.restrict s) := by
    apply hareaS.congr
    filter_upwards [ae_restrict_mem hsMeas] with z hz
    have hzFull : z ∈ sFull := hsSubsetFull hz
    rw [hsFullEq] at hzFull
    simp only [controlledBoundaryChartAreaSymplecticDensity,
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
    rw [← riemannianSurfaceAreaMeasure_restrict_interior I]
    exact ae_restrict_mem (I.isOpen_interior one_ne_zero).measurableSet
  have hqzero : ∀ᵐ x ∂μ, x ∉ U → q x = 0 := by
    filter_upwards [hμInterior] with x hxInterior hxU
    by_cases hpartition : P.partition i x = 0
    · simp only [q, hpartition, zero_mul]
    · exfalso
      apply hxU
      rw [chosenControlledInteriorComplexChartDomain,
        image_controlledInteriorComplexChartDomain]
      exact ⟨P.controlledSubordinate i (subset_closure hpartition), hxInterior⟩
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
      exact (image_interiorComplexExtChartDomain I e (P.center i) ▸
        ⟨z, hzFull, rfl⟩).2
    have hzNotImage : F z ∉ U := by
      rintro ⟨w, hw, hwz⟩
      have hwFull : w ∈ sFull := hsSubsetFull hw
      have hzw : z = w :=
        injOn_interiorComplexExtChart I e (P.center i)
          hzFull hwFull hwz.symm
      exact hzs (hzw ▸ hw)
    have hpartition : P.partition i (F z) = 0 := by
      by_contra hp
      apply hzNotImage
      rw [chosenControlledInteriorComplexChartDomain,
        image_controlledInteriorComplexChartDomain]
      exact ⟨P.controlledSubordinate i (subset_closure hp), hzInterior⟩
    simp only [q, hpartition, zero_mul, mul_zero]
  have hrightToFull :
      (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        ∫ z in sFull,
          controlledBoundaryChartAreaSymplecticDensity P O i G z := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      isOpen_complexRightOpenHalfPlane.measurableSet
      (by rw [hsFullEq]; exact inter_subset_right)
    rintro z ⟨hzRight, hzNotFull⟩
    have hzNotDomain : z ∉ halfSpaceComplexExtChartDomain (P.center i) := by
      intro hzDomain
      exact hzNotFull (hsFullEq.symm ▸ ⟨hzDomain, hzRight⟩)
    simp only [controlledBoundaryChartAreaSymplecticDensity,
      if_neg hzNotDomain]
  have hfullArea :
      (∫ z in sFull,
          controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        ∫ z in sFull,
          (riemannianChartDensity I F z).toReal * q (F z) := by
    apply setIntegral_congr_fun hsFullMeas
    intro z hz
    rw [hsFullEq] at hz
    simp only [controlledBoundaryChartAreaSymplecticDensity,
      if_pos hz.1, q, F, I, e, halfSpaceComplexExtChart,
      interiorComplexExtChart]
  refine ⟨hqGlobal, ?_⟩
  calc
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        ∫ z in sFull,
          controlledBoundaryChartAreaSymplecticDensity P O i G z :=
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

/-- Summing the chart transfers removes the partition of unity and produces
one intrinsic signed surface integral. -/
theorem sum_integral_controlledBoundaryChartAreaSymplecticDensity_eq_surface
    {M : Type uM} [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    [Nonempty M]
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P) (G : M → ι → ℂ)
    {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    let q : M → ℝ := fun x ↦
      orientedFiniteComplexRiemannianSymplecticDensity
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation G x
    let μ := riemannianSurfaceAreaMeasure
      (modelWithCornersEuclideanHalfSpace 2)
    Integrable q μ ∧
      (∑ i, ∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        ∫ x, q x ∂μ := by
  let I := modelWithCornersEuclideanHalfSpace 2
  letI : Nonempty (ControlledInteriorAtlas I M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
      (Classical.choice inferInstance)
  let D : ∀ i : P.ι, ControlledBoundaryChartWeakStokesData P i G :=
    fun i ↦ Classical.choice
      (nonempty_controlledBoundaryChartWeakStokesData P i G hG)
  let q : M → ℝ := fun x ↦
    orientedFiniteComplexRiemannianSymplecticDensity
      I O.tangentOrientation G x
  let qi : P.ι → M → ℝ := fun i x ↦ P.partition i x * q x
  let μ := riemannianSurfaceAreaMeasure I
  have htransfer (i : P.ι) :=
    (D i).integrable_and_integral_areaSymplecticDensity_eq_surface O hG
  have hqi (i : P.ι) : Integrable (qi i) μ := by
    simpa only [qi, q, μ, I] using (htransfer i).1
  have hsumPoint (x : M) : (∑ i, qi i x) = q x := by
    simp only [qi, ← Finset.sum_mul, P.sum_partition_eq_one, one_mul]
  have hq : Integrable q μ := by
    apply (integrable_finset_sum Finset.univ fun i _hi ↦ hqi i).congr
    filter_upwards with x
    exact (hsumPoint x).symm
  refine ⟨hq, ?_⟩
  calc
    (∑ i, ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
      ∑ i, ∫ x, qi i x ∂μ := by
        apply Finset.sum_congr rfl
        intro i _hi
        simpa only [qi, q, μ, I] using (htransfer i).2
    _ = ∫ x, ∑ i, qi i x ∂μ := by
      rw [integral_finset_sum Finset.univ]
      intro i _hi
      exact hqi i
    _ = ∫ x, q x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact hsumPoint x

#print axioms
  integrable_cutoff_mul_finiteComplexWeakSymplecticDensityComplex
#print axioms integrable_cutoff_mul_finiteSymplecticFDerivDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.integrable_weightedSymplecticDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.integrable_and_integral_areaSymplecticDensity_eq_surface
#print axioms
  sum_integral_controlledBoundaryChartAreaSymplecticDensity_eq_surface

end

end GromovFilling
