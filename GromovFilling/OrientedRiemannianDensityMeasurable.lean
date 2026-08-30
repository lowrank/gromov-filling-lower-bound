import GromovFilling.OrientedRiemannianChartDensity
import GromovFilling.RiemannianInteriorAtlasArea

/-!
# Measurability of absolute oriented Riemannian densities

An orientation field on a Riemannian surface is only fiberwise data, so its
sign need not be measurable.  The absolute intrinsic symplectic density is
nevertheless canonical: its chart pullback is the measurable planar
Fréchet-derivative density divided by the chart-area weight.  This file makes
that weighted transfer first on one controlled chart piece and then for the
canonical Riemannian surface-area measure.
-/

open Bundle Function MeasureTheory Set
open scoped Bundle ENNReal Function Manifold NNReal Topology

namespace GromovFilling

noncomputable section

local instance complexFinrankTwoFactOrientedDensityMeasurable :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The planar finite symplectic Fréchet-derivative density is measurable for
every finite complex coordinate family. -/
theorem measurable_finiteSymplecticFDerivDensity
    {ι : Type*} [Fintype ι] [Finite ι] (F : ℂ → ι → ℂ) :
    Measurable (finiteSymplecticFDerivDensity F) := by
  change Measurable (fun z ↦ standardComplexSymplecticBilinear
    ((fderiv ℝ F z) 1) ((fderiv ℝ F z) Complex.I))
  exact standardComplexSymplecticBilinear.continuous₂.measurable.comp
    ((measurable_fderiv_apply_const ℝ F 1).prodMk
      (measurable_fderiv_apply_const ℝ F Complex.I))

namespace ControlledInteriorAtlas

/-- On one controlled chart piece, the absolute intrinsic finite symplectic
density of a globally Lipschitz finite complex map is almost everywhere
measurable for the chart-area measure. -/
theorem aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity_of_lipschitzWith
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Fintype ι] [Finite ι]
    (A : ControlledInteriorAtlas I M)
    (o : RiemannianTangentPlaneOrientation I M) (G : M → ι → ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G) (i : ℕ) :
    AEMeasurable
      (fun x ↦ ENNReal.ofReal
        |orientedFiniteComplexRiemannianSymplecticDensity I o G x|)
      (riemannianChartAreaMeasure I (A.parametrization i)
        (A.piece I i)) := by
  let F : ℂ → M := A.parametrization i
  let s : Set ℂ := A.piece I i
  let q : M → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    |orientedFiniteComplexRiemannianSymplecticDensity I o G x|
  let d : ℂ → ℝ≥0∞ := riemannianChartDensity I F
  let dNN : ℂ → ℝ≥0 := fun z ↦ (d z).toNNReal
  let planarQ : ℂ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal |finiteSymplecticFDerivDensity (G ∘ F) z|
  have hs : MeasurableSet s := by
    simpa only [s] using A.measurableSet_piece I i
  have hsDomain : s ⊆ A.domain i := by
    simpa only [s] using A.piece_subset_domain I i
  have hFcont : ContinuousOn F s := by
    exact (A.continuousOn_parametrization i).mono hsDomain
  have hFinj : Set.InjOn F s := by
    exact (A.injOn_parametrization i).mono hsDomain
  have hFembed : MeasurableEmbedding (s.restrict F) :=
    hFcont.measurableEmbedding hs hFinj
  have hFbase : AEMeasurable F (volume.restrict s) :=
    hFcont.aemeasurable hs
  have hd : AEMeasurable d (volume.restrict s) := by
    simpa only [d, F] using
      AEMeasurable.mono_set hsDomain
        (aemeasurable_riemannianChartDensity_of_contMDiffOn I
          (A.parametrization i) (A.domain i) (A.isOpen_domain i)
            (A.contMDiffOn_parametrization i))
  have hdNN : AEMeasurable dNN (volume.restrict s) := by
    exact hd.ennreal_toNNReal
  have hplanarQ : Measurable planarQ := by
    exact ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp
        (measurable_finiteSymplecticFDerivDensity (G ∘ F)))
  have hGdiff : ∀ᵐ z ∂volume.restrict (A.piece I i), ∀ j : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x j)
        (A.parametrization i z) := by
    rw [ae_all_iff]
    intro j
    apply A.ae_mdifferentiableAt_of_lipschitzWith I (fun x ↦ G x j)
    simpa only [Function.comp_apply, one_mul] using
      ((LipschitzWith.eval j).comp hG)
  have hchain : planarQ =ᵐ[volume.restrict s]
      fun z ↦ d z * q (F z) := by
    filter_upwards [ae_restrict_mem hs, hGdiff] with z hz hGz
    have hzDomain : z ∈ A.domain i := hsDomain hz
    have hFdiff : MDifferentiableAt 𝓘(ℝ, ℂ) I F z := by
      exact ((A.contMDiffOn_parametrization i z hzDomain).contMDiffAt
        ((A.isOpen_domain i).mem_nhds hzDomain)).mdifferentiableAt
          one_ne_zero
    simpa only [planarQ, d, q, F, s] using
      ofReal_abs_finiteSymplecticFDerivDensity_comp_parametrization_eq_chartDensity_mul
        I o G F z hFdiff hGz
  have hproduct : AEMeasurable (fun z ↦ d z * q (F z))
      (volume.restrict s) :=
    hplanarQ.aemeasurable.restrict.congr hchain
  have hdNNcoe : (fun z ↦ (dNN z : ℝ≥0∞)) = d := by
    funext z
    exact ENNReal.coe_toNNReal (by
      simp [d, F, riemannianChartDensity])
  have hqFweighted : AEMeasurable (fun z ↦ q (F z))
      ((volume.restrict s).withDensity d) := by
    rw [← hdNNcoe]
    apply (aemeasurable_withDensity_ennreal_iff' hdNN).2
    have hdNNcoe_apply : ∀ z, (dNN z : ℝ≥0∞) = d z :=
      congrFun hdNNcoe
    simpa only [hdNNcoe_apply] using hproduct
  let ν : Measure ℂ := (volume.restrict s).withDensity d
  have hFweighted : AEMeasurable F ν := by
    exact hFbase.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict s) d)
  have hνmem : ∀ᵐ z ∂ν, z ∈ s := by
    exact (Measure.ae_le_iff_absolutelyContinuous.mpr
      (withDensity_absolutelyContinuous (volume.restrict s) d))
        (ae_restrict_mem hs)
  have hνrestrict : ν.restrict s = ν :=
    Measure.restrict_eq_self_of_ae_mem hνmem
  let μs : Measure s := Measure.comap ((↑) : s → ℂ) ν
  have hcoeMap : μs.map ((↑) : s → ℂ) = ν := by
    rw [show μs = Measure.comap ((↑) : s → ℂ) ν by rfl,
      map_comap_subtype_coe hs, hνrestrict]
  have hqSubtype : AEMeasurable (q ∘ s.restrict F) μs := by
    have hqRestrict : AEMeasurable (fun z ↦ q (F z)) (ν.restrict s) := by
      rw [hνrestrict]
      simpa only [ν] using hqFweighted
    have hqComap :=
      (aemeasurable_restrict_iff_comap_subtype hs).1 hqRestrict
    simpa only [μs, Function.comp_apply, Set.restrict_apply] using hqComap
  have hqMappedSubtype : AEMeasurable q (μs.map (s.restrict F)) :=
    hFembed.aemeasurable_map_iff.2 hqSubtype
  have hFafterCoe : AEMeasurable F
      (μs.map ((↑) : s → ℂ)) := by
    rw [hcoeMap]
    exact hFweighted
  have hmap : μs.map (s.restrict F) = ν.map F := by
    change μs.map (F ∘ ((↑) : s → ℂ)) = ν.map F
    rw [← hFafterCoe.map_map_of_aemeasurable
      measurable_subtype_coe.aemeasurable]
    exact congrArg (Measure.map F) hcoeMap
  simpa only [riemannianChartAreaMeasure, q, F, s, ν, hmap] using
    hqMappedSubtype

end ControlledInteriorAtlas

/-- The absolute intrinsic finite symplectic density of a globally Lipschitz
finite complex map is almost everywhere measurable for canonical Riemannian
surface area. -/
theorem aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M) (G : M → ι → ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G) :
    AEMeasurable
      (fun x ↦ ENNReal.ofReal
        |orientedFiniteComplexRiemannianSymplecticDensity I o G x|)
      (riemannianSurfaceAreaMeasure I) := by
  let A : ControlledInteriorAtlas I M :=
    Classical.choice (inferInstance : Nonempty (ControlledInteriorAtlas I M))
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  change AEMeasurable _ (Measure.sum fun i ↦
    riemannianChartAreaMeasure I (A.parametrization i) (A.piece I i))
  exact AEMeasurable.sum_measure fun i ↦
    A.aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity_of_lipschitzWith
      I o G hG i

/-- Real-valued form of canonical measurability for the absolute intrinsic
finite symplectic density. -/
theorem aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity_real
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M) (G : M → ι → ℂ)
    {KG : ℝ≥0} (hG : LipschitzWith KG G) :
    AEMeasurable
      (fun x ↦ |orientedFiniteComplexRiemannianSymplecticDensity I o G x|)
      (riemannianSurfaceAreaMeasure I) := by
  have h :=
    (aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity
      I o G hG).ennreal_toReal
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h

#print axioms measurable_finiteSymplecticFDerivDensity
#print axioms
  ControlledInteriorAtlas.aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity_of_lipschitzWith
#print axioms
  aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity
#print axioms
  aemeasurable_abs_orientedFiniteComplexRiemannianSymplecticDensity_real

end

end GromovFilling
