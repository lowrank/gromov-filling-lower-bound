import GromovFilling.FiniteResonantUniformBound
import GromovFilling.IntegratedComassLimit
import GromovFilling.RiemannianProfileFourierAE

/-!
# Almost-everywhere finite resonant estimates on Riemannian surface area

The pointwise finite resonant comass theorems require differentiability of
the odd distance profile and all of its odd Fourier modes.  Those hypotheses
hold at planar-volume almost every point of every controlled chart piece.
This file transports the full (not necessarily measurable) regularity
predicate through the injective chart parametrizations to canonical
Riemannian surface area.

The resulting surface-area statements provide both ingredients required by
dominated convergence: a truncation-independent envelope and pointwise
vanishing of the positive excess above the sharp limiting comass.
-/

open Bundle Filter Manifold MeasureTheory Set
open scoped Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

/-- An arbitrary almost-everywhere predicate may be transported from a
measurable planar set to its Jacobian-weighted chart-area measure when the
chart is continuous and injective there.  Passing through the subtype makes
the chart a measurable embedding, so the predicate itself need not be
measurable. -/
theorem ae_riemannianChartAreaMeasure_of_ae_comp_of_continuousOn_injOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (hs : MeasurableSet s)
    (hFcont : ContinuousOn F s) (hFinj : Set.InjOn F s)
    {p : M → Prop}
    (hsource : ∀ᵐ z ∂volume.restrict s, p (F z)) :
    ∀ᵐ x ∂riemannianChartAreaMeasure I F s, p x := by
  let d : ℂ → ℝ≥0∞ := riemannianChartDensity I F
  let ν : Measure ℂ := (volume.restrict s).withDensity d
  have hνac : ν ≪ volume.restrict s := by
    exact withDensity_absolutelyContinuous _ _
  have hFbase : AEMeasurable F (volume.restrict s) :=
    hFcont.aemeasurable hs
  have hFν : AEMeasurable F ν := hFbase.mono_ac hνac
  have hsourceν : ∀ᵐ z ∂ν, p (F z) :=
    (Measure.ae_le_iff_absolutelyContinuous.mpr hνac) hsource
  have hνmem : ∀ᵐ z ∂ν, z ∈ s := by
    exact (Measure.ae_le_iff_absolutelyContinuous.mpr hνac)
      (ae_restrict_mem hs)
  have hνrestrict : ν.restrict s = ν :=
    Measure.restrict_eq_self_of_ae_mem hνmem
  let μs : Measure s := Measure.comap ((↑) : s → ℂ) ν
  have hcoeMap : μs.map ((↑) : s → ℂ) = ν := by
    rw [show μs = Measure.comap ((↑) : s → ℂ) ν by rfl,
      map_comap_subtype_coe hs, hνrestrict]
  have hsourceSubtype : ∀ᵐ z : s ∂μs, p (F z) := by
    apply ((MeasurableEmbedding.subtype_coe hs).ae_map_iff
      (μ := μs) (p := fun z : ℂ ↦ p (F z))).mp
    rw [hcoeMap]
    simpa only [Function.comp_apply] using hsourceν
  have hFembed : MeasurableEmbedding (s.restrict F) :=
    hFcont.measurableEmbedding hs hFinj
  have htargetSubtype : ∀ᵐ x ∂μs.map (s.restrict F), p x :=
    hFembed.ae_map_iff.2 hsourceSubtype
  have hFafterCoe : AEMeasurable F
      (μs.map ((↑) : s → ℂ)) := by
    rw [hcoeMap]
    exact hFν
  have hmap : μs.map (s.restrict F) = ν.map F := by
    change μs.map (F ∘ ((↑) : s → ℂ)) = ν.map F
    rw [← hFafterCoe.map_map_of_aemeasurable
      measurable_subtype_coe.aemeasurable]
    exact congrArg (Measure.map F) hcoeMap
  change ∀ᵐ x ∂ν.map F, p x
  rw [← hmap]
  exact htargetSubtype

/-- The simultaneous pointwise regularity needed by the coherent finite
resonant comass limit. -/
def FiniteResonantRegularPoint
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (boundary : UnitAddCircle → M) (x : M) : Prop :=
  I.IsInteriorPoint x ∧
    (∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) ∧
    ∀ k : ℕ,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x

/-- Simultaneous finite-resonant regularity holds at almost every planar
point of each disjoint controlled chart piece. -/
theorem ControlledInteriorAtlas.ae_finiteResonantRegularPoint
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M)
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (A.piece I i),
      FiniteResonantRegularPoint I boundary (A.parametrization i z) := by
  have hprofile :=
    A.ae_ae_mdifferentiableAt_oddDistanceProfile I hboundary i
  have hFourier : ∀ᵐ z ∂volume.restrict (A.piece I i),
      ∀ k : ℕ,
        MDifferentiableAt I 𝓘(ℝ, ℂ)
          (oddProfileFourierMap boundary (oddMode k))
          (A.parametrization i z) := by
    rw [ae_all_iff]
    intro k
    exact A.ae_mdifferentiableAt_of_lipschitzWith I
      (oddProfileFourierMap boundary (oddMode k))
      (oddProfileFourierMap_lipschitzWith hboundary (oddMode k)) i
  filter_upwards [ae_restrict_mem (A.measurableSet_piece I i),
    hprofile, hFourier] with z hz hprofilez hFourierz
  refine ⟨?_, hprofilez, hFourierz⟩
  exact A.image_subset_interior i
    ⟨z, A.piece_subset_domain I i hz, rfl⟩

/-- Simultaneous finite-resonant regularity transported to one weighted
Riemannian chart-area contribution. -/
theorem ControlledInteriorAtlas.ae_finiteResonantRegularPoint_chartArea
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M)
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary) (i : ℕ) :
    ∀ᵐ x ∂riemannianChartAreaMeasure I
        (A.parametrization i) (A.piece I i),
      FiniteResonantRegularPoint I boundary x := by
  exact ae_riemannianChartAreaMeasure_of_ae_comp_of_continuousOn_injOn
    I (A.parametrization i) (A.piece I i)
      (A.measurableSet_piece I i)
      ((A.continuousOn_parametrization i).mono
        (A.piece_subset_domain I i))
      ((A.injOn_parametrization i).mono
        (A.piece_subset_domain I i))
      (A.ae_finiteResonantRegularPoint I hboundary i)

/-- Simultaneous finite-resonant regularity holds almost everywhere for the
canonical Riemannian surface-area measure. -/
theorem ae_finiteResonantRegularPoint_surfaceArea
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary) :
    ∀ᵐ x ∂riemannianSurfaceAreaMeasure I,
      FiniteResonantRegularPoint I boundary x := by
  let A : ControlledInteriorAtlas I M :=
    Classical.choice (inferInstance : Nonempty (ControlledInteriorAtlas I M))
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  unfold ControlledInteriorAtlas.areaMeasure riemannianAtlasAreaMeasure
  exact Measure.ae_sum_iff.2 fun i ↦
    A.ae_finiteResonantRegularPoint_chartArea I hboundary i

/-- Every oriented finite resonant density obeys one truncation-independent
envelope at canonical surface-area almost every point. -/
theorem ae_abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (o : RiemannianTangentPlaneOrientation I M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    ∀ᵐ x ∂riemannianSurfaceAreaMeasure I, ∀ N : ℕ,
      |orientedFiniteResonantRiemannianSymplecticDensity
          I o boundary N lam x| ≤ finiteResonantUniformDensityBound lam := by
  filter_upwards [ae_finiteResonantRegularPoint_surfaceArea I hboundary]
    with x hx
  intro N
  exact abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
    I hboundary o lam hlam0 hlam x hx.1 hx.2.1 hx.2.2 N

/-- The positive excess of the finite oriented resonant densities above the
sharp limiting comass tends to zero at canonical surface-area almost every
point. -/
theorem ae_tendsto_comassPositiveExcess_orientedFiniteResonant_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (o : RiemannianTangentPlaneOrientation I M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    ∀ᵐ x ∂riemannianSurfaceAreaMeasure I,
      Tendsto
        (fun N ↦ comassPositiveExcess (comassBound lam)
          (orientedFiniteResonantRiemannianSymplecticDensity
            I o boundary N lam x))
        atTop (nhds 0) := by
  filter_upwards [ae_finiteResonantRegularPoint_surfaceArea I hboundary]
    with x hx
  obtain ⟨error, herror, hbound⟩ :=
    exists_orientedFiniteResonantRiemannian_comass_error
      I hboundary o lam hlam0 hlam x hx.1 hx.2.1 hx.2.2
  exact tendsto_comassPositiveExcess_zero_of_abs_le_add_error
    herror hbound

end

end GromovFilling

#print axioms
  GromovFilling.ae_riemannianChartAreaMeasure_of_ae_comp_of_continuousOn_injOn
#print axioms GromovFilling.FiniteResonantRegularPoint
#print axioms
  GromovFilling.ae_finiteResonantRegularPoint_surfaceArea
#print axioms
  GromovFilling.ae_abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
#print axioms
  GromovFilling.ae_tendsto_comassPositiveExcess_orientedFiniteResonant_zero
