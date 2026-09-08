import GromovFilling.RiemannianConventionalNonlinearImprovement
import GromovFilling.SharpenedComass
import GromovFilling.SharpenedNumerics
import GromovFilling.SharpenedProfileTail

/-!
# The revised nonlinear bound for oriented Riemannian fillings

The improved Fourier estimate passes through the existing finite Stokes and
surface-area construction. The final statements retain exactly the geometric
interface of the earlier bound; the new tail and cancellation estimates are
derived internally.
-/

open Bundle Filter Manifold MeasureTheory Set
open scoped Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance sharpenedNonlinearEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩

/-- At every regular interior tangent plane, the intrinsic oriented finite
resonant densities satisfy the sharp infinite comass bound up to one scalar
error sequence tending to zero.  The auxiliary coherent Fourier field and
orthonormal frame have both been eliminated from the statement. -/
theorem exists_orientedFiniteResonantRiemannian_sharpened_comass_error
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (o : RiemannianTangentPlaneOrientation I M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (x : M) (hx : I.IsInteriorPoint x)
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : ℕ,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
      ∀ N : ℕ,
        |orientedFiniteResonantRiemannianSymplecticDensity
            I o boundary N lam x| ≤
          sharpenedComassBound lam + |error N| := by
  let e := o.positiveOrthonormalBasis I x
  obtain ⟨f, hf, hanti, hunit, heq, herror, _hbound⟩ :=
    exists_coherentProfile_finiteResonantRiemannian_comass_limit
      I hboundary lam hlam0 hlam x hx e hprofileDiff hFourierDiff
  let error : ℕ → ℝ :=
    finiteTruncationResonantBaseFirstError lam
      (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n)
  refine ⟨error, ?_, ?_⟩
  · simpa only [error] using herror
  · intro N
    rw [abs_orientedFiniteResonantRiemannianSymplecticDensity_eq_frame
      I o boundary N lam x e]
    rw [heq N]
    have hprofile25 :=
      oddProfileFourierMap_first_add_twenty_five_infiniteTailEnergy_le_two hboundary x
    have hnew :=
      abs_finiteTruncationResonantDensity_fourierCoeffOn_le_sharpenedComassBound_add_error
        lam (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
        f N hlam0 hlam (summable_normSq_oddProfileFourierMap_tail hboundary x)
        hf hanti hunit
        (oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two hboundary x)
        (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hprofile25)
        (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)
    simpa only [error] using hnew
/-- The positive excess of the finite oriented resonant densities above the
sharp limiting comass tends to zero at canonical surface-area almost every
point. -/
theorem ae_tendsto_sharpenedComassPositiveExcess_orientedFiniteResonant_zero
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
        (fun N ↦ comassPositiveExcess (sharpenedComassBound lam)
          (orientedFiniteResonantRiemannianSymplecticDensity
            I o boundary N lam x))
        atTop (nhds 0) := by
  filter_upwards [ae_finiteResonantRegularPoint_surfaceArea I hboundary]
    with x hx
  obtain ⟨error, herror, hbound⟩ :=
    exists_orientedFiniteResonantRiemannian_sharpened_comass_error
      I hboundary o lam hlam0 hlam x hx.1 hx.2.1 hx.2.2
  exact tendsto_comassPositiveExcess_zero_of_abs_le_add_error
    herror hbound
/-- The complete finite-to-infinite nonlinear area certificate once an
oriented controlled boundary atlas and its compatible angular phases have
been supplied. -/
theorem ControlledBoundaryAtlasBoundaryPhase.sharpenedNonlinearCertificate_le_surfaceArea
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    {P : FiniteControlledBoundaryChartPartition M}
    {O : ControlledBoundaryAtlasOrientation P}
    {boundary : UnitAddCircle → M}
    (B : ControlledBoundaryAtlasBoundaryPhase P O boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
        (Classical.choice inferInstance)
    ENNReal.ofReal (sharpenedNonlinearCertificate lam) ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  let I := modelWithCornersEuclideanHalfSpace 2
  letI : Nonempty (ControlledInteriorAtlas I M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition
      P (Classical.choice inferInstance)
  let μ : Measure M := riemannianSurfaceAreaMeasure I
  change ENNReal.ofReal (sharpenedNonlinearCertificate lam) ≤ μ Set.univ
  by_cases hμtop : μ Set.univ = ∞
  · rw [hμtop]
    exact le_top
  · letI : IsFiniteMeasure μ :=
      ⟨lt_top_iff_ne_top.2 hμtop⟩
    let F : ℕ → M → ℝ := fun N x ↦
      orientedFiniteResonantRiemannianSymplecticDensity
        I O.tangentOrientation boundary N lam x
    let b : ℕ → ℝ := fun N ↦
      finiteResonantSymplecticBoundaryAction N lam
    let C : ℝ := sharpenedComassBound lam
    let K : ℝ := finiteResonantUniformDensityBound lam + |C|
    have hb : Tendsto b atTop (nhds (boundaryAction lam)) := by
      simpa only [b,
        finiteResonantSymplecticBoundaryAction_eq_fourierGreenArea,
        boundaryActionSeries_eq] using
        tendsto_fourierGreenArea_resonantBoundaryCoefficient lam
    have hFsigned (N : ℕ) : Integrable (F N) μ := by
      obtain ⟨CG, hG⟩ :=
        exists_lipschitzWith_finiteResonantProfileMap hboundary N lam
      have h :=
        (sum_integral_controlledBoundaryChartAreaSymplecticDensity_eq_surface
          P O (finiteResonantProfileMap boundary N lam) hG).1
      simpa only [F, μ, I,
        orientedFiniteResonantRiemannianSymplecticDensity] using h
    have hFint (N : ℕ) : Integrable (fun x ↦ |F N x|) μ := by
      simpa only [Real.norm_eq_abs] using (hFsigned N).norm
    have hfinite (N : ℕ) : b N ≤ ∫ x, |F N x| ∂μ := by
      have hstokes :=
        B.integral_orientedFiniteResonantRiemannianSymplecticDensity_eq_boundaryAction
          hboundary N lam
      change (∫ x, F N x ∂μ) = b N at hstokes
      rw [← hstokes]
      exact (le_abs_self _).trans abs_integral_le_integral_abs
    have hmeas (N : ℕ) :
        AEStronglyMeasurable
          (fun x ↦ comassPositiveExcess C (F N x)) μ := by
      have hcontinuous : Continuous (fun r : ℝ ↦ max (r - C) 0) := by
        fun_prop
      simpa only [comassPositiveExcess] using
        hcontinuous.comp_aestronglyMeasurable
          (hFint N).aestronglyMeasurable
    have hK : Integrable (fun _x : M ↦ K) μ := by
      exact integrable_const_iff.2 (Or.inr inferInstance)
    have hbound (N : ℕ) : ∀ᵐ x ∂μ,
        ‖comassPositiveExcess C (F N x)‖ ≤ K := by
      filter_upwards
          [ae_abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
            I hboundary O.tangentOrientation lam hlam0 hlam]
          with x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (comassPositiveExcess_nonneg C (F N x))]
      unfold comassPositiveExcess K
      apply max_le
      · have hN := hx N
        linarith [neg_le_abs C]
      · exact add_nonneg
          (finiteResonantUniformDensityBound_nonneg lam) (abs_nonneg C)
    have hlim : ∀ᵐ x ∂μ,
        Tendsto (fun N ↦ comassPositiveExcess C (F N x))
          atTop (nhds 0) := by
      simpa only [F, C, μ, I] using
        ae_tendsto_sharpenedComassPositiveExcess_orientedFiniteResonant_zero
          I hboundary O.tangentOrientation lam hlam0 hlam
    have hC : Integrable (fun _x : M ↦ C) μ := by
      exact integrable_const_iff.2 (Or.inr inferInstance)
    have harea : (∫ _x : M, C ∂μ) ≤ C * (μ Set.univ).toReal := by
      rw [integral_const, measureReal_def, smul_eq_mul]
      exact le_of_eq (mul_comm _ _)
    have hcalibration :
        boundaryAction lam ≤ C * (μ Set.univ).toReal :=
      calibration_le_comass_mul_area_of_dominated_positiveExcess
        μ hb hfinite hFint hmeas hK hbound hlim hC harea
    have hreal :
        sharpenedNonlinearCertificate lam ≤ (μ Set.univ).toReal := by
      exact area_ge_sharpenedNonlinearCertificate hlam hcalibration
    exact ENNReal.ofReal_le_of_le_toReal hreal

/-- The all-parameter nonlinear master formula for a compact connected
controlled oriented Riemannian isometric filling. -/
theorem riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_controlled_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (R : ControlledRiemannianSurfaceOrientation M)
    (H : ControlledRiemannianInducedBoundaryOrientation R boundary)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    letI : Nonempty M := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (sharpenedNonlinearCertificate lam) ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  letI : Nonempty M := ⟨boundary 0⟩
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M) :=
    nonempty_controlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  let P : FiniteControlledBoundaryChartPartition M :=
    Classical.choice (nonempty_finiteControlledBoundaryChartPartition M)
  let B : ControlledBoundaryAtlasBoundaryPhase P
      (R.toBoundaryAtlasOrientation P) boundary :=
    Classical.choice
      (nonempty_controlledBoundaryAtlasBoundaryPhase_of_inducedBoundaryOrientation
        boundary hboundary hboundaryRange P R H)
  simpa only using
    B.sharpenedNonlinearCertificate_le_surfaceArea hboundary lam hlam0 hlam
/-- The all-parameter nonlinear master formula for every compact connected
conventionally oriented Riemannian isometric filling. -/
theorem riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32) :
    letI : Nonempty M := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (sharpenedNonlinearCertificate lam) ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  rcases O.controlledInducedBoundaryOrientation_or_reverse
      boundary hboundary hboundaryRange with H | H
  · exact riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_controlled_oriented_isometric_filling
      boundary hboundary hboundaryRange O.toControlledRiemannianSurfaceOrientation
      H lam hlam0 hlam
  · have hreverseRange : Set.range (reverseCircleBoundary boundary) =
        (modelWithCornersEuclideanHalfSpace 2).boundary M :=
      (range_reverseCircleBoundary boundary).trans hboundaryRange
    simpa only [reverseCircleBoundary_apply, neg_zero] using
      (riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_controlled_oriented_isometric_filling
        (reverseCircleBoundary boundary) hboundary.reverse hreverseRange
        O.toControlledRiemannianSurfaceOrientation H lam hlam0 hlam)
/-- The strict decimal nonlinear improvement for every compact connected
conventionally oriented Riemannian isometric filling. -/
theorem riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace
        (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M) :
    letI : Nonempty M := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (540154 / 100000 : ℝ) <
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  letI : Nonempty M := ⟨boundary 0⟩
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M) :=
    nonempty_controlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  have hcertificate :=
    riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling
      boundary hboundary hboundaryRange O (1 / 25) (by norm_num)
      lambda_one_div_twenty_five_admissible
  have hlower : (540154 / 100000 : ℝ) < sharpenedNonlinearCertificate (1 / 25) :=
    (by norm_num : (540154 / 100000 : ℝ) < 5401544 / 1000000).trans
      sharpenedNonlinearCertificate_one_div_twenty_five_gt
  have hpositive : 0 < sharpenedNonlinearCertificate (1 / 25) :=
    (by norm_num : (0 : ℝ) < 540154 / 100000).trans hlower
  exact (ENNReal.ofReal_lt_ofReal_iff hpositive).2 hlower |>.trans_le hcertificate

end

end GromovFilling

#print axioms GromovFilling.riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling
#print axioms GromovFilling.riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling
