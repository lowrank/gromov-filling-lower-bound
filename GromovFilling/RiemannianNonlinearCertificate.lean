import GromovFilling.Certificates
import GromovFilling.RiemannianControlledBoundaryResonantAction
import GromovFilling.RiemannianFiniteResonantAE

/-!
# The nonlinear certificate from an oriented Riemannian boundary atlas

This file assembles the analytic end of the oriented argument.  Finite
controlled-atlas Stokes identifies every finite resonant surface integral
with its explicit boundary action.  The almost-everywhere finite-resonant
estimates provide a truncation-independent envelope and vanishing positive
comass excess.  Dominated convergence then yields the sharp limiting comass
inequality and hence the nonlinear certificate.

The theorem is deliberately parameterized by the oriented atlas and its
boundary-phase compatibility.  Constructing those data from a conventional
orientation of an arbitrary filling is a separate geometric obligation; no
Stokes or comass conclusion is stored in either datum.
-/

open Bundle Filter Manifold MeasureTheory Set
open scoped Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance nonlinearCertificateEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- The complete finite-to-infinite nonlinear area certificate once an
oriented controlled boundary atlas and its compatible angular phases have
been supplied. -/
theorem ControlledBoundaryAtlasBoundaryPhase.nonlinearCertificate_le_surfaceArea
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
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
    ENNReal.ofReal (nonlinearCertificate lam) ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  let I := modelWithCornersEuclideanHalfSpace 2
  letI : Nonempty (ControlledInteriorAtlas I M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition
      P (Classical.choice inferInstance)
  let μ : Measure M := riemannianSurfaceAreaMeasure I
  change ENNReal.ofReal (nonlinearCertificate lam) ≤ μ Set.univ
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
    let C : ℝ := comassBound lam
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
        ae_tendsto_comassPositiveExcess_orientedFiniteResonant_zero
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
        nonlinearCertificate lam ≤ (μ Set.univ).toReal := by
      exact oriented_area_ge_nonlinearCertificate hlam0 hlam hcalibration
    exact ENNReal.ofReal_le_of_le_toReal hreal

/-- The exact strict decimal endpoint of the nonlinear certificate once the
oriented controlled atlas and its compatible boundary phases are supplied. -/
theorem ControlledBoundaryAtlasBoundaryPhase.surfaceArea_gt_point_zero_three
    {M : Type uM} [PseudoMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
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
    (hboundary : IsometricCircleBoundary boundary) :
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) M) :=
      nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
        (Classical.choice inferInstance)
    ENNReal.ofReal (538982446 / 100000000 : ℝ) <
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set M) := by
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) M) :=
    nonempty_controlledInteriorAtlas_of_finiteControlledBoundaryChartPartition P
      (Classical.choice inferInstance)
  have hcertificate :=
    B.nonlinearCertificate_le_surfaceArea hboundary (3 / 100)
      (by norm_num) lambda_point_zero_three_admissible
  have hcertificatePos : 0 < nonlinearCertificate (3 / 100) :=
    (by norm_num : (0 : ℝ) < 538982446 / 100000000).trans
      nonlinearCertificate_point_zero_three_gt
  have hnumeric :
      ENNReal.ofReal (538982446 / 100000000 : ℝ) <
        ENNReal.ofReal (nonlinearCertificate (3 / 100)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff hcertificatePos]
    exact nonlinearCertificate_point_zero_three_gt
  exact hnumeric.trans_le hcertificate

end

end GromovFilling

#print axioms
  GromovFilling.ControlledBoundaryAtlasBoundaryPhase.nonlinearCertificate_le_surfaceArea
#print axioms
  GromovFilling.ControlledBoundaryAtlasBoundaryPhase.surfaceArea_gt_point_zero_three
