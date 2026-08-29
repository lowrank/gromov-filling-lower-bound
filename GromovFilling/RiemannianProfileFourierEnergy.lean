import GromovFilling.RiemannianJacobianBudget
import GromovFilling.RiemannianLipschitzDerivative
import GromovFilling.ProfileFourier

/-!
# Intrinsic Fourier energy of distance profiles

This file proves the pointwise Fourier-energy estimate needed for the
universal Fourier bound on a Riemannian filling surface.  At an interior
point where the angular distance profiles and the selected Fourier maps
are differentiable, every finite family of positive odd modes has total
intrinsic derivative energy at most two and total intrinsic two-Jacobian
at most one.

The proof constructs measurable angular derivative fields along clipped
Riemannian tangent-chart lines, differentiates the Fourier integrals, and
combines the sharp covector norm bound with finite Bessel inequality.
-/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- Joint continuity of the angular odd-distance profile on an arbitrary
pseudometric target. -/
theorem IsometricCircleBoundary.continuous_oddDistanceProfile_uncurry_general
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) :
    Continuous (Function.uncurry (fun t : ℝ ↦ fun x : X ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x)) := by
  have hb : Continuous boundary := hboundary.lipschitzWith.continuous
  unfold Function.uncurry oddDistanceProfile boundaryDistance
  have hangle : Continuous (fun p : ℝ × X ↦ angleToUnitAddCircle p.1) :=
    continuous_angleToUnitAddCircle.comp continuous_fst
  have hfirst : Continuous (fun p : ℝ × X ↦
      dist p.2 (boundary (angleToUnitAddCircle p.1))) :=
    continuous_snd.dist (hb.comp hangle)
  have hsecond : Continuous (fun p : ℝ × X ↦
      dist p.2 (boundary
        (angleToUnitAddCircle p.1 +
          ((1 / 2 : ℝ) : UnitAddCircle)))) :=
    continuous_snd.dist
      (hb.comp (hangle.add continuous_const))
  exact (hfirst.sub hsecond).div_const 2

theorem exists_tangentProfileDerivativeField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x)
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) :
    ∃ d : ℝ → ℝ,
      Measurable d ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
        d t = (NormedSpace.fromTangentSpace
          (oddDistanceProfile boundary (angleToUnitAddCircle t) x))
            (mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x v)) ∧
      (∀ (w : ℝ → ℝ), Continuous w → (∀ t, |w t| ≤ 1) →
        HasFDerivAt (fun s : ℝ ↦ ∫ t in (-Real.pi)..Real.pi,
          oddDistanceProfile boundary (angleToUnitAddCircle t)
            (riemannianTangentChartLine I x v s) * w t)
          (ContinuousLinearMap.toSpanSingleton ℝ
            (∫ t in (-Real.pi)..Real.pi, d t * w t)) 0) ∧
      Function.Antiperiodic d Real.pi := by
  obtain ⟨ε, hε, hγLip⟩ :=
    exists_lipschitzOnWith_riemannianTangentChartLine I x hx v
      (show (1 : ℝ) < 2 by norm_num)
  have hbounds : -ε / 2 ≤ ε / 2 := by linarith
  let clip : ℝ → ℝ := fun s ↦
    (Set.projIcc (-ε / 2) (ε / 2) hbounds s : ℝ)
  let γ : ℝ → M := riemannianTangentChartLine I x v
  let γc : ℝ → M := γ ∘ clip
  have hclipCont : Continuous clip := by
    exact continuous_subtype_val.comp continuous_projIcc
  have hclipBall : Set.MapsTo clip Set.univ (Metric.ball 0 ε) := by
    intro s _hs
    have hs := (Set.projIcc (-ε / 2) (ε / 2) hbounds s).property
    change dist (clip s) 0 < ε
    rw [Real.dist_eq]
    dsimp only [clip]
    have hlo : -ε / 2 ≤
        (Set.projIcc (-ε / 2) (ε / 2) hbounds s : ℝ) := hs.1
    have hhi :
        (Set.projIcc (-ε / 2) (ε / 2) hbounds s : ℝ) ≤ ε / 2 := hs.2
    rw [sub_zero]
    exact (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hγcCont : Continuous γc := by
    rw [← continuousOn_univ]
    exact hγLip.continuousOn.comp hclipCont.continuousOn hclipBall
  let P : ℝ → ℝ → ℝ := fun t s ↦
    oddDistanceProfile boundary (angleToUnitAddCircle t) (γc s)
  have hP : Continuous P.uncurry := by
    exact hboundary.continuous_oddDistanceProfile_uncurry_general.comp
      (continuous_fst.prodMk (hγcCont.comp continuous_snd))
  let d : ℝ → ℝ := fun t ↦ fderiv ℝ (P t) 0 1
  have hdmeas : Measurable d := by
    exact (measurable_fderiv_apply_const_with_param ℝ hP 1).comp
      (measurable_id.prodMk measurable_const)
  refine ⟨d, hdmeas, ?_, ?_, ?_⟩
  · filter_upwards [hdiff] with t htdiff
    have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := by
      exact mdifferentiableAt_riemannianTangentChartLine_zero I x hx v
    have htdiff' : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) (γ 0) := by
      simpa only [γ, riemannianTangentChartLine_zero] using htdiff
    have hcomp := mfderiv_comp 0 htdiff' hγdiff
    rw [show γ = riemannianTangentChartLine I x v from rfl,
      mfderiv_riemannianTangentChartLine_zero I x hx v,
      riemannianTangentChartLine_zero] at hcomp
    have hclipLocal : clip =ᶠ[𝓝 0] id := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < ε / 2)] with s hs
      have hs' : s ∈ Set.Icc (-ε / 2) (ε / 2) := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hs
        constructor <;> linarith [hs.1, hs.2]
      change (Set.projIcc (-ε / 2) (ε / 2) hbounds s : ℝ) = id s
      rw [Set.projIcc_of_mem hbounds hs']
      rfl
    have hprofileLocal : P t =ᶠ[𝓝 0]
        (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) := by
      filter_upwards [hclipLocal] with s hs
      simp only [P, γc, Function.comp_apply, hs, id_eq]
    have hfd : fderiv ℝ (P t) 0 =
        fderiv ℝ
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) 0 :=
      hprofileLocal.fderiv_eq
    dsimp only [d]
    rw [hfd]
    have hcomp' : fderiv ℝ
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) 0 =
        (mfderiv I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) x) ∘L
            ContinuousLinearMap.toSpanSingleton ℝ v := by
      simpa only [mfderiv_eq_fderiv, γ,
        riemannianTangentChartLine_zero] using hcomp
    rw [hcomp']
    change (mfderiv I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
          (ContinuousLinearMap.toSpanSingleton ℝ v 1) = _
    rw [ContinuousLinearMap.toSpanSingleton_apply_one]
    rfl
  · intro w hw hwabs
    let F : ℝ → ℝ → ℝ := fun s t ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) (γ s) * w t
    let F' : ℝ → ℝ →L[ℝ] ℝ := fun t ↦
      ContinuousLinearMap.toSpanSingleton ℝ (d t * w t)
    have hFmeas : ∀ᶠ s in 𝓝 (0 : ℝ),
        AEStronglyMeasurable (F s)
          (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
      filter_upwards [] with s
      exact ((hboundary.continuous_oddDistanceProfile_parameter (γ s)).mul hw)
        |>.aestronglyMeasurable.restrict
    have hFint : IntervalIntegrable (F 0) volume
        (-Real.pi) Real.pi := by
      apply Continuous.intervalIntegrable
      exact (hboundary.continuous_oddDistanceProfile_parameter (γ 0)).mul hw
    have hF'meas : AEStronglyMeasurable F'
        (volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
      exact (((ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := ℝ)).continuous.measurable).comp
        (hdmeas.mul hw.measurable)).aestronglyMeasurable.restrict
    have hlip : ∀ᵐ t : ℝ ∂volume.restrict
        (Set.uIoc (-Real.pi) Real.pi),
        LipschitzOnWith (Real.nnabs ((2 * ‖v‖) : ℝ)) (F · t)
          (Metric.ball 0 ε) := by
      apply ae_of_all
      intro t
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      change dist
        (oddDistanceProfile boundary (angleToUnitAddCircle t) (γ a) * w t)
        (oddDistanceProfile boundary (angleToUnitAddCircle t) (γ b) * w t) ≤
          (Real.nnabs (2 * ‖v‖) : ℝ) * dist a b
      rw [Real.dist_eq]
      rw [← sub_mul, abs_mul]
      have hp := (oddDistanceProfile_lipschitzWith boundary
        (angleToUnitAddCircle t)).dist_le_mul (γ a) (γ b)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hp
      have hγ := hγLip.dist_le_mul a ha b hb
      have hcoe : (Real.toNNReal (2 * ‖v‖) : ℝ) = 2 * ‖v‖ := by
        rw [Real.coe_toNNReal]
        positivity
      rw [Real.nnabs_of_nonneg (by positivity), hcoe]
      calc
        |oddDistanceProfile boundary (angleToUnitAddCircle t) (γ a) -
            oddDistanceProfile boundary (angleToUnitAddCircle t) (γ b)| * |w t| ≤
            dist (γ a) (γ b) * 1 :=
          mul_le_mul hp (hwabs t) (abs_nonneg _) (dist_nonneg)
        _ ≤ (2 * ‖v‖) * dist a b := by
          simpa [hcoe] using hγ
    have hbound : IntervalIntegrable (fun _ : ℝ ↦ 2 * ‖v‖) volume
        (-Real.pi) Real.pi := by
      exact (continuous_const : Continuous (fun _ : ℝ ↦ 2 * ‖v‖))
        |>.intervalIntegrable _ _
    have hdiff' : ∀ᵐ t : ℝ ∂volume.restrict
        (Set.uIoc (-Real.pi) Real.pi),
        HasFDerivAt (F · t) (F' t) 0 := by
      have hdiffU : ∀ᵐ t : ℝ ∂volume.restrict
          (Set.uIoc (-Real.pi) Real.pi),
          MDifferentiableAt I 𝓘(ℝ, ℝ)
            (oddDistanceProfile boundary (angleToUnitAddCircle t)) x := by
        simpa [Set.uIoc_of_le (le_of_lt (by linarith [Real.pi_pos] : -Real.pi < Real.pi))]
          using hdiff
      filter_upwards [hdiffU] with t htdiff
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := by
        exact mdifferentiableAt_riemannianTangentChartLine_zero I x hx v
      have htdiff' : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) (γ 0) := by
        simpa only [γ, riemannianTangentChartLine_zero] using htdiff
      have hcompdiff : DifferentiableAt ℝ
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) 0 := by
        exact (htdiff'.comp 0 hγdiff).differentiableAt
      have hclipLocal : clip =ᶠ[𝓝 0] id := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < ε / 2)] with s hs
        have hs' : s ∈ Set.Icc (-ε / 2) (ε / 2) := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hs
          constructor <;> linarith [hs.1, hs.2]
        change (Set.projIcc (-ε / 2) (ε / 2) hbounds s : ℝ) = id s
        rw [Set.projIcc_of_mem hbounds hs']
        rfl
      have hprofileLocal : P t =ᶠ[𝓝 0]
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) := by
        filter_upwards [hclipLocal] with s hs
        change oddDistanceProfile boundary (angleToUnitAddCircle t) (γc s) =
          oddDistanceProfile boundary (angleToUnitAddCircle t) (γ s)
        congr 1
        simp only [γc, Function.comp_apply, hs, id_eq]
      have hdEq : d t = fderiv ℝ
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ) 0 1 := by
        dsimp only [d]
        rw [hprofileLocal.fderiv_eq]
      have hbase : HasFDerivAt
          (oddDistanceProfile boundary (angleToUnitAddCircle t) ∘ γ)
          (ContinuousLinearMap.toSpanSingleton ℝ (d t)) 0 := by
        have hfd := hcompdiff.hasFDerivAt
        apply hfd.congr_fderiv
        apply ContinuousLinearMap.ext
        intro s
        have hsrep : s = s • (1 : ℝ) := by simp
        rw [hsrep, map_smul, map_smul]
        simp only [ContinuousLinearMap.toSpanSingleton_apply_one, hdEq]
      have hmul := hbase.mul_const (w t)
      convert hmul using 1
      ext
      simp [F', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        mul_comm]
    obtain ⟨hF'int, hmain⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip_interval
      (x₀ := (0 : ℝ)) (s := Metric.ball 0 ε) (F := F) (F' := F')
      (bound := fun _ : ℝ ↦ 2 * ‖v‖) (Metric.ball_mem_nhds 0 hε)
      hFmeas hFint hF'meas hlip hbound hdiff'
    apply hmain.congr_fderiv
    apply ContinuousLinearMap.ext
    intro s
    rw [ContinuousLinearMap.intervalIntegral_apply hF'int s]
    simp only [F', ContinuousLinearMap.toSpanSingleton_apply]
    change (∫ t in (-Real.pi)..Real.pi, s * (d t * w t)) =
      s * ∫ t in (-Real.pi)..Real.pi, d t * w t
    rw [intervalIntegral.integral_const_mul]
  · intro t
    have hangle :
        angleToUnitAddCircle (t + Real.pi) =
          angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle) := by
      rw [angleToUnitAddCircle_add]
      congr 1
      unfold angleToUnitAddCircle
      rw [show Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) by
        field_simp [Real.pi_ne_zero]]
    have hP : P (t + Real.pi) = -P t := by
      funext s
      simp only [P, hangle, Pi.neg_apply]
      exact oddDistanceProfile_add_half boundary
        (angleToUnitAddCircle t) (γc s)
    dsimp only [d]
    rw [hP]
    simp

private theorem riemannianComplexMFDeriv_apply_eq_fderiv_comp_tangentLine
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (G : M → ℂ) (x : M) (hx : I.IsInteriorPoint x)
    (v : TangentSpace I x)
    (hG : MDifferentiableAt I 𝓘(ℝ, ℂ) G x) :
    riemannianComplexMFDeriv I G x v =
      fderiv ℝ (G ∘ riemannianTangentChartLine I x v) 0 1 := by
  let γ : ℝ → M := riemannianTangentChartLine I x v
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    mdifferentiableAt_riemannianTangentChartLine_zero I x hx v
  have hG' : MDifferentiableAt I 𝓘(ℝ, ℂ) G (γ 0) := by
    simpa only [γ, riemannianTangentChartLine_zero] using hG
  have hcomp := mfderiv_comp 0 hG' hγ
  rw [show γ = riemannianTangentChartLine I x v from rfl,
    mfderiv_riemannianTangentChartLine_zero I x hx v,
    riemannianTangentChartLine_zero] at hcomp
  have hcomp' : fderiv ℝ (G ∘ γ) 0 =
      (mfderiv I 𝓘(ℝ, ℂ) G x) ∘L
        ContinuousLinearMap.toSpanSingleton ℝ v := by
    simpa only [mfderiv_eq_fderiv, γ,
      riemannianTangentChartLine_zero] using hcomp
  rw [hcomp']
  unfold riemannianComplexMFDeriv
  change (NormedSpace.fromTangentSpace (G x))
      (mfderiv I 𝓘(ℝ, ℂ) G x v) =
    (mfderiv I 𝓘(ℝ, ℂ) G x)
      (ContinuousLinearMap.toSpanSingleton ℝ v 1)
  rw [ContinuousLinearMap.toSpanSingleton_apply_one]
  rfl

theorem riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (n : ℕ) (x : M) (hx : I.IsInteriorPoint x)
    (v : TangentSpace I x) (d : ℝ → ℝ)
    (hdL2 : MemLp (fun t ↦ (d t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)))
    (hdweighted : ∀ (w : ℝ → ℝ), Continuous w → (∀ t, |w t| ≤ 1) →
      HasFDerivAt (fun s : ℝ ↦ ∫ t in (-Real.pi)..Real.pi,
        oddDistanceProfile boundary (angleToUnitAddCircle t)
          (riemannianTangentChartLine I x v s) * w t)
        (ContinuousLinearMap.toSpanSingleton ℝ
          (∫ t in (-Real.pi)..Real.pi, d t * w t)) 0)
    (hFourierDiff : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (oddProfileFourierMap boundary n) x) :
    riemannianComplexMFDeriv I (oddProfileFourierMap boundary n) x v =
      2 * fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
        (fun t ↦ (d t : ℂ)) (-(n : ℤ)) := by
  let γ : ℝ → M := riemannianTangentChartLine I x v
  have hcosRaw := hdweighted (fun t ↦ Real.cos ((n : ℝ) * t))
    (by fun_prop) (fun t ↦ Real.abs_cos_le_one _)
  have hsinRaw := hdweighted (fun t ↦ Real.sin ((n : ℝ) * t))
    (by fun_prop) (fun t ↦ Real.abs_sin_le_one _)
  have hcos : HasFDerivAt
      (oddProfileCosineCoordinate boundary n ∘ γ)
      ((1 / Real.pi : ℝ) • ContinuousLinearMap.toSpanSingleton ℝ
        (∫ t in (-Real.pi)..Real.pi, d t * Real.cos ((n : ℝ) * t))) 0 := by
    simpa only [oddProfileCosineCoordinate, γ, Function.comp_apply] using
      hcosRaw.const_mul (1 / Real.pi)
  have hsin : HasFDerivAt
      (oddProfileSineCoordinate boundary n ∘ γ)
      ((1 / Real.pi : ℝ) • ContinuousLinearMap.toSpanSingleton ℝ
        (∫ t in (-Real.pi)..Real.pi, d t * Real.sin ((n : ℝ) * t))) 0 := by
    simpa only [oddProfileSineCoordinate, γ, Function.comp_apply] using
      hsinRaw.const_mul (1 / Real.pi)
  have hcosC := Complex.ofRealCLM.hasFDerivAt.comp 0 hcos
  have hsinC := Complex.ofRealCLM.hasFDerivAt.comp 0 hsin
  have hcurve : HasFDerivAt
      (oddProfileFourierMap boundary n ∘ γ)
      (Complex.ofRealCLM.comp
          ((1 / Real.pi : ℝ) • ContinuousLinearMap.toSpanSingleton ℝ
            (∫ t in (-Real.pi)..Real.pi, d t * Real.cos ((n : ℝ) * t))) +
        Complex.I • Complex.ofRealCLM.comp
          ((1 / Real.pi : ℝ) • ContinuousLinearMap.toSpanSingleton ℝ
            (∫ t in (-Real.pi)..Real.pi, d t * Real.sin ((n : ℝ) * t)))) 0 := by
    simpa only [oddProfileFourierMap, γ, Function.comp_apply] using
      hcosC.add (hsinC.mul_const Complex.I)
  have hvalue :
      riemannianComplexMFDeriv I (oddProfileFourierMap boundary n) x v =
        (((1 / Real.pi : ℝ) *
          ∫ t in (-Real.pi)..Real.pi, d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) +
        ((((1 / Real.pi : ℝ) *
          ∫ t in (-Real.pi)..Real.pi, d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) *
            Complex.I) := by
    rw [riemannianComplexMFDeriv_apply_eq_fderiv_comp_tangentLine
      I (oddProfileFourierMap boundary n) x hx v hFourierDiff,
      show riemannianTangentChartLine I x v = γ from rfl, hcurve.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    simp only [smul_eq_mul, one_mul]
    push_cast
    ring
  have hInt : IntervalIntegrable (fun t ↦ (d t : ℂ)) volume
      (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simpa [IntegrableOn] using
      hdL2.integrable (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi))
        (by norm_num)
  have hcoeff := two_mul_fourierCoeffOn_neg_eq_cos_add_sin
    (by linarith [Real.pi_pos] : -Real.pi < Real.pi) hInt n
  rw [hvalue, hcoeff]
  have hdReal : IntervalIntegrable d volume (-Real.pi) Real.pi := by
    constructor
    · simpa using Complex.reCLM.integrable_comp hInt.1
    · simpa using Complex.reCLM.integrable_comp hInt.2
  have hcosInt : IntervalIntegrable
      (fun t ↦ d t * Real.cos ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    exact hdReal.mul_continuousOn (by
      simpa [Set.uIcc_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using
        (show ContinuousOn (fun t : ℝ ↦ Real.cos ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hsinInt : IntervalIntegrable
      (fun t ↦ d t * Real.sin ((n : ℝ) * t)) volume
      (-Real.pi) Real.pi := by
    exact hdReal.mul_continuousOn (by
      simpa [Set.uIcc_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using
        (show ContinuousOn (fun t : ℝ ↦ Real.sin ((n : ℝ) * t))
          (Set.Icc (-Real.pi) Real.pi) from by fun_prop))
  have hcosCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            d t * Real.cos ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.intervalIntegral_comp_comm hcosInt)
  have hsinCast :
      (∫ t in (-Real.pi)..Real.pi,
          ((d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ)) =
        ((∫ t in (-Real.pi)..Real.pi,
            d t * Real.sin ((n : ℝ) * t) : ℝ) : ℂ) := by
    simpa using (Complex.ofRealCLM.intervalIntegral_comp_comm hsinInt)
  rw [hcosCast, hsinCast]
  push_cast
  ring

/-- Pointwise intrinsic derivative-energy budget for every finite family of
positive odd Fourier modes. -/
theorem sum_riemannianComplexDerivativeEnergy_oddProfileFourierMap_le_two
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : Fin N,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    (∑ k : Fin N, riemannianComplexDerivativeEnergy I x e
      (oddProfileFourierMap boundary (oddMode k))) ≤ 2 := by
  obtain ⟨d0, hd0meas, hd0eq, hd0weighted, _hd0anti⟩ :=
    exists_tangentProfileDerivativeField I hboundary x hx (e 0) hdiff
  obtain ⟨d1, hd1meas, hd1eq, hd1weighted, _hd1anti⟩ :=
    exists_tangentProfileDerivativeField I hboundary x hx (e 1) hdiff
  have hd0bound : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi), ‖(d0 t : ℂ)‖ ≤ 1 := by
    filter_upwards [hd0eq, hdiff] with t hdeq htdiff
    rw [hdeq]
    rw [Complex.norm_real]
    calc
      ‖(NormedSpace.fromTangentSpace
          (oddDistanceProfile boundary (angleToUnitAddCircle t) x))
            (mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x (e 0))‖ =
          ‖mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x (e 0)‖ := by
            rfl
      _ ≤ ‖mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x‖ * ‖e 0‖ :=
        (mfderiv I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) x).le_opNorm (e 0)
      _ ≤ 1 * 1 := mul_le_mul
        (norm_mfderiv_oddDistanceProfile_le_one I boundary
          (angleToUnitAddCircle t) x hx htdiff)
        (e.orthonormal.norm_eq_one 0).le
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hd1bound : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi), ‖(d1 t : ℂ)‖ ≤ 1 := by
    filter_upwards [hd1eq, hdiff] with t hdeq htdiff
    rw [hdeq]
    rw [Complex.norm_real]
    calc
      ‖(NormedSpace.fromTangentSpace
          (oddDistanceProfile boundary (angleToUnitAddCircle t) x))
            (mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x (e 1))‖ =
          ‖mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x (e 1)‖ := by
            rfl
      _ ≤ ‖mfderiv I 𝓘(ℝ, ℝ)
              (oddDistanceProfile boundary (angleToUnitAddCircle t)) x‖ * ‖e 1‖ :=
        (mfderiv I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) x).le_opNorm (e 1)
      _ ≤ 1 * 1 := mul_le_mul
        (norm_mfderiv_oddDistanceProfile_le_one I boundary
          (angleToUnitAddCircle t) x hx htdiff)
        (e.orthonormal.norm_eq_one 1).le
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hd0L2 : MemLp (fun t ↦ (d0 t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hd0meas).aestronglyMeasurable
      1 hd0bound
  have hd1L2 : MemLp (fun t ↦ (d1 t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hd1meas).aestronglyMeasurable
      1 hd1bound
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hfieldBound : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      ‖(d0 t : ℂ)‖ ^ 2 + ‖(d1 t : ℂ)‖ ^ 2 ≤ 1 := by
    filter_upwards [hd0eq, hd1eq, hdiff] with t hd0t hd1t htdiff
    let D : TangentSpace I x →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace
        (oddDistanceProfile boundary (angleToUnitAddCircle t) x)).toContinuousLinearMap.comp
          (mfderiv I 𝓘(ℝ, ℝ)
            (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    have hDnormEq : ‖D‖ =
        ‖mfderiv I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t)) x‖ := by
      apply ContinuousLinearMap.opNorm_ext
      intro v
      rfl
    have hDnorm : ‖D‖ ≤ 1 := by
      rw [hDnormEq]
      exact norm_mfderiv_oddDistanceProfile_le_one I boundary
        (angleToUnitAddCircle t) x hx htdiff
    have hdual := e.norm_dual D
    rw [Fin.sum_univ_two] at hdual
    have hDbudget : (D (e 0)) ^ 2 + (D (e 1)) ^ 2 ≤ 1 := by
      rw [← hdual]
      nlinarith [norm_nonneg D]
    simpa [hd0t, hd1t, D, Complex.norm_real, sq_abs] using hDbudget
  have hpow0 : IntervalIntegrable (fun t ↦ ‖(d0 t : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hd0L2)
  have hpow1 : IntervalIntegrable (fun t ↦ ‖(d1 t : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hd1L2)
  have hsumIntegral :
      (∫ t in (-Real.pi)..Real.pi,
          ‖(d0 t : ℂ)‖ ^ 2 + ‖(d1 t : ℂ)‖ ^ 2) ≤
        ∫ _t in (-Real.pi)..Real.pi, (1 : ℝ) := by
    have hconst : IntervalIntegrable (fun _t : ℝ ↦ (1 : ℝ)) volume
        (-Real.pi) Real.pi := by
      exact (continuous_const : Continuous (fun _t : ℝ ↦ (1 : ℝ)))
        |>.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
    rw [intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_of_le hab.le]
    exact MeasureTheory.integral_mono_ae
      (hpow0.1.add hpow1.1) hconst.1 hfieldBound
  have hsumEnergy :
      (∫ t in (-Real.pi)..Real.pi, ‖(d0 t : ℂ)‖ ^ 2) +
        (∫ t in (-Real.pi)..Real.pi, ‖(d1 t : ℂ)‖ ^ 2) ≤
          Real.pi - -Real.pi := by
    rw [intervalIntegral.integral_add hpow0 hpow1] at hsumIntegral
    simpa using hsumIntegral
  have hlengthPos : 0 < Real.pi - -Real.pi := sub_pos.mpr hab
  have hfieldEnergy :
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi, ‖(d0 t : ℂ)‖ ^ 2) +
      2 * ((Real.pi - -Real.pi)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi, ‖(d1 t : ℂ)‖ ^ 2) ≤ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hsumEnergy
      (inv_nonneg.mpr hlengthPos.le)
    have hunit : (Real.pi - -Real.pi)⁻¹ *
        (Real.pi - -Real.pi) = 1 := by
      exact inv_mul_cancel₀ (ne_of_gt hlengthPos)
    calc
      2 * ((Real.pi - -Real.pi)⁻¹ *
          ∫ t in (-Real.pi)..Real.pi, ‖(d0 t : ℂ)‖ ^ 2) +
        2 * ((Real.pi - -Real.pi)⁻¹ *
          ∫ t in (-Real.pi)..Real.pi, ‖(d1 t : ℂ)‖ ^ 2) =
          2 * ((Real.pi - -Real.pi)⁻¹ *
            ((∫ t in (-Real.pi)..Real.pi, ‖(d0 t : ℂ)‖ ^ 2) +
              ∫ t in (-Real.pi)..Real.pi, ‖(d1 t : ℂ)‖ ^ 2)) := by ring
      _ ≤ 2 * ((Real.pi - -Real.pi)⁻¹ *
          (Real.pi - -Real.pi)) := by gcongr
      _ = 2 := by rw [hunit]; ring
  have hcoeff0 : ∀ k : Fin N,
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 0) =
        2 * fourierCoeffOn hab (fun t ↦ (d0 t : ℂ))
          (-(oddMode k : ℤ)) := by
    intro k
    exact
      riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
        I (oddMode k) x hx (e 0) d0 hd0L2 hd0weighted (hFourierDiff k)
  have hcoeff1 : ∀ k : Fin N,
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 1) =
        2 * fourierCoeffOn hab (fun t ↦ (d1 t : ℂ))
          (-(oddMode k : ℤ)) := by
    intro k
    exact
      riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
        I (oddMode k) x hx (e 1) d1 hd1L2 hd1weighted (hFourierDiff k)
  have hoddinj : Function.Injective (fun k : Fin N ↦ oddMode k) := by
    intro k l hkl
    apply Fin.val_injective
    have hval : 2 * k.val + 1 = 2 * l.val + 1 := by
      simpa only [oddMode] using hkl
    omega
  have hoddpos : ∀ k : Fin N, 0 < oddMode k := by
    intro k
    unfold oddMode
    omega
  have hb0 := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab d0 hd0L2 (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  have hb1 := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab d1 hd1L2 (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  simp only [smul_eq_mul] at hb0 hb1
  have hrewrite :
      (∑ k : Fin N, riemannianComplexDerivativeEnergy I x e
        (oddProfileFourierMap boundary (oddMode k))) =
        4 * (∑ k : Fin N,
          ‖fourierCoeffOn hab (fun t ↦ (d0 t : ℂ))
            (-(oddMode k : ℤ))‖ ^ 2) +
        4 * (∑ k : Fin N,
          ‖fourierCoeffOn hab (fun t ↦ (d1 t : ℂ))
            (-(oddMode k : ℤ))‖ ^ 2) := by
    simp_rw [riemannianComplexDerivativeEnergy, hcoeff0, hcoeff1, norm_mul]
    simp_rw [mul_pow]
    norm_num
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hrewrite]
  linarith

/-- The derivative-energy budget implies the pointwise unit intrinsic
two-Jacobian budget for the same finite odd-mode family. -/
theorem sum_riemannianTwoJacobian_oddProfileFourierMap_le_one
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : Fin N,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    (∑ k : Fin N, riemannianTwoJacobian I
      (oddProfileFourierMap boundary (oddMode k)) x) ≤ 1 := by
  exact sum_riemannianTwoJacobian_le_one_of_derivativeEnergy I
    (fun k : Fin N ↦ oddProfileFourierMap boundary (oddMode k)) x e
    (sum_riemannianComplexDerivativeEnergy_oddProfileFourierMap_le_two
      I hboundary N x hx e hdiff hFourierDiff)

end

end GromovFilling

#print axioms GromovFilling.sum_riemannianComplexDerivativeEnergy_oddProfileFourierMap_le_two
#print axioms GromovFilling.sum_riemannianTwoJacobian_oddProfileFourierMap_le_one
