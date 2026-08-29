import GromovFilling.RiemannianProfileFourierEnergy
import GromovFilling.RiemannianInteriorAtlasArea

/-!
# Almost-everywhere intrinsic Fourier budgets on Riemannian fillings

This module closes the measure-theoretic bridge from angular distance-profile
differentiability to the canonical Riemannian surface-area budget.  Joint
Lipschitz regularity and Fubini provide the required profile derivatives on
controlled chart pieces.  Orthogonal Givens mixing preserves intrinsic
Fourier energy, and the resulting pointwise Jacobian estimate is transported
through weighted chart measures and summed over the canonical area measure.
-/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

private theorem fromTangentSpace_complex_toContinuousLinearMap (a : ℂ) :
    (NormedSpace.fromTangentSpace a).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ ℂ := by
  rfl

private theorem angleToUnitAddCircle_lipschitzWith :
    LipschitzWith
      ⟨(2 * Real.pi)⁻¹, inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)⟩
      angleToUnitAddCircle := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, show angleToUnitAddCircle s - angleToUnitAddCircle t =
      (((s - t) / (2 * Real.pi) : ℝ) : UnitAddCircle) by
    rw [show angleToUnitAddCircle s =
        ((s / (2 * Real.pi) : ℝ) : UnitAddCircle) by rfl,
      show angleToUnitAddCircle t =
        ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) by rfl,
      ← AddCircle.coe_sub]
    congr 1
    ring]
  calc
    ‖(((s - t) / (2 * Real.pi) : ℝ) : UnitAddCircle)‖ ≤
        ‖(s - t) / (2 * Real.pi)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |s - t| / (2 * Real.pi) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    _ = (2 * Real.pi)⁻¹ * dist s t := by
      rw [Real.dist_eq]
      field_simp

private theorem IsometricCircleBoundary.lipschitzWith_oddDistanceProfile_parameter
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary) (x : X) :
    LipschitzWith 1 (fun t : ℝ ↦
      oddDistanceProfile boundary (angleToUnitAddCircle t) x) := by
  apply LipschitzWith.mk_one
  intro s t
  rw [Real.dist_eq]
  unfold oddDistanceProfile boundaryDistance
  have hfirst :
      |dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary (angleToUnitAddCircle t))| ≤ |s - t| := by
    calc
      |dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary (angleToUnitAddCircle t))| ≤
          dist (boundary (angleToUnitAddCircle s))
            (boundary (angleToUnitAddCircle t)) := by
        simpa only [Real.dist_eq] using dist_dist_dist_le_right x
          (boundary (angleToUnitAddCircle s))
          (boundary (angleToUnitAddCircle t))
      _ = 2 * Real.pi * dist (angleToUnitAddCircle s)
          (angleToUnitAddCircle t) := hboundary _ _
      _ ≤ 2 * Real.pi * ((2 * Real.pi)⁻¹ * dist s t) := by
        gcongr
        exact angleToUnitAddCircle_lipschitzWith.dist_le_mul s t
      _ = |s - t| := by
        rw [Real.dist_eq]
        field_simp [Real.pi_ne_zero]
  have hsecond :
      |dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))| ≤
        |s - t| := by
    calc
      |dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))| ≤
          dist
            (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))
            (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))) := by
        simpa only [Real.dist_eq] using dist_dist_dist_le_right x
          (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))
          (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))
      _ = 2 * Real.pi *
          dist
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)) :=
        hboundary _ _
      _ = 2 * Real.pi *
          dist (angleToUnitAddCircle s) (angleToUnitAddCircle t) := by
        rw [dist_add_right]
      _ ≤ 2 * Real.pi * ((2 * Real.pi)⁻¹ * dist s t) := by
        gcongr
        exact angleToUnitAddCircle_lipschitzWith.dist_le_mul s t
      _ = |s - t| := by
        rw [Real.dist_eq]
        field_simp [Real.pi_ne_zero]
  calc
    |(dist x (boundary (angleToUnitAddCircle s)) -
          dist x (boundary
            (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
        (dist x (boundary (angleToUnitAddCircle t)) -
          dist x (boundary
            (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2| =
        |(dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary (angleToUnitAddCircle t))) -
          (dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))))| / 2 := by
      rw [show
        (dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
          (dist x (boundary (angleToUnitAddCircle t)) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 =
          ((dist x (boundary (angleToUnitAddCircle s)) -
              dist x (boundary (angleToUnitAddCircle t))) -
            (dist x (boundary
                (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
              dist x (boundary
                (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle))))) / 2 by
          ring,
        abs_div]
      norm_num
    _ ≤
        (|dist x (boundary (angleToUnitAddCircle s)) -
            dist x (boundary (angleToUnitAddCircle t))| +
          |dist x (boundary
              (angleToUnitAddCircle s + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist x (boundary
              (angleToUnitAddCircle t + ((1 / 2 : ℝ) : UnitAddCircle)))|) / 2 := by
      gcongr
      exact abs_sub _ _
    _ ≤ |s - t| := by linarith

private theorem ControlledInteriorAtlas.lipschitzOnWith_oddDistanceProfile_uncurry
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
    LipschitzOnWith (1 + A.lipschitzConstant i)
      (fun p : ℝ × ℂ ↦ oddDistanceProfile boundary
        (angleToUnitAddCircle p.1) (A.parametrization i p.2))
      (Set.univ ×ˢ A.domain i) := by
  apply LipschitzOnWith.of_dist_le_mul
  rintro ⟨s, z⟩ ⟨-, hz⟩ ⟨t, w⟩ ⟨-, hw⟩
  calc
    dist
        (oddDistanceProfile boundary (angleToUnitAddCircle s)
          (A.parametrization i z))
        (oddDistanceProfile boundary (angleToUnitAddCircle t)
          (A.parametrization i w)) ≤
        dist
            (oddDistanceProfile boundary (angleToUnitAddCircle s)
              (A.parametrization i z))
            (oddDistanceProfile boundary (angleToUnitAddCircle t)
              (A.parametrization i z)) +
          dist
            (oddDistanceProfile boundary (angleToUnitAddCircle t)
              (A.parametrization i z))
            (oddDistanceProfile boundary (angleToUnitAddCircle t)
              (A.parametrization i w)) := dist_triangle _ _ _
    _ ≤ dist s t + dist (A.parametrization i z) (A.parametrization i w) := by
      exact add_le_add
        (by simpa using
          (hboundary.lipschitzWith_oddDistanceProfile_parameter
            (A.parametrization i z)).dist_le_mul s t)
        (by simpa using
          (oddDistanceProfile_lipschitzWith boundary
            (angleToUnitAddCircle t)).dist_le_mul
              (A.parametrization i z) (A.parametrization i w))
    _ ≤ dist s t + (A.lipschitzConstant i : ℝ) * dist z w := by
      gcongr
      exact (A.lipschitzOnWith_parametrization i).dist_le_mul z hz w hw
    _ ≤ (1 + (A.lipschitzConstant i : ℝ)) * dist (s, z) (t, w) := by
      rw [Prod.dist_eq]
      calc
        dist s t + (A.lipschitzConstant i : ℝ) * dist z w ≤
            max (dist s t) (dist z w) +
              (A.lipschitzConstant i : ℝ) *
                max (dist s t) (dist z w) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
        _ = (1 + (A.lipschitzConstant i : ℝ)) *
            max (dist s t) (dist z w) := by ring

private theorem ControlledInteriorAtlas.mdifferentiableAt_real_of_differentiableAt_comp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (f : M → ℝ) (i : ℕ) (z : ℂ)
    (hz : z ∈ A.domain i)
    (hdiff : DifferentiableAt ℝ (f ∘ A.parametrization i) z) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f (A.parametrization i z) := by
  let G : M → ℂ := Complex.ofRealCLM ∘ f
  have hGcomp : DifferentiableAt ℝ (G ∘ A.parametrization i) z := by
    exact Complex.ofRealCLM.differentiableAt.comp z hdiff
  have hG : MDifferentiableAt I 𝓘(ℝ, ℂ) G (A.parametrization i z) :=
    A.mdifferentiableAt_of_differentiableAt_comp i G z hz hGcomp
  have hre := Complex.reCLM.differentiableAt.comp_mdifferentiableAt hG
  simpa only [G, Function.comp_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_re] using hre

theorem ControlledInteriorAtlas.ae_ae_mdifferentiableAt_oddDistanceProfile
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
      ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
        MDifferentiableAt I 𝓘(ℝ, ℝ)
          (oddDistanceProfile boundary (angleToUnitAddCircle t))
          (A.parametrization i z) := by
  let pulled : ℝ × ℂ → ℝ := fun p ↦
    oddDistanceProfile boundary (angleToUnitAddCircle p.1)
      (A.parametrization i p.2)
  obtain ⟨g, hg, hEq⟩ :=
    (A.lipschitzOnWith_oddDistanceProfile_uncurry I hboundary i).extend_real
  let G : ℝ → ℂ → ℝ := fun t z ↦ g (t, z)
  let P : ℝ → ℂ → Prop := fun t z ↦ DifferentiableAt ℝ (G t) z
  have hGcont : Continuous (Function.uncurry G) := by
    simpa only [G, Function.uncurry] using hg.continuous
  have hP : MeasurableSet {p : ℝ × ℂ | P p.1 p.2} :=
    measurableSet_of_differentiableAt_with_param ℝ hGcont
  have ht : ∀ᵐ t : ℝ ∂volume,
      ∀ᵐ z ∂volume.restrict (A.piece I i), P t z := by
    apply ae_of_all
    intro t
    have hLip : LipschitzOnWith (A.lipschitzConstant i)
        (fun z : ℂ ↦ pulled (t, z)) (A.domain i) := by
      simpa only [pulled, Function.comp_apply, one_mul] using
        (oddDistanceProfile_lipschitzWith boundary
        (angleToUnitAddCircle t)).comp_lipschitzOnWith
          (A.lipschitzOnWith_parametrization i)
    have hdiffWithin := hLip.ae_differentiableWithinAt (μ := volume)
      (A.isOpen_domain i).measurableSet
    have hdiffDomain : ∀ᵐ z ∂volume.restrict (A.domain i), P t z := by
      filter_upwards [ae_restrict_mem (A.isOpen_domain i).measurableSet,
        hdiffWithin] with z hz hdiff
      have hactual : DifferentiableAt ℝ (fun w : ℂ ↦ pulled (t, w)) z :=
        hdiff.differentiableAt ((A.isOpen_domain i).mem_nhds hz)
      have hev : G t =ᶠ[nhds z] fun w : ℂ ↦ pulled (t, w) :=
        ((A.isOpen_domain i).eventually_mem hz).mono fun w hw ↦ by
          exact (hEq (show (t, w) ∈ Set.univ ×ˢ A.domain i from
            ⟨Set.mem_univ t, hw⟩)).symm
      exact hactual.congr_of_eventuallyEq hev
    exact ae_mono
      (Measure.restrict_mono (A.piece_subset_domain I i) le_rfl)
      hdiffDomain
  have hz : ∀ᵐ z ∂volume.restrict (A.piece I i),
      ∀ᵐ t : ℝ ∂volume, P t z :=
    (MeasureTheory.Measure.ae_ae_comm
      (μ := volume) (ν := volume.restrict (A.piece I i)) hP).mp ht
  filter_upwards [ae_restrict_mem (A.measurableSet_piece I i), hz] with
      z hzPiece hz'
  have hzDomain : z ∈ A.domain i := A.piece_subset_domain I i hzPiece
  filter_upwards [ae_restrict_of_ae hz'] with t htdiff
  let f : M → ℝ :=
    oddDistanceProfile boundary (angleToUnitAddCircle t)
  have hev : (f ∘ A.parametrization i) =ᶠ[nhds z] G t :=
    ((A.isOpen_domain i).eventually_mem hzDomain).mono fun w hw ↦ by
      exact hEq (show (t, w) ∈ Set.univ ×ˢ A.domain i from
        ⟨Set.mem_univ t, hw⟩)
  exact A.mdifferentiableAt_real_of_differentiableAt_comp I f i z hzDomain
    (htdiff.congr_of_eventuallyEq hev)

private theorem sum_norm_sq_complex_matrix_mix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (horth : U.transpose * U = 1) (v : ι → ℂ) :
    (∑ j, ‖∑ k, U j k • v k‖ ^ 2) = ∑ k, ‖v k‖ ^ 2 := by
  have hre (j : ι) :
      (∑ k, U j k • v k).re = U.mulVec (fun k ↦ (v k).re) j := by
    simp [Complex.mul_re, Matrix.mulVec, dotProduct]
  have him (j : ι) :
      (∑ k, U j k • v k).im = U.mulVec (fun k ↦ (v k).im) j := by
    simp [Complex.mul_im, Matrix.mulVec, dotProduct]
  simp_rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← pow_two]
  rw [
    orthogonal_mulVec_energy U horth (fun k ↦ (v k).re),
    orthogonal_mulVec_energy U horth (fun k ↦ (v k).im)]

private theorem riemannianComplexMFDeriv_givensMetricFourierMap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (j : Fin N) (x : M)
    (hdiff : ∀ k : Fin N,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    riemannianComplexMFDeriv I
        (givensMetricFourierMap boundary N j) x =
      -(∑ k : Fin N, (givensMatrix N j k : ℝ) •
        riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x) := by
  let F : Fin N → M → ℂ := fun k ↦
    oddProfileFourierMap boundary (oddMode k)
  have hsum : HasMFDerivAt I 𝓘(ℝ, ℂ)
      (∑ k : Fin N, (givensMatrix N j k : ℝ) • F k) x
      (∑ k : Fin N, (givensMatrix N j k : ℝ) •
        mfderiv I 𝓘(ℝ, ℂ) (F k) x) := by
    apply HasMFDerivAt.sum
    intro k _
    exact (hdiff k).hasMFDerivAt.const_smul (givensMatrix N j k)
  have hneg := hsum.neg
  have hfun : givensMetricFourierMap boundary N j =
      -(∑ k : Fin N, (givensMatrix N j k : ℝ) • F k) := by
    funext y
    simp only [givensMetricFourierMap, mixedOddProfileFourierMap,
      Pi.neg_apply, Finset.sum_apply, Pi.smul_apply]
    congr 1
  have hmf : mfderiv I 𝓘(ℝ, ℂ)
      (givensMetricFourierMap boundary N j) x =
      -(∑ k : Fin N, (givensMatrix N j k : ℝ) •
        mfderiv I 𝓘(ℝ, ℂ) (F k) x) := by
    rw [hfun]
    exact hneg.mfderiv
  ext v
  unfold riemannianComplexMFDeriv
  simp only [fromTangentSpace_complex_toContinuousLinearMap]
  rw [hmf]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, F]
  rw [map_neg]
  congr 1
  let L : Fin N → TangentSpace I x →L[ℝ] ℂ := fun k ↦
    (givensMatrix N j k : ℝ) •
      (mfderiv I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x :
          TangentSpace I x →L[ℝ] ℂ)
  change (ContinuousLinearMap.id ℝ ℂ) ((∑ k, L k) v) =
    ∑ k : Fin N, (givensMatrix N j k : ℝ) •
      (ContinuousLinearMap.id ℝ ℂ)
        (mfderiv I 𝓘(ℝ, ℂ)
          (oddProfileFourierMap boundary (oddMode k)) x v)
  have hsumApply : (∑ k, L k) v = ∑ k, L k v := by
    simp
  rw [hsumApply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (ContinuousLinearMap.id ℝ ℂ)
      ((givensMatrix N j k : ℝ) •
        (mfderiv I 𝓘(ℝ, ℂ)
          (oddProfileFourierMap boundary (oddMode k)) x v : ℂ)) =
    (givensMatrix N j k : ℝ) •
      (ContinuousLinearMap.id ℝ ℂ)
        (mfderiv I 𝓘(ℝ, ℂ)
          (oddProfileFourierMap boundary (oddMode k)) x v : ℂ)
  exact map_smul (ContinuousLinearMap.id ℝ ℂ)
    (givensMatrix N j k) _

theorem sum_riemannianComplexDerivativeEnergy_givensMetricFourierMap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ k : Fin N,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    (∑ j : Fin N, riemannianComplexDerivativeEnergy I x e
      (givensMetricFourierMap boundary N j)) =
      ∑ k : Fin N, riemannianComplexDerivativeEnergy I x e
        (oddProfileFourierMap boundary (oddMode k)) := by
  have hderiv (j : Fin N) :=
    riemannianComplexMFDeriv_givensMetricFourierMap I N j x hdiff
  simp_rw [riemannianComplexDerivativeEnergy, hderiv,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, norm_neg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · exact sum_norm_sq_complex_matrix_mix (givensMatrix N)
      (givensMatrix_orthogonal N)
      (fun k : Fin N ↦ riemannianComplexMFDeriv I
        (oddProfileFourierMap boundary (oddMode k)) x (e 0))
  · exact sum_norm_sq_complex_matrix_mix (givensMatrix N)
      (givensMatrix_orthogonal N)
      (fun k : Fin N ↦ riemannianComplexMFDeriv I
        (oddProfileFourierMap boundary (oddMode k)) x (e 1))

/-- Orthogonal mixing transfers the intrinsic odd-mode energy estimate to
the boundary curves used by the finite coverage certificate. -/
theorem sum_riemannianTwoJacobian_givensMetricFourierMap_le_one
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
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : Fin N,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    (∑ j : Fin N, riemannianTwoJacobian I
      (givensMetricFourierMap boundary N j) x) ≤ 1 := by
  apply sum_riemannianTwoJacobian_le_one_of_derivativeEnergy I
    (fun j : Fin N ↦ givensMetricFourierMap boundary N j) x e
  rw [sum_riemannianComplexDerivativeEnergy_givensMetricFourierMap
    I N x e hFourierDiff]
  exact sum_riemannianComplexDerivativeEnergy_oddProfileFourierMap_le_two
    I hboundary N x hx e hprofileDiff hFourierDiff

set_option maxHeartbeats 800000 in
private theorem ae_le_one_riemannianChartAreaMeasure_of_ae_le_one_comp
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [MeasurableSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) (q : M → ℝ≥0∞)
    (hF : AEMeasurable F (volume.restrict s))
    (hq : AEMeasurable q (riemannianChartAreaMeasure I F s))
    (hsource : ∀ᵐ z ∂volume.restrict s, q (F z) ≤ 1) :
    ∀ᵐ x ∂riemannianChartAreaMeasure I F s, q x ≤ 1 := by
  let ν : Measure ℂ :=
    (volume.restrict s).withDensity (riemannianChartDensity I F)
  have hνac : ν ≪ volume.restrict s := by
    exact withDensity_absolutelyContinuous _ _
  have hFν : AEMeasurable F ν := hF.mono_ac hνac
  have hqMap : AEMeasurable q (Measure.map F ν) := by
    simpa only [ν, riemannianChartAreaMeasure] using hq
  let qm : M → ℝ≥0∞ := hqMap.mk q
  have hqm : Measurable qm := hqMap.measurable_mk
  have heq : q =ᵐ[Measure.map F ν] qm := hqMap.ae_eq_mk
  have heqComp : (fun z ↦ q (F z)) =ᵐ[ν] fun z ↦ qm (F z) :=
    ae_of_ae_map hFν heq
  have hsourceν : ∀ᵐ z ∂ν, q (F z) ≤ 1 :=
    (Measure.ae_le_iff_absolutelyContinuous.mpr hνac) hsource
  have hqmSource : ∀ᵐ z ∂ν, qm (F z) ≤ 1 := by
    filter_upwards [hsourceν, heqComp] with z hz heqz
    simpa only [← heqz] using hz
  have hqmTarget : ∀ᵐ x ∂Measure.map F ν, qm x ≤ 1 :=
    (ae_map_iff hFν (measurableSet_le hqm measurable_const)).2 hqmSource
  have htarget : ∀ᵐ x ∂Measure.map F ν, q x ≤ 1 := by
    filter_upwards [heq, hqmTarget] with x heqx hx
    simpa only [heqx] using hx
  simpa only [ν, riemannianChartAreaMeasure] using htarget

/-- On each disjoint controlled chart piece, the mixed family satisfies the
sharp unit intrinsic Jacobian budget at planar-volume almost every source
point. -/
theorem ControlledInteriorAtlas.ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M)
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (A.piece I i),
      (∑ j : Fin N, riemannianTwoJacobian I
        (givensMetricFourierMap boundary N j)
        (A.parametrization i z)) ≤ 1 := by
  have hprofile :=
    A.ae_ae_mdifferentiableAt_oddDistanceProfile I hboundary i
  have hFourier : ∀ᵐ z ∂volume.restrict (A.piece I i),
      ∀ k : Fin N,
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
  have hx : I.IsInteriorPoint (A.parametrization i z) := by
    exact A.image_subset_interior i
      ⟨z, A.piece_subset_domain I i hz, rfl⟩
  letI : Fact (Module.finrank ℝ
      (TangentSpace I (A.parametrization i z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (A.parametrization i z)⟩
  exact sum_riemannianTwoJacobian_givensMetricFourierMap_le_one
    I hboundary N (A.parametrization i z) hx
      (canonicalOrthonormalBasisTwo
        (TangentSpace I (A.parametrization i z)))
      hprofilez hFourierz

/-- The mixed unit Jacobian budget transported from planar source volume to
one weighted Riemannian chart-area contribution. -/
theorem ControlledInteriorAtlas.ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one_chartArea
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
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (i : ℕ) :
    ∀ᵐ x ∂riemannianChartAreaMeasure I (A.parametrization i) (A.piece I i),
      (∑ j : Fin N, riemannianTwoJacobian I
        (givensMetricFourierMap boundary N j) x) ≤ 1 := by
  let q : M → ℝ≥0∞ := fun x ↦
    ∑ j : Fin N, ENNReal.ofReal (riemannianTwoJacobian I
      (givensMetricFourierMap boundary N j) x)
  have hF : AEMeasurable (A.parametrization i)
      (volume.restrict (A.piece I i)) :=
    ((A.continuousOn_parametrization i).mono
      (A.piece_subset_domain I i)).aemeasurable
        (A.measurableSet_piece I i)
  have hq : AEMeasurable q
      (riemannianChartAreaMeasure I (A.parametrization i)
        (A.piece I i)) := by
    dsimp only [q]
    have hsum := Finset.aemeasurable_sum Finset.univ fun j _hj ↦
      A.aemeasurable_riemannianTwoJacobian_of_lipschitzWith I
        (givensMetricFourierMap boundary N j)
        (givensMetricFourierMap_lipschitzWith hboundary N j) i
    convert hsum using 1
    funext x
    simp
  have hsourceReal :=
    A.ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one
      I hboundary N i
  have hsource : ∀ᵐ z ∂volume.restrict (A.piece I i),
      q (A.parametrization i z) ≤ 1 := by
    filter_upwards [hsourceReal] with z hz
    dsimp only [q]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · exact ENNReal.ofReal_le_one.mpr hz
    · intro j _hj
      exact riemannianTwoJacobian_nonneg I
        (givensMetricFourierMap boundary N j) (A.parametrization i z)
  have htarget :=
    ae_le_one_riemannianChartAreaMeasure_of_ae_le_one_comp
      I (A.parametrization i) (A.piece I i) q hF hq hsource
  filter_upwards [htarget] with x hx
  apply ENNReal.ofReal_le_one.mp
  rw [ENNReal.ofReal_sum_of_nonneg]
  · simpa only [q] using hx
  · intro j _hj
    exact riemannianTwoJacobian_nonneg I
      (givensMetricFourierMap boundary N j) x

/-- The mixed finite-family unit Jacobian budget for canonical Riemannian
surface area. -/
theorem ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one_surfaceArea
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
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    ∀ᵐ x ∂riemannianSurfaceAreaMeasure I,
      (∑ j : Fin N, riemannianTwoJacobian I
        (givensMetricFourierMap boundary N j) x) ≤ 1 := by
  let A : ControlledInteriorAtlas I M :=
    Classical.choice (inferInstance : Nonempty (ControlledInteriorAtlas I M))
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  unfold ControlledInteriorAtlas.areaMeasure riemannianAtlasAreaMeasure
  exact Measure.ae_sum_iff.2 fun i ↦
    A.ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one_chartArea
      I hboundary N i

/-- Integrated canonical-area form of the finite mixed Fourier Jacobian
budget. -/
theorem sum_lintegral_riemannianTwoJacobian_givensMetricFourierMap_le_surfaceArea
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
    (hboundary : IsometricCircleBoundary boundary) (N : ℕ) :
    (∑ j : Fin N, ∫⁻ x,
      ENNReal.ofReal (riemannianTwoJacobian I
        (givensMetricFourierMap boundary N j) x)
        ∂riemannianSurfaceAreaMeasure I) ≤
      riemannianSurfaceAreaMeasure I (Set.univ : Set M) := by
  exact sum_lintegral_riemannianTwoJacobian_le_surfaceAreaMeasure I
    (fun j : Fin N ↦ givensMetricFourierMap boundary N j)
    (fun j : Fin N ↦ mixedOddProfileFourierLipschitzConstant N j)
    (fun j ↦ givensMetricFourierMap_lipschitzWith hboundary N j)
    (ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one_surfaceArea
      I hboundary N)

end

end GromovFilling

#print axioms GromovFilling.ControlledInteriorAtlas.ae_ae_mdifferentiableAt_oddDistanceProfile
#print axioms GromovFilling.sum_riemannianComplexDerivativeEnergy_givensMetricFourierMap
#print axioms GromovFilling.sum_riemannianTwoJacobian_givensMetricFourierMap_le_one
#print axioms GromovFilling.ae_sum_riemannianTwoJacobian_givensMetricFourierMap_le_one_surfaceArea
#print axioms GromovFilling.sum_lintegral_riemannianTwoJacobian_givensMetricFourierMap_le_surfaceArea
