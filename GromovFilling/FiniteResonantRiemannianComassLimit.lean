import GromovFilling.FiniteResonantRiemannian
import GromovFilling.InfiniteResonantComassLimit

/-!
# Genuine Riemannian finite-to-infinite comass bridge

This module identifies every finite pulled-back resonant symplectic density
at one regular oriented tangent plane with the corresponding truncation of a
single, coherent Fourier field.  The sharp infinite comass estimate then
controls all truncations up to one explicit base/first-variation error, and
that error tends to zero.
-/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The exact finite Riemannian expansion agrees definitionally with the
finite truncation package once its two genuine derivative columns have been
identified with the positive/negative Fourier columns. -/
theorem finiteResonantRiemannianSymplecticDensity_eq_finiteTruncation
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (lam : ℝ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x)
    (c : ℤ → ℂ)
    (hcolumn₀ :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0) =
        finiteFourierTangentVector
          (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
          (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))))
    (hcolumn₁ :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1) =
        finiteFourierQuarterTurnVector
          (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
          (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ)))) :
    finiteResonantRiemannianSymplecticDensity
        I boundary N lam x e =
      finiteTruncationResonantDensity lam
        (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
        c N := by
  rw [finiteResonantRiemannianSymplecticDensity_eq_expansion
      I N lam x hx e hdiff,
    hcolumn₀, hcolumn₁]
  rfl

/-- One pair of measurable tangent-profile fields reconstructs every odd
Fourier derivative at the point, rather than choosing new fields separately
for each truncation. -/
theorem exists_orientedRiemannianProfileFourierData_all
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : ℕ,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    ∃ d₀ d₁ : ℝ → ℝ,
      Measurable d₀ ∧ Measurable d₁ ∧
      MemLp (fun t ↦ (d₀ t : ℂ)) 2
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) ∧
      MemLp (fun t ↦ (d₁ t : ℂ)) 2
        (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) ∧
      Function.Antiperiodic d₀ Real.pi ∧
      Function.Antiperiodic d₁ Real.pi ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
        ‖(d₀ t : ℂ)‖ ^ 2 + ‖(d₁ t : ℂ)‖ ^ 2 ≤ 1) ∧
      (∀ k : ℕ,
        riemannianComplexMFDeriv I
            (oddProfileFourierMap boundary (oddMode k)) x (e 0) =
          2 * fourierCoeffOn
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
            (fun t ↦ (d₀ t : ℂ)) (-(oddMode k : ℤ))) ∧
      (∀ k : ℕ,
        riemannianComplexMFDeriv I
            (oddProfileFourierMap boundary (oddMode k)) x (e 1) =
          2 * fourierCoeffOn
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
            (fun t ↦ (d₁ t : ℂ)) (-(oddMode k : ℤ))) := by
  obtain ⟨d₀, hd₀meas, hd₀eq, hd₀weighted, hd₀anti⟩ :=
    exists_tangentProfileDerivativeField I hboundary x hx (e 0) hprofileDiff
  obtain ⟨d₁, hd₁meas, hd₁eq, hd₁weighted, hd₁anti⟩ :=
    exists_tangentProfileDerivativeField I hboundary x hx (e 1) hprofileDiff
  have hd₀bound : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi), ‖(d₀ t : ℂ)‖ ≤ 1 := by
    filter_upwards [hd₀eq, hprofileDiff] with t hdeq htdiff
    rw [hdeq, Complex.norm_real]
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
  have hd₁bound : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi), ‖(d₁ t : ℂ)‖ ≤ 1 := by
    filter_upwards [hd₁eq, hprofileDiff] with t hdeq htdiff
    rw [hdeq, Complex.norm_real]
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
  have hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hd₀meas).aestronglyMeasurable
      1 hd₀bound
  have hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    MemLp.of_bound
      (Complex.continuous_ofReal.measurable.comp hd₁meas).aestronglyMeasurable
      1 hd₁bound
  have hjoint : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      ‖(d₀ t : ℂ)‖ ^ 2 + ‖(d₁ t : ℂ)‖ ^ 2 ≤ 1 := by
    filter_upwards [hd₀eq, hd₁eq, hprofileDiff] with t hd₀t hd₁t htdiff
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
    simpa [hd₀t, hd₁t, D, Complex.norm_real, sq_abs] using hDbudget
  have hcolumn₀ (k : ℕ) :
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 0) =
        2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d₀ t : ℂ)) (-(oddMode k : ℤ)) :=
    riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
      I (oddMode k) x hx (e 0) d₀ hd₀L2 hd₀weighted (hFourierDiff k)
  have hcolumn₁ (k : ℕ) :
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 1) =
        2 * fourierCoeffOn
          (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
          (fun t ↦ (d₁ t : ℂ)) (-(oddMode k : ℤ)) :=
    riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
      I (oddMode k) x hx (e 1) d₁ hd₁L2 hd₁weighted (hFourierDiff k)
  exact ⟨d₀, d₁, hd₀meas, hd₁meas, hd₀L2, hd₁L2,
    hd₀anti, hd₁anti, hjoint, hcolumn₀, hcolumn₁⟩

/-- At every regular oriented tangent plane, all genuine finite resonant
densities come from one coherent antiperiodic Fourier field.  They satisfy
the sharp infinite comass bound up to a single explicit error sequence which
tends to zero. -/
theorem exists_coherentProfile_finiteResonantRiemannian_comass_limit
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : ℕ,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    ∃ f : ℝ → ℂ,
      MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) ∧
      Function.Antiperiodic f Real.pi ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (-Real.pi) Real.pi),
        Complex.normSq (f t) ≤ 1) ∧
      (∀ N : ℕ,
        finiteResonantRiemannianSymplecticDensity
            I boundary N lam x e =
          finiteTruncationResonantDensity lam
            (oddProfileFourierMap boundary (oddMode 0) x)
            (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
            (fun n ↦ fourierCoeffOn
              (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) N) ∧
      Tendsto
        (finiteTruncationResonantBaseFirstError lam
          (oddProfileFourierMap boundary (oddMode 0) x)
          (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
          (fun n ↦ fourierCoeffOn
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n))
        atTop (nhds 0) ∧
      (∀ N : ℕ,
        |finiteResonantRiemannianSymplecticDensity
            I boundary N lam x e| ≤
          comassBound lam +
            |finiteTruncationResonantBaseFirstError lam
              (oddProfileFourierMap boundary (oddMode 0) x)
              (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
              (fun n ↦ fourierCoeffOn
                (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n) N|) := by
  obtain ⟨d₀, d₁, _hd₀meas, _hd₁meas, hd₀L2, hd₁L2,
      hd₀anti, hd₁anti, hjoint, hderiv₀, hderiv₁⟩ :=
    exists_orientedRiemannianProfileFourierData_all
      I hboundary x hx e hprofileDiff hFourierDiff
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let f : ℝ → ℂ := complexTangentProfileField d₀ d₁
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  have hf : MemLp f 2
      (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) := by
    simpa [f, complexTangentProfileField] using
      hd₀L2.add (hd₁L2.const_mul Complex.I)
  have hanti : Function.Antiperiodic f Real.pi := by
    simpa [f] using
      complexTangentProfileField_antiperiodic hd₀anti hd₁anti
  have hunit : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi), Complex.normSq (f t) ≤ 1 := by
    filter_upwards [hjoint] with t ht
    simpa [f, complexTangentProfileField, Complex.normSq_apply,
      Complex.norm_real, sq_abs, pow_two] using ht
  have hcPos (N : ℕ) :
      (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ)) =
        fun k : Fin (N + 1) ↦
          positiveOddTangentProfileCoefficient hab d₀ d₁ k := by
    funext k
    exact (positiveOddTangentProfileCoefficient_eq_fourierCoeffOn
      hab d₀ d₁ hd₀L2 hd₁L2 k).symm
  have hcNeg (N : ℕ) :
      (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))) =
        fun k : Fin (N + 1) ↦
          negativeOddTangentProfileCoefficient hab d₀ d₁ k := by
    funext k
    exact (negativeOddTangentProfileCoefficient_eq_fourierCoeffOn
      hab d₀ d₁ hd₀L2 hd₁L2 k).symm
  have hcolumn₀ (N : ℕ) :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0) =
        finiteFourierTangentVector
          (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
          (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))) := by
    funext k
    change riemannianComplexMFDeriv I
        (oddProfileFourierMap boundary (oddMode k)) x (e 0) = _
    rw [hderiv₀ k, hcPos N, hcNeg N]
    exact (finiteFourierTangentVector_profileCoefficients hab d₀ d₁ k).symm
  have hcolumn₁ (N : ℕ) :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1) =
        finiteFourierQuarterTurnVector
          (fun k : Fin (N + 1) ↦ c (oddMode k : ℤ))
          (fun k : Fin (N + 1) ↦ c (-(oddMode k : ℤ))) := by
    funext k
    change riemannianComplexMFDeriv I
        (oddProfileFourierMap boundary (oddMode k)) x (e 1) = _
    rw [hderiv₁ k, hcPos N, hcNeg N]
    exact (finiteFourierQuarterTurnVector_profileCoefficients hab d₀ d₁ k).symm
  have heq (N : ℕ) :
      finiteResonantRiemannianSymplecticDensity
          I boundary N lam x e =
        finiteTruncationResonantDensity lam
          (oddProfileFourierMap boundary (oddMode 0) x)
          (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
          c N :=
    finiteResonantRiemannianSymplecticDensity_eq_finiteTruncation
      I N lam x hx e (fun k ↦ hFourierDiff k) c
      (hcolumn₀ N) (hcolumn₁ N)
  have hy : Summable (fun n : ℕ ↦ Complex.normSq
      (oddProfileFourierMap boundary (oddMode n.succ) x)) :=
    summable_normSq_oddProfileFourierMap_tail hboundary x
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  have herror : Tendsto
      (finiteTruncationResonantBaseFirstError lam
        (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x) c)
      atTop (nhds 0) :=
    tendsto_finiteTruncationResonantBaseFirstError
      lam (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      c hy (by simpa [c] using hpos) (by simpa [c] using hneg)
  have hbound (N : ℕ) :
      |finiteResonantRiemannianSymplecticDensity
          I boundary N lam x e| ≤
        comassBound lam +
          |finiteTruncationResonantBaseFirstError lam
            (oddProfileFourierMap boundary (oddMode 0) x)
            (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
            c N| := by
    rw [heq N]
    exact abs_finiteTruncationResonantDensity_fourierCoeffOn_le_comassBound_add_error
      lam (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      f N hlam0 hlam hy hf hanti hunit
      (oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
        hboundary x)
      (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)
  refine ⟨f, hf, hanti, hunit, ?_, ?_, ?_⟩
  · intro N
    simpa [c] using heq N
  · simpa [c] using herror
  · intro N
    simpa [c] using hbound N

end

end GromovFilling

#print axioms
  GromovFilling.finiteResonantRiemannianSymplecticDensity_eq_finiteTruncation
#print axioms GromovFilling.exists_orientedRiemannianProfileFourierData_all
#print axioms
  GromovFilling.exists_coherentProfile_finiteResonantRiemannian_comass_limit
