import GromovFilling.NonlinearCorrelationBounds
import GromovFilling.RiemannianProfileFourierEnergy

/-!
# Distance-profile Fourier data for the nonlinear deformation

This file connects the intrinsic derivative fields of the odd distance
profile to the positive- and negative-frequency variables used by the finite
nonlinear symplectic calculus.  The construction keeps both real tangent
columns visible.  Their joint pointwise unit bound yields the exact finite
coefficient-energy budget, while conjugate symmetry reconstructs the two
oriented tangent columns with the manuscript's signs.

The shift-correlation limit and global Stokes argument remain separate.  In
particular, no finite truncation is identified with the full infinite
shift-two correlation in this module.
-/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The complex tangent-profile field associated with an oriented orthonormal
pair of real tangent directions. -/
def complexTangentProfileField (d₀ d₁ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (d₀ t : ℂ) + Complex.I * (d₁ t : ℂ)

/-- Fourier coefficients distribute over the two real columns of the complex
tangent-profile field. -/
theorem fourierCoeffOn_complexTangentProfileField
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b))) (n : ℤ) :
    fourierCoeffOn hab (complexTangentProfileField d₀ d₁) n =
      fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ)) n +
        Complex.I * fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ)) n := by
  letI : Fact (0 < b - a) := ⟨by linarith⟩
  have hd₀L2' := hd₀L2
  have hd₁L2' := hd₁L2
  rw [← add_sub_cancel a b] at hd₀L2' hd₁L2'
  have hd₀Int : Integrable
      (AddCircle.liftIoc (b - a) a (fun t ↦ (d₀ t : ℂ)))
      AddCircle.haarAddCircle :=
    hd₀L2'.memLp_liftIoc.haarAddCircle.integrable (by norm_num)
  have hd₁Int : Integrable
      (AddCircle.liftIoc (b - a) a (fun t ↦ (d₁ t : ℂ)))
      AddCircle.haarAddCircle :=
    hd₁L2'.memLp_liftIoc.haarAddCircle.integrable (by norm_num)
  unfold fourierCoeffOn
  have hlift :
      AddCircle.liftIoc (b - a) a (complexTangentProfileField d₀ d₁) =
        AddCircle.liftIoc (b - a) a (fun t ↦ (d₀ t : ℂ)) +
          Complex.I • AddCircle.liftIoc (b - a) a
            (fun t ↦ (d₁ t : ℂ)) := by
    funext t
    rfl
  have hd₁SmulInt : Integrable
      (Complex.I • AddCircle.liftIoc (b - a) a
        (fun t ↦ (d₁ t : ℂ))) AddCircle.haarAddCircle := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      hd₁Int.const_mul Complex.I
  rw [hlift, fourierCoeff.add hd₀Int hd₁SmulInt]
  simp only [Pi.add_apply]
  rw [fourierCoeff.const_smul]
  rfl

/-- The positive odd coefficient assembled from the two real tangent-profile
fields.  Conjugate symmetry identifies this expression with the positive
Fourier coefficient of `d₀ + i d₁`. -/
def positiveOddTangentProfileCoefficient
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ) (k : ℕ) : ℂ :=
  star (fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ)) (-(oddMode k : ℤ))) +
    Complex.I *
      star (fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ)) (-(oddMode k : ℤ)))

/-- The negative odd coefficient assembled from the same two real
tangent-profile fields. -/
def negativeOddTangentProfileCoefficient
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ) (k : ℕ) : ℂ :=
  fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ)) (-(oddMode k : ℤ)) +
    Complex.I * fourierCoeffOn hab
      (fun t ↦ (d₁ t : ℂ)) (-(oddMode k : ℤ))

/-- The assembled positive variable is the actual positive odd Fourier
coefficient of the complex tangent-profile field. -/
theorem positiveOddTangentProfileCoefficient_eq_fourierCoeffOn
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b))) (k : ℕ) :
    positiveOddTangentProfileCoefficient hab d₀ d₁ k =
      fourierCoeffOn hab (complexTangentProfileField d₀ d₁)
        (oddMode k : ℤ) := by
  rw [fourierCoeffOn_complexTangentProfileField hab d₀ d₁
    hd₀L2 hd₁L2]
  have hd₀sym := fourierCoeffOn_neg_eq_conj_of_real
    hab d₀ (-(oddMode k : ℤ))
  have hd₁sym := fourierCoeffOn_neg_eq_conj_of_real
    hab d₁ (-(oddMode k : ℤ))
  simp only [neg_neg] at hd₀sym hd₁sym
  rw [hd₀sym, hd₁sym]
  simp [positiveOddTangentProfileCoefficient]

/-- The assembled negative variable is the actual negative odd Fourier
coefficient of the complex tangent-profile field. -/
theorem negativeOddTangentProfileCoefficient_eq_fourierCoeffOn
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b))) (k : ℕ) :
    negativeOddTangentProfileCoefficient hab d₀ d₁ k =
      fourierCoeffOn hab (complexTangentProfileField d₀ d₁)
        (-(oddMode k : ℤ)) := by
  rw [fourierCoeffOn_complexTangentProfileField hab d₀ d₁
    hd₀L2 hd₁L2]
  rfl

/-- The real tangent column is exactly reconstructed from the positive and
negative odd profile coefficients. -/
theorem finiteFourierTangentVector_profileCoefficients
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ) {N : ℕ}
    (k : Fin (N + 1)) :
    finiteFourierTangentVector
        (fun j : Fin (N + 1) ↦
          positiveOddTangentProfileCoefficient hab d₀ d₁ j)
        (fun j : Fin (N + 1) ↦
          negativeOddTangentProfileCoefficient hab d₀ d₁ j) k =
      2 * fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ))
        (-(oddMode k : ℤ)) := by
  simp [finiteFourierTangentVector,
    positiveOddTangentProfileCoefficient,
    negativeOddTangentProfileCoefficient]
  ring

/-- The quarter-turned tangent column has the corresponding exact
reconstruction formula. -/
theorem finiteFourierQuarterTurnVector_profileCoefficients
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ) {N : ℕ}
    (k : Fin (N + 1)) :
    finiteFourierQuarterTurnVector
        (fun j : Fin (N + 1) ↦
          positiveOddTangentProfileCoefficient hab d₀ d₁ j)
        (fun j : Fin (N + 1) ↦
          negativeOddTangentProfileCoefficient hab d₀ d₁ j) k =
      2 * fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ))
        (-(oddMode k : ℤ)) := by
  simp [finiteFourierQuarterTurnVector,
    positiveOddTangentProfileCoefficient,
    negativeOddTangentProfileCoefficient]
  let B : ℂ := fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ))
    (-(oddMode k : ℤ))
  change Complex.I * (-(Complex.I * B) - Complex.I * B) = 2 * B
  calc
    Complex.I * (-(Complex.I * B) - Complex.I * B) =
        -(2 : ℂ) * (Complex.I * Complex.I) * B := by ring
    _ = 2 * B := by rw [Complex.I_mul_I]; ring

private lemma normSq_positive_add_negative_profileCoefficient
    (a b : ℂ) :
    Complex.normSq (star a + Complex.I * star b) +
        Complex.normSq (a + Complex.I * b) =
      2 * (Complex.normSq a + Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The combined positive/negative finite energy is twice the energy of the
two negative real-field coefficient families. -/
theorem finiteComplexEnergy_profileCoefficients
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ) (N : ℕ) :
    finiteComplexEnergy
          (fun k : Fin N ↦
            positiveOddTangentProfileCoefficient hab d₀ d₁ k) +
        finiteComplexEnergy
          (fun k : Fin N ↦
            negativeOddTangentProfileCoefficient hab d₀ d₁ k) =
      2 *
        ((∑ k : Fin N,
            Complex.normSq
              (fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ))
                (-(oddMode k : ℤ)))) +
          ∑ k : Fin N,
            Complex.normSq
              (fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ))
                (-(oddMode k : ℤ)))) := by
  unfold finiteComplexEnergy
  rw [← Finset.sum_add_distrib]
  simp_rw [positiveOddTangentProfileCoefficient,
    negativeOddTangentProfileCoefficient,
    normSq_positive_add_negative_profileCoefficient]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Finite Bessel and the normalized joint `L²` bound give the exact unit
energy hypothesis used by the nonlinear correlation estimates. -/
theorem finiteComplexEnergy_profileCoefficients_le_one
    {a b : ℝ} (hab : a < b) (d₀ d₁ : ℝ → ℝ)
    (hd₀L2 : MemLp (fun t ↦ (d₀ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b)))
    (hd₁L2 : MemLp (fun t ↦ (d₁ t : ℂ)) 2
      (volume.restrict (Set.Ioc a b)))
    (hjoint :
      (b - a)⁻¹ * (∫ t in a..b, ‖(d₀ t : ℂ)‖ ^ 2) +
        (b - a)⁻¹ * (∫ t in a..b, ‖(d₁ t : ℂ)‖ ^ 2) ≤ 1)
    (N : ℕ) :
    finiteComplexEnergy
          (fun k : Fin N ↦
            positiveOddTangentProfileCoefficient hab d₀ d₁ k) +
        finiteComplexEnergy
          (fun k : Fin N ↦
            negativeOddTangentProfileCoefficient hab d₀ d₁ k) ≤ 1 := by
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
  have hd₀ := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab d₀ hd₀L2 (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  have hd₁ := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab d₁ hd₁L2 (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  simp only [smul_eq_mul] at hd₀ hd₁
  rw [finiteComplexEnergy_profileCoefficients]
  simp_rw [← Complex.sq_norm]
  calc
    2 *
        ((∑ k : Fin N,
            ‖fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ))
              (-(oddMode k : ℤ))‖ ^ 2) +
          ∑ k : Fin N,
            ‖fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ))
              (-(oddMode k : ℤ))‖ ^ 2) =
        2 * (∑ k : Fin N,
            ‖fourierCoeffOn hab (fun t ↦ (d₀ t : ℂ))
              (-(oddMode k : ℤ))‖ ^ 2) +
          2 * (∑ k : Fin N,
            ‖fourierCoeffOn hab (fun t ↦ (d₁ t : ℂ))
              (-(oddMode k : ℤ))‖ ^ 2) := by ring
    _ ≤
        (b - a)⁻¹ * (∫ t in a..b, ‖(d₀ t : ℂ)‖ ^ 2) +
          (b - a)⁻¹ * (∫ t in a..b, ‖(d₁ t : ℂ)‖ ^ 2) :=
      by simpa only [] using add_le_add hd₀ hd₁
    _ ≤ 1 := hjoint

/-- At every regular oriented Riemannian tangent plane, the actual
distance-profile Fourier derivatives have positive/negative coefficient
data which reconstruct both tangent columns and have total finite energy at
most one.  The returned real fields are measurable, square-integrable,
pointwise jointly bounded, and anti-periodic. -/
theorem exists_orientedRiemannianProfileFourierData
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
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : Fin (N + 1),
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
      finiteComplexEnergy
          (fun k : Fin (N + 1) ↦ positiveOddTangentProfileCoefficient
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ k) +
        finiteComplexEnergy
          (fun k : Fin (N + 1) ↦ negativeOddTangentProfileCoefficient
            (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ k) ≤ 1 ∧
      (∀ k : Fin (N + 1),
        riemannianComplexMFDeriv I
            (oddProfileFourierMap boundary (oddMode k)) x (e 0) =
          finiteFourierTangentVector
            (fun j : Fin (N + 1) ↦ positiveOddTangentProfileCoefficient
              (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ j)
            (fun j : Fin (N + 1) ↦ negativeOddTangentProfileCoefficient
              (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ j) k) ∧
      (∀ k : Fin (N + 1),
        riemannianComplexMFDeriv I
            (oddProfileFourierMap boundary (oddMode k)) x (e 1) =
          finiteFourierQuarterTurnVector
            (fun j : Fin (N + 1) ↦ positiveOddTangentProfileCoefficient
              (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ j)
            (fun j : Fin (N + 1) ↦ negativeOddTangentProfileCoefficient
              (by linarith [Real.pi_pos] : -Real.pi < Real.pi) d₀ d₁ j) k) := by
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
  have hpow₀ : IntervalIntegrable (fun t ↦ ‖(d₀ t : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hd₀L2)
  have hpow₁ : IntervalIntegrable (fun t ↦ ‖(d₁ t : ℂ)‖ ^ 2)
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    simpa [IntegrableOn] using
      (MemLp.integrable_norm_pow'
        (μ := volume.restrict (Set.Ioc (-Real.pi) Real.pi)) hd₁L2)
  have hsumIntegral :
      (∫ t in (-Real.pi)..Real.pi,
          ‖(d₀ t : ℂ)‖ ^ 2 + ‖(d₁ t : ℂ)‖ ^ 2) ≤
        ∫ _t in (-Real.pi)..Real.pi, (1 : ℝ) := by
    have hconst : IntervalIntegrable (fun _t : ℝ ↦ (1 : ℝ)) volume
        (-Real.pi) Real.pi := by
      exact (continuous_const : Continuous (fun _t : ℝ ↦ (1 : ℝ)))
        |>.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
    rw [intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      intervalIntegral.integral_of_le
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact MeasureTheory.integral_mono_ae
      (hpow₀.1.add hpow₁.1) hconst.1 hjoint
  have hsumEnergy :
      (∫ t in (-Real.pi)..Real.pi, ‖(d₀ t : ℂ)‖ ^ 2) +
        (∫ t in (-Real.pi)..Real.pi, ‖(d₁ t : ℂ)‖ ^ 2) ≤
          Real.pi - -Real.pi := by
    rw [intervalIntegral.integral_add hpow₀ hpow₁] at hsumIntegral
    simpa using hsumIntegral
  have hlengthPos : 0 < Real.pi - -Real.pi := by
    linarith [Real.pi_pos]
  have hnormalized :
      (Real.pi - -Real.pi)⁻¹ *
          (∫ t in (-Real.pi)..Real.pi, ‖(d₀ t : ℂ)‖ ^ 2) +
        (Real.pi - -Real.pi)⁻¹ *
          (∫ t in (-Real.pi)..Real.pi, ‖(d₁ t : ℂ)‖ ^ 2) ≤ 1 := by
    have hscaled := mul_le_mul_of_nonneg_left hsumEnergy
      (inv_nonneg.mpr hlengthPos.le)
    have hunit : (Real.pi - -Real.pi)⁻¹ *
        (Real.pi - -Real.pi) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hlengthPos)
    calc
      (Real.pi - -Real.pi)⁻¹ *
            (∫ t in (-Real.pi)..Real.pi, ‖(d₀ t : ℂ)‖ ^ 2) +
          (Real.pi - -Real.pi)⁻¹ *
            (∫ t in (-Real.pi)..Real.pi, ‖(d₁ t : ℂ)‖ ^ 2) =
          (Real.pi - -Real.pi)⁻¹ *
            ((∫ t in (-Real.pi)..Real.pi, ‖(d₀ t : ℂ)‖ ^ 2) +
              ∫ t in (-Real.pi)..Real.pi, ‖(d₁ t : ℂ)‖ ^ 2) := by
        rw [mul_add]
      _ ≤ (Real.pi - -Real.pi)⁻¹ * (Real.pi - -Real.pi) := hscaled
      _ = 1 := hunit
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have henergy := finiteComplexEnergy_profileCoefficients_le_one
    hab d₀ d₁ hd₀L2 hd₁L2 hnormalized (N + 1)
  have hcolumn₀ : ∀ k : Fin (N + 1),
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 0) =
        finiteFourierTangentVector
          (fun j : Fin (N + 1) ↦
            positiveOddTangentProfileCoefficient hab d₀ d₁ j)
          (fun j : Fin (N + 1) ↦
            negativeOddTangentProfileCoefficient hab d₀ d₁ j) k := by
    intro k
    rw [riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
      I (oddMode k) x hx (e 0) d₀ hd₀L2 hd₀weighted (hFourierDiff k)]
    exact (finiteFourierTangentVector_profileCoefficients hab d₀ d₁ k).symm
  have hcolumn₁ : ∀ k : Fin (N + 1),
      riemannianComplexMFDeriv I
          (oddProfileFourierMap boundary (oddMode k)) x (e 1) =
        finiteFourierQuarterTurnVector
          (fun j : Fin (N + 1) ↦
            positiveOddTangentProfileCoefficient hab d₀ d₁ j)
          (fun j : Fin (N + 1) ↦
            negativeOddTangentProfileCoefficient hab d₀ d₁ j) k := by
    intro k
    rw [riemannianComplexMFDeriv_oddProfileFourierMap_apply_eq_two_mul_fourierCoeffOn
      I (oddMode k) x hx (e 1) d₁ hd₁L2 hd₁weighted (hFourierDiff k)]
    exact (finiteFourierQuarterTurnVector_profileCoefficients hab d₀ d₁ k).symm
  exact ⟨d₀, d₁, hd₀meas, hd₁meas, hd₀L2, hd₁L2,
    hd₀anti, hd₁anti, hjoint, henergy, hcolumn₀, hcolumn₁⟩

end

end GromovFilling

#print axioms GromovFilling.finiteFourierTangentVector_profileCoefficients
#print axioms GromovFilling.finiteFourierQuarterTurnVector_profileCoefficients
#print axioms GromovFilling.positiveOddTangentProfileCoefficient_eq_fourierCoeffOn
#print axioms GromovFilling.negativeOddTangentProfileCoefficient_eq_fourierCoeffOn
#print axioms GromovFilling.finiteComplexEnergy_profileCoefficients_le_one
#print axioms GromovFilling.exists_orientedRiemannianProfileFourierData
