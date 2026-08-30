import GromovFilling.OrientedFiniteResonantComassLimit

/-!
# A uniform envelope for finite resonant densities

The sharp comass estimate is obtained only after passing from finite odd-mode
truncations to the coherent infinite Fourier field.  Dominated convergence
therefore also needs a bound on every finite truncation which is uniform in
the truncation index.  This file supplies that envelope directly from the
finite energy of the resonant tangent map.
-/

open Bundle Filter Manifold MeasureTheory Set
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal Topology

namespace GromovFilling

noncomputable section

/-- A truncation-independent envelope for the finite resonant symplectic
density.  It is deliberately crude; its role is domination, not the sharp
comass estimate. -/
def finiteResonantUniformDensityBound (lam : ℝ) : ℝ :=
  (1 + |lam| * Real.sqrt Qstar) ^ 2

private lemma Qstar_nonneg_for_uniformDensityBound : 0 ≤ Qstar := by
  unfold Qstar
  positivity

theorem finiteResonantUniformDensityBound_nonneg (lam : ℝ) :
    0 ≤ finiteResonantUniformDensityBound lam := by
  unfold finiteResonantUniformDensityBound
  positivity

private lemma sqrt_mul_sqrt_le_average_uniform
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt A * Real.sqrt B ≤ (A + B) / 2 := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]

/-- The finite resonant tangent map has a uniform squared-energy operator
bound once the profile resonance coefficient is bounded by `Qstar`. -/
private theorem finiteComplexEnergy_finiteResonantTangentMap_le_uniform
    {N : ℕ} (lam : ℝ) (a : ℂ) (y : Fin N → ℂ)
    (p : Fin (N + 1) → ℂ)
    (hcoefficient :
      ‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y ≤ Qstar) :
    finiteComplexEnergy (finiteResonantTangentMap lam a y p) ≤
      finiteResonantUniformDensityBound lam * finiteComplexEnergy p := by
  let pHead : Fin N → ℂ := fun k ↦ p k.castSucc
  let r : Fin N → ℂ := resonantDifferentialVariation a y p
  have hp0 : 0 ≤ finiteComplexEnergy p := finiteComplexEnergy_nonneg p
  have hpHeadLe : finiteComplexEnergy pHead ≤ finiteComplexEnergy p := by
    simpa only [pHead] using finiteComplexEnergy_castSucc_le p
  have hpHeadSqrt : Real.sqrt (finiteComplexEnergy pHead) ≤
      Real.sqrt (finiteComplexEnergy p) :=
    Real.sqrt_le_sqrt hpHeadLe
  have hr0 : 0 ≤ finiteComplexEnergy r := finiteComplexEnergy_nonneg r
  have hr : finiteComplexEnergy r ≤
      Qstar * finiteComplexEnergy p := by
    calc
      finiteComplexEnergy r ≤
          (‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy y) *
            finiteComplexEnergy p := by
        simpa only [r] using
          finiteComplexEnergy_resonantDifferentialVariation_le a y p
      _ ≤ Qstar * finiteComplexEnergy p := by
        exact mul_le_mul_of_nonneg_right hcoefficient hp0
  have hsqrt : Real.sqrt (finiteComplexEnergy r) ≤
      Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p) := by
    calc
      Real.sqrt (finiteComplexEnergy r) ≤
          Real.sqrt (Qstar * finiteComplexEnergy p) :=
        Real.sqrt_le_sqrt hr
      _ = Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p) := by
        rw [Real.sqrt_mul Qstar_nonneg_for_uniformDensityBound]
  have hadd : finiteComplexEnergy
      (fun k ↦ pHead k + (lam : ℂ) * r k) ≤
        (Real.sqrt (finiteComplexEnergy pHead) +
          ‖(lam : ℂ)‖ * Real.sqrt (finiteComplexEnergy r)) ^ 2 := by
    simpa only [sqrt_finiteComplexEnergy_const_mul] using
      finiteComplexEnergy_add_le pHead (fun k ↦ (lam : ℂ) * r k)
  have hsum :
      Real.sqrt (finiteComplexEnergy pHead) +
          ‖(lam : ℂ)‖ * Real.sqrt (finiteComplexEnergy r) ≤
        Real.sqrt (finiteComplexEnergy p) +
          |lam| *
            (Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p)) := by
    calc
      Real.sqrt (finiteComplexEnergy pHead) +
          ‖(lam : ℂ)‖ * Real.sqrt (finiteComplexEnergy r) ≤
        Real.sqrt (finiteComplexEnergy p) +
          ‖(lam : ℂ)‖ *
            (Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p)) :=
        add_le_add hpHeadSqrt
          (mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _))
      _ = Real.sqrt (finiteComplexEnergy p) +
          |lam| *
            (Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p)) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    finiteComplexEnergy (finiteResonantTangentMap lam a y p) =
        finiteComplexEnergy
          (fun k ↦ pHead k + (lam : ℂ) * r k) := by
      rfl
    _ ≤ (Real.sqrt (finiteComplexEnergy pHead) +
          ‖(lam : ℂ)‖ * Real.sqrt (finiteComplexEnergy r)) ^ 2 := hadd
    _ ≤ (Real.sqrt (finiteComplexEnergy p) +
          |lam| *
            (Real.sqrt Qstar * Real.sqrt (finiteComplexEnergy p))) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
    _ = (1 + |lam| * Real.sqrt Qstar) ^ 2 *
          (Real.sqrt (finiteComplexEnergy p)) ^ 2 := by ring
    _ = finiteResonantUniformDensityBound lam * finiteComplexEnergy p := by
      rw [Real.sq_sqrt hp0]
      rfl

/-- Every coherent finite resonant truncation is bounded by one scalar
envelope independent of the truncation index. -/
theorem abs_finiteTruncationResonantDensity_le_uniform
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))))
    (hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    |finiteTruncationResonantDensity lam a y c N| ≤
      finiteResonantUniformDensityBound lam := by
  let cPos : Fin (N + 1) → ℂ := fun k ↦ c (oddMode k : ℤ)
  let cNeg : Fin (N + 1) → ℂ := fun k ↦ c (-(oddMode k : ℤ))
  let p : Fin (N + 1) → ℂ := finiteFourierTangentVector cPos cNeg
  let q : Fin (N + 1) → ℂ := finiteFourierQuarterTurnVector cPos cNeg
  let yN : Fin N → ℂ := fun k ↦ y k
  have hposPrefix : finiteComplexEnergy cPos ≤
      infinitePositiveOddEnergy c :=
    finiteComplexEnergy_truncation_le_infiniteComplexEnergy
      (fun k ↦ c (oddMode k : ℤ)) hpos (N + 1)
  have hnegPrefix : finiteComplexEnergy cNeg ≤
      infiniteNegativeOddEnergy c :=
    finiteComplexEnergy_truncation_le_infiniteComplexEnergy
      (fun k ↦ c (-(oddMode k : ℤ))) hneg (N + 1)
  have hcoeffPrefix :
      finiteComplexEnergy cPos + finiteComplexEnergy cNeg ≤ 1 :=
    (add_le_add hposPrefix hnegPrefix).trans hcoeff
  have hpqIdentity :
      finiteComplexEnergy p + finiteComplexEnergy q =
        2 * (finiteComplexEnergy cPos + finiteComplexEnergy cNeg) := by
    simpa only [p, q] using finiteFourier_pair_energy cPos cNeg
  have hpq : finiteComplexEnergy p + finiteComplexEnergy q ≤ 2 := by
    rw [hpqIdentity]
    linarith
  have hyPrefix : finiteComplexEnergy yN ≤ infiniteComplexEnergy y :=
    finiteComplexEnergy_truncation_le_infiniteComplexEnergy y hy N
  have hprofilePrefix :
      ‖a‖ ^ 2 + 9 * finiteComplexEnergy yN ≤ 2 :=
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hyPrefix (by norm_num))).trans hprofile
  have hySqrt := Real.sq_sqrt (finiteComplexEnergy_nonneg yN)
  have hcoefficient :
      ‖a‖ ^ 4 + 4 * ‖a‖ ^ 2 * finiteComplexEnergy yN ≤ Qstar := by
    have h := resonance_coefficient_le_Qstar
      ‖a‖ (Real.sqrt (finiteComplexEnergy yN)) (norm_nonneg a)
      (by simpa only [hySqrt] using hprofilePrefix) hapi
    simpa only [hySqrt] using h
  have hpMap := finiteComplexEnergy_finiteResonantTangentMap_le_uniform
    lam a yN p hcoefficient
  have hqMap := finiteComplexEnergy_finiteResonantTangentMap_le_uniform
    lam a yN q hcoefficient
  have hdensity : finiteTruncationResonantDensity lam a y c N =
      standardComplexSymplectic
        (finiteResonantTangentMap lam a yN p)
        (finiteResonantTangentMap lam a yN q) := by
    simpa only [finiteTruncationResonantDensity,
      finiteTruncationOddBaseDensity,
      finiteTruncationResonantFirstVariation,
      finiteTruncationResonantQuadraticVariation,
      cPos, cNeg, p, q, yN] using
        (finiteResonant_symplectic_expansion lam a yN p q).symm
  rw [hdensity]
  calc
    |standardComplexSymplectic
        (finiteResonantTangentMap lam a yN p)
        (finiteResonantTangentMap lam a yN q)| ≤
      Real.sqrt (finiteComplexEnergy
          (finiteResonantTangentMap lam a yN p)) *
        Real.sqrt (finiteComplexEnergy
          (finiteResonantTangentMap lam a yN q)) :=
      abs_standardComplexSymplectic_le_sqrt_finiteComplexEnergy _ _
    _ ≤ (finiteComplexEnergy (finiteResonantTangentMap lam a yN p) +
          finiteComplexEnergy (finiteResonantTangentMap lam a yN q)) / 2 :=
      sqrt_mul_sqrt_le_average_uniform _ _
        (finiteComplexEnergy_nonneg _)
        (finiteComplexEnergy_nonneg _)
    _ ≤ (finiteResonantUniformDensityBound lam * finiteComplexEnergy p +
          finiteResonantUniformDensityBound lam * finiteComplexEnergy q) / 2 := by
      have := add_le_add hpMap hqMap
      linarith
    _ = finiteResonantUniformDensityBound lam *
          (finiteComplexEnergy p + finiteComplexEnergy q) / 2 := by ring
    _ ≤ finiteResonantUniformDensityBound lam * 2 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hpq
        (finiteResonantUniformDensityBound_nonneg lam)
      linarith
    _ = finiteResonantUniformDensityBound lam := by ring

/-- Fourier-coefficient specialization of the uniform finite-truncation
envelope. -/
theorem abs_finiteTruncationResonantDensity_fourierCoeffOn_le_uniform
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (N : ℕ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    |finiteTruncationResonantDensity lam a y c N| ≤
      finiteResonantUniformDensityBound lam := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  have hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1 := by
    simpa only [c] using
      infiniteOddEnergies_fourierCoeffOn_le_one f hf hanti hunit
  exact abs_finiteTruncationResonantDensity_le_uniform
    lam a y c N hy (by simpa only [c] using hpos)
      (by simpa only [c] using hneg) hcoeff hprofile hapi

/-- At every regular interior tangent plane, all intrinsic oriented finite
resonant densities obey the same truncation-independent envelope. -/
theorem abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
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
        (oddProfileFourierMap boundary (oddMode k)) x)
    (N : ℕ) :
    |orientedFiniteResonantRiemannianSymplecticDensity
        I o boundary N lam x| ≤ finiteResonantUniformDensityBound lam := by
  let e := o.positiveOrthonormalBasis I x
  obtain ⟨f, hf, hanti, hunit, heq, _herror, _hbound⟩ :=
    exists_coherentProfile_finiteResonantRiemannian_comass_limit
      I hboundary lam hlam0 hlam x hx e hprofileDiff hFourierDiff
  rw [abs_orientedFiniteResonantRiemannianSymplecticDensity_eq_frame
    I o boundary N lam x e, heq N]
  exact abs_finiteTruncationResonantDensity_fourierCoeffOn_le_uniform
    lam (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      f N
      (summable_normSq_oddProfileFourierMap_tail hboundary x)
      hf hanti hunit
      (oddProfileFourierMap_first_add_nine_infiniteTailEnergy_le_two
        hboundary x)
      (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)

end

end GromovFilling

#print axioms GromovFilling.finiteResonantUniformDensityBound
#print axioms GromovFilling.finiteResonantUniformDensityBound_nonneg
#print axioms
  GromovFilling.abs_finiteTruncationResonantDensity_le_uniform
#print axioms
  GromovFilling.abs_finiteTruncationResonantDensity_fourierCoeffOn_le_uniform
#print axioms
  GromovFilling.abs_orientedFiniteResonantRiemannianSymplecticDensity_le_uniform
