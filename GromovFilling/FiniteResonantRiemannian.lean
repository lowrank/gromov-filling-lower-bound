import GromovFilling.FiniteResonantStokes
import GromovFilling.NonlinearCorrelationBounds
import GromovFilling.NonlinearProfileFourierBridge

/-!
# Finite resonant Riemannian derivatives

This file identifies the genuine manifold derivatives of the finite resonant
metric-profile map with the algebraic tangent map used by the nonlinear
comass calculation.  It then records the exact pulled-back symplectic-density
expansion and connects that density to the verified finite comass estimate.

The global weak Stokes theorem and the limiting passage from finite
truncations remain separate obligations.
-/

open Bundle Manifold

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The finite vector of genuine Riemannian derivatives of the metric odd
Fourier coordinates in one tangent direction. -/
def finiteOddProfileRiemannianDerivative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (boundary : UnitAddCircle → M) (N : ℕ) (x : M)
    (v : TangentSpace I x) : Fin N → ℂ :=
  fun k ↦ riemannianComplexMFDeriv I
    (oddProfileFourierMap boundary (oddMode k)) x v

/-- The finite vector of genuine Riemannian derivatives of the resonant
metric-profile output in one tangent direction. -/
def finiteResonantRiemannianDerivative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (boundary : UnitAddCircle → M) (N : ℕ) (lam : ℝ) (x : M)
    (v : TangentSpace I x) : Fin N → ℂ :=
  fun n ↦ riemannianComplexMFDeriv I
    (fun u ↦ finiteResonantProfileMap boundary N lam u n) x v

/-- Every coordinate of the finite resonant metric-profile map is genuinely
manifold-differentiable whenever its finitely many input Fourier coordinates
are. -/
theorem mdifferentiableAt_finiteResonantProfileMap_coordinate
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (lam : ℝ) (x : M)
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x)
    (n : Fin N) :
    MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun u ↦ finiteResonantProfileMap boundary N lam u n) x := by
  let F : Fin (N + 1) → M → ℂ := fun k ↦
    oddProfileFourierMap boundary (oddMode k)
  have hbase : MDifferentiableAt I 𝓘(ℝ, ℂ) (F n.castSucc) x :=
    hdiff n.castSucc
  have hzero : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun u ↦ star (F 0 u)) x := by
    exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).mdifferentiableAt.comp x (hdiff 0)
  have hshift : MDifferentiableAt I 𝓘(ℝ, ℂ) (F n.succ) x :=
    hdiff n.succ
  have hnonlinear : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun u ↦ star (F 0 u) ^ 2 * F n.succ u) x := by
    exact (hzero.pow 2).mul hshift
  have hscaled : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun u ↦ (lam : ℂ) *
        (star (F 0 u) ^ 2 * F n.succ u)) x := by
    exact mdifferentiableAt_const.mul hnonlinear
  simpa [finiteResonantProfileMap, finiteResonantNonlinearMap,
    F, mul_assoc] using hbase.add hscaled

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

/-- The genuine Riemannian derivative of the finite resonant metric-profile
map is exactly its verified algebraic tangent map applied to the genuine
metric Fourier derivative vector. -/
theorem finiteResonantRiemannianDerivative_eq_tangentMap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (lam : ℝ) (x : M) (hx : I.IsInteriorPoint x)
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x)
    (v : TangentSpace I x) :
    finiteResonantRiemannianDerivative I boundary N lam x v =
      finiteResonantTangentMap lam
        (oddProfileFourierMap boundary (oddMode 0) x)
        (fun n : Fin N ↦
          oddProfileFourierMap boundary (oddMode n.succ) x)
        (finiteOddProfileRiemannianDerivative I boundary (N + 1) x v) := by
  let F : Fin (N + 1) → M → ℂ := fun k ↦
    oddProfileFourierMap boundary (oddMode k)
  let γ : ℝ → M := riemannianTangentChartLine I x v
  let D : ℝ →L[ℝ] (Fin (N + 1) → ℂ) :=
    ContinuousLinearMap.pi fun k ↦ fderiv ℝ (F k ∘ γ) 0
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    mdifferentiableAt_riemannianTangentChartLine_zero I x hx v
  have hcurveDiff (k : Fin (N + 1)) :
      DifferentiableAt ℝ (F k ∘ γ) 0 := by
    have hk : MDifferentiableAt I 𝓘(ℝ, ℂ) (F k) (γ 0) := by
      simpa only [γ, riemannianTangentChartLine_zero] using hdiff k
    exact (hk.comp 0 hγ).differentiableAt
  have hprofileCurve : HasFDerivAt
      (fun s : ℝ ↦ fun k : Fin (N + 1) ↦ F k (γ s)) D 0 := by
    rw [hasFDerivAt_pi']
    intro k
    have hk := (hcurveDiff k).hasFDerivAt
    simpa only [D, ContinuousLinearMap.proj_pi, Function.comp_apply] using hk
  have houter := hasFDerivAt_finiteResonantNonlinearMap lam
    (fun k : Fin (N + 1) ↦ F k (γ 0))
  have hcomp := houter.comp 0 hprofileCurve
  funext n
  have hcoord := (ContinuousLinearMap.proj n).hasFDerivAt.comp 0 hcomp
  have hcoord' : HasFDerivAt
      (fun s ↦ finiteResonantNonlinearMap lam
        (fun k : Fin (N + 1) ↦ F k (γ s)) n)
      ((ContinuousLinearMap.proj n).comp
        ((finiteResonantTangentCLM lam
          (F 0 (γ 0)) (fun j ↦ F j.succ (γ 0))).comp D)) 0 := by
    simpa only [Function.comp_apply] using hcoord
  have houtDiff :=
    mdifferentiableAt_finiteResonantProfileMap_coordinate
      I N lam x hdiff n
  unfold finiteResonantRiemannianDerivative
  rw [riemannianComplexMFDeriv_apply_eq_fderiv_comp_tangentLine
      I (fun u ↦ finiteResonantProfileMap boundary N lam u n)
      x hx v houtDiff]
  rw [show (fun u ↦ finiteResonantProfileMap boundary N lam u n) ∘ γ =
      fun s ↦ finiteResonantNonlinearMap lam
        (fun k : Fin (N + 1) ↦ F k (γ s)) n by
      funext s
      rfl]
  rw [hcoord'.fderiv]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, finiteResonantTangentCLM_apply,
    γ, riemannianTangentChartLine_zero]
  congr 1
  funext k
  change fderiv ℝ (F k ∘ γ) 0 1 = _
  rw [← riemannianComplexMFDeriv_apply_eq_fderiv_comp_tangentLine
    I (F k) x hx v (hdiff k)]
  rfl

/-- The pulled-back standard symplectic density of the finite resonant
metric-profile map in an oriented orthonormal tangent frame. -/
def finiteResonantRiemannianSymplecticDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (boundary : UnitAddCircle → M) (N : ℕ) (lam : ℝ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x)) : ℝ :=
  standardComplexSymplectic
    (finiteResonantRiemannianDerivative I boundary N lam x (e 0))
    (finiteResonantRiemannianDerivative I boundary N lam x (e 1))

/-- Exact finite expansion of the genuine pulled-back resonant symplectic
density into its base, first-variation, and quadratic terms. -/
theorem finiteResonantRiemannianSymplecticDensity_eq_expansion
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (lam : ℝ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    finiteResonantRiemannianSymplecticDensity
        I boundary N lam x e =
      finiteBaseSymplecticDensity
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0))
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1)) +
        lam * finiteResonantFirstVariation
          (oddProfileFourierMap boundary (oddMode 0) x)
          (fun n : Fin N ↦
            oddProfileFourierMap boundary (oddMode n.succ) x)
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0))
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1)) +
        lam ^ 2 * finiteResonantQuadraticVariation
          (oddProfileFourierMap boundary (oddMode 0) x)
          (fun n : Fin N ↦
            oddProfileFourierMap boundary (oddMode n.succ) x)
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0))
          (finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1)) := by
  unfold finiteResonantRiemannianSymplecticDensity
  rw [finiteResonantRiemannianDerivative_eq_tangentMap
      I N lam x hx hdiff (e 0),
    finiteResonantRiemannianDerivative_eq_tangentMap
      I N lam x hx hdiff (e 1)]
  exact finiteResonant_symplectic_expansion _ _ _ _ _

/-- The existing finite nonlinear comass theorem applies directly to the
genuine pulled-back symplectic density once the actual Fourier derivative
columns have been represented by positive/negative frequency data. -/
theorem abs_finiteResonantRiemannianSymplecticDensity_le_comassBound
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (N : ℕ) (lam delta : ℝ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x)
    (cPos cNeg : Fin (N + 1) → ℂ)
    (hcolumn0 :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0) =
        finiteFourierTangentVector cPos cNeg)
    (hcolumn1 :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1) =
        finiteFourierQuarterTurnVector cPos cNeg)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hcoeffEnergy :
      finiteComplexEnergy cPos + finiteComplexEnergy cNeg ≤ 1)
    (hbase :
      |finiteBaseSymplecticDensity
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤ 1 - delta)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg)
    (hprofile :
      ‖oddProfileFourierMap boundary (oddMode 0) x‖ ^ 2 +
          9 * finiteComplexEnergy (fun n : Fin N ↦
            oddProfileFourierMap boundary (oddMode n.succ) x) ≤ 2)
    (hapi :
      ‖oddProfileFourierMap boundary (oddMode 0) x‖ ≤ 4 / Real.pi) :
    |finiteResonantRiemannianSymplecticDensity
        I boundary N lam x e| ≤ comassBound lam := by
  unfold finiteResonantRiemannianSymplecticDensity
  rw [finiteResonantRiemannianDerivative_eq_tangentMap
      I N lam x hx hdiff (e 0),
    finiteResonantRiemannianDerivative_eq_tangentMap
      I N lam x hx hdiff (e 1),
    hcolumn0, hcolumn1]
  exact abs_finiteResonantSymplectic_le_comassBound
    lam delta
      (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n : Fin N ↦
        oddProfileFourierMap boundary (oddMode n.succ) x)
      cPos cNeg hlam0 hlam hcoeffEnergy hbase hFull hprofile hapi

#print axioms mdifferentiableAt_finiteResonantProfileMap_coordinate
#print axioms finiteResonantRiemannianDerivative_eq_tangentMap
#print axioms finiteResonantRiemannianSymplecticDensity_eq_expansion
#print axioms abs_finiteResonantRiemannianSymplecticDensity_le_comassBound

end

end GromovFilling
