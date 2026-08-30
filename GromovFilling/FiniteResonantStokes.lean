import GromovFilling.BoundaryActionSeries
import GromovFilling.ClosedOneForm
import GromovFilling.NonlinearSymplecticCalculus
import GromovFilling.ProfileFourier
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Finite resonant Stokes data

This file packages the target-space differential geometry for the finite
resonant truncations used in the nonlinear filling certificate.  In
particular, it realizes the standard complex symplectic form as the exterior
derivative of an explicit linear-in-the-base-point primitive.

The global Stokes theorem for an arbitrary compact oriented Riemannian
surface, and its weak regularity interface for the metric Fourier map, remain
separate geometric obligations.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

section StandardComplexSymplecticPrimitive

variable {ι : Type*} [Fintype ι]

private theorem standardComplexSymplectic_isBilinear :
    IsBilinearMap ℝ
      (standardComplexSymplectic : (ι → ℂ) → (ι → ℂ) → ℝ) where
  add_left p₁ p₂ q := by
    unfold standardComplexSymplectic
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.mul_im]
    ring
  smul_left c p q := by
    unfold standardComplexSymplectic
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change Complex.imCLM (star ((c • p) i) * q i) =
      c • Complex.imCLM (star (p i) * q i)
    rw [Pi.smul_apply, star_smul, star_trivial, smul_mul_assoc,
      map_smul]
  add_right p q₁ q₂ := by
    unfold standardComplexSymplectic
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.mul_im]
    ring
  smul_right c p q := by
    unfold standardComplexSymplectic
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change Complex.imCLM (star (p i) * (c • q) i) =
      c • Complex.imCLM (star (p i) * q i)
    rw [Pi.smul_apply, mul_smul_comm, map_smul]

theorem standardComplexSymplectic_swap (p q : ι → ℂ) :
    standardComplexSymplectic q p =
      -standardComplexSymplectic p q := by
  unfold standardComplexSymplectic
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_im]
  ring

variable [Finite ι]

/-- The standard complex symplectic form, bundled as a continuous real
bilinear map on a finite complex coordinate space. -/
def standardComplexSymplecticBilinear :
    (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  standardComplexSymplectic_isBilinear.toContinuousBilinearMap

@[simp] theorem standardComplexSymplecticBilinear_apply
    (p q : ι → ℂ) :
    standardComplexSymplecticBilinear p q =
      standardComplexSymplectic p q := by
  simp [standardComplexSymplecticBilinear]

/-- The standard symplectic primitive `z ↦ (1/2) Ω(z, ·)`, bundled as a
continuous real-linear map into the continuous dual. -/
def standardComplexSymplecticPrimitiveCLM :
    (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • standardComplexSymplecticBilinear

/-- The standard symplectic primitive as a differential `1`-form. -/
def standardComplexSymplecticPrimitive
    (z : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  standardComplexSymplecticPrimitiveCLM z

@[simp] theorem standardComplexSymplecticPrimitive_apply
    (z p : ι → ℂ) :
    standardComplexSymplecticPrimitive z p =
      (1 / 2 : ℝ) * standardComplexSymplectic z p := by
  simp [standardComplexSymplecticPrimitive,
    standardComplexSymplecticPrimitiveCLM]

/-- The derivative of the standard symplectic primitive is its defining
continuous linear map, independently of the base point. -/
theorem hasFDerivAt_standardComplexSymplecticPrimitive
    (z : ι → ℂ) :
    HasFDerivAt
      (standardComplexSymplecticPrimitive :
        (ι → ℂ) → (ι → ℂ) →L[ℝ] ℝ)
      standardComplexSymplecticPrimitiveCLM z := by
  simpa [standardComplexSymplecticPrimitive] using
    (standardComplexSymplecticPrimitiveCLM (ι := ι)).hasFDerivAt

theorem fderiv_standardComplexSymplecticPrimitive
    (z : ι → ℂ) :
    fderiv ℝ
        (standardComplexSymplecticPrimitive :
          (ι → ℂ) → (ι → ℂ) →L[ℝ] ℝ) z =
      standardComplexSymplecticPrimitiveCLM :=
  (hasFDerivAt_standardComplexSymplecticPrimitive z).fderiv

/-- The antisymmetrized derivative of the explicit primitive is exactly the
standard complex symplectic form. -/
theorem fderiv_standardComplexSymplecticPrimitive_skew
    (z p q : ι → ℂ) :
    fderiv ℝ
          (standardComplexSymplecticPrimitive :
            (ι → ℂ) → (ι → ℂ) →L[ℝ] ℝ) z p q -
        fderiv ℝ
          (standardComplexSymplecticPrimitive :
            (ι → ℂ) → (ι → ℂ) →L[ℝ] ℝ) z q p =
      standardComplexSymplectic p q := by
  rw [fderiv_standardComplexSymplecticPrimitive]
  simp only [standardComplexSymplecticPrimitiveCLM,
    ContinuousLinearMap.smul_apply,
    standardComplexSymplecticBilinear_apply, smul_eq_mul]
  rw [standardComplexSymplectic_swap]
  ring

/-- The explicit symplectic primitive is continuously differentiable. -/
theorem contDiff_standardComplexSymplecticPrimitive :
    ContDiff ℝ 1
      (standardComplexSymplecticPrimitive :
        (ι → ℂ) → (ι → ℂ) →L[ℝ] ℝ) := by
  simpa [standardComplexSymplecticPrimitive] using
    (standardComplexSymplecticPrimitiveCLM (ι := ι)).contDiff

#print axioms standardComplexSymplecticBilinear_apply
#print axioms standardComplexSymplectic_swap
#print axioms hasFDerivAt_standardComplexSymplecticPrimitive
#print axioms fderiv_standardComplexSymplecticPrimitive
#print axioms fderiv_standardComplexSymplecticPrimitive_skew
#print axioms contDiff_standardComplexSymplecticPrimitive

end StandardComplexSymplecticPrimitive

section FiniteResonantDifferential

private theorem finiteResonantTangentMap_isLinear {N : ℕ}
    (lam : ℝ) (a : ℂ) (y : Fin N → ℂ) :
    IsLinearMap ℝ (finiteResonantTangentMap lam a y) where
  map_add p q := by
    funext n
    simp [finiteResonantTangentMap, resonantDifferentialVariation,
      Pi.add_apply, star_add]
    ring
  map_smul c p := by
    funext n
    simp [finiteResonantTangentMap, resonantDifferentialVariation,
      Pi.smul_apply, star_smul, star_trivial, smul_add,
      mul_smul_comm]
    rw [← smul_add, mul_smul_comm]

/-- The exact tangent map as a real-linear map. -/
def finiteResonantTangentLinearMap {N : ℕ} (lam : ℝ)
    (a : ℂ) (y : Fin N → ℂ) :
    (Fin (N + 1) → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun := finiteResonantTangentMap lam a y
  map_add' := (finiteResonantTangentMap_isLinear lam a y).map_add
  map_smul' := (finiteResonantTangentMap_isLinear lam a y).map_smul

/-- The exact tangent map of the finite resonant nonlinear deformation,
bundled as a continuous real-linear map. -/
def finiteResonantTangentCLM {N : ℕ} (lam : ℝ)
    (a : ℂ) (y : Fin N → ℂ) :
    (Fin (N + 1) → ℂ) →L[ℝ] (Fin N → ℂ) :=
  (finiteResonantTangentLinearMap lam a y).toContinuousLinearMap

@[simp] theorem finiteResonantTangentCLM_apply {N : ℕ}
    (lam : ℝ) (a : ℂ) (y : Fin N → ℂ)
    (p : Fin (N + 1) → ℂ) :
    finiteResonantTangentCLM lam a y p =
      finiteResonantTangentMap lam a y p := by
  rfl

/-- The bundled tangent map is the exact real Fréchet derivative of the
finite resonant nonlinear deformation. -/
theorem hasFDerivAt_finiteResonantNonlinearMap {N : ℕ}
    (lam : ℝ) (z : Fin (N + 1) → ℂ) :
    HasFDerivAt (finiteResonantNonlinearMap lam)
      (finiteResonantTangentCLM lam (z 0) (fun n ↦ z n.succ)) z := by
  rw [hasFDerivAt_pi']
  intro n
  have hbase : HasFDerivAt
      (fun w : Fin (N + 1) → ℂ ↦ w n.castSucc)
      (ContinuousLinearMap.proj n.castSucc) z :=
    hasFDerivAt_apply (𝕜 := ℝ) n.castSucc z
  have hzero : HasFDerivAt
      (fun w : Fin (N + 1) → ℂ ↦ star (w 0))
      (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L
        ContinuousLinearMap.proj 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) 0 z).star
  have hshift : HasFDerivAt
      (fun w : Fin (N + 1) → ℂ ↦ w n.succ)
      (ContinuousLinearMap.proj n.succ) z :=
    hasFDerivAt_apply (𝕜 := ℝ) n.succ z
  have hproduct := (hzero.mul hzero).mul hshift
  have hscaled := hproduct.const_mul (lam : ℂ)
  have hsum := hbase.add hscaled
  convert hsum using 1
  · funext w
    simp [finiteResonantNonlinearMap, pow_two]
    ring
  · ext p
    let starProj : (Fin (N + 1) → ℂ) →L[ℝ] ℂ :=
        (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L
          (ContinuousLinearMap.proj 0 :
            (Fin (N + 1) → ℂ) →L[ℝ] ℂ))
    let nonlinearDeriv : (Fin (N + 1) → ℂ) →L[ℝ] ℂ :=
      (star (z 0) * star (z 0)) •
          (ContinuousLinearMap.proj n.succ :
            (Fin (N + 1) → ℂ) →L[ℝ] ℂ) +
        z n.succ •
          (star (z 0) • starProj + star (z 0) • starProj)
    let totalDeriv : (Fin (N + 1) → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj n.castSucc :
          (Fin (N + 1) → ℂ) →L[ℝ] ℂ) +
        (lam : ℂ) • nonlinearDeriv
    change _ = totalDeriv p
    simp only [totalDeriv, nonlinearDeriv, starProj,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      finiteResonantTangentCLM_apply]
    simp
    simp [finiteResonantTangentMap, resonantDifferentialVariation, pow_two]
    ring_nf
    simp

/-- Exact formula for the real Fréchet derivative of the finite resonant
nonlinear deformation. -/
theorem fderiv_finiteResonantNonlinearMap {N : ℕ}
    (lam : ℝ) (z : Fin (N + 1) → ℂ) :
    fderiv ℝ (finiteResonantNonlinearMap lam) z =
      finiteResonantTangentCLM lam (z 0) (fun n ↦ z n.succ) :=
  (hasFDerivAt_finiteResonantNonlinearMap lam z).fderiv

/-- Every finite resonant nonlinear deformation is smooth of all orders. -/
theorem contDiff_finiteResonantNonlinearMap {N : ℕ}
    (lam : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (finiteResonantNonlinearMap (N := N) lam) := by
  rw [contDiff_pi]
  intro n
  have hcast : ContDiff ℝ k
      (fun z : Fin (N + 1) → ℂ ↦ z n.castSucc) := by
    fun_prop
  have hzero : ContDiff ℝ k
      (fun z : Fin (N + 1) → ℂ ↦ star (z 0)) := by
    exact (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (by fun_prop)
  have hshift : ContDiff ℝ k
      (fun z : Fin (N + 1) → ℂ ↦ z n.succ) := by
    fun_prop
  simpa [finiteResonantNonlinearMap, pow_two] using
    hcast.add ((contDiff_const.mul (hzero.mul hzero)).mul hshift)

/-- The actual finite resonant deformation of the metric odd-profile Fourier
map.  The input keeps one additional odd mode so every shifted output mode is
available. -/
def finiteResonantProfileMap {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (N : ℕ) (lam : ℝ) (x : X) :
    Fin N → ℂ :=
  finiteResonantNonlinearMap lam
    (fun k : Fin (N + 1) ↦
      oddProfileFourierMap boundary (oddMode k) x)

/-- The finite resonant profile map is continuous on every isometric circle
filling. -/
theorem continuous_finiteResonantProfileMap
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) :
    Continuous (finiteResonantProfileMap boundary N lam) := by
  have hprofile : Continuous
      (fun x : X ↦ fun k : Fin (N + 1) ↦
        oddProfileFourierMap boundary (oddMode k) x) := by
    exact continuous_pi fun k ↦
      continuous_oddProfileFourierMap hboundary (oddMode k)
  exact (contDiff_finiteResonantNonlinearMap (N := N) lam ⊤).continuous.comp
    hprofile

/-- On a compact metric filling, every finite resonant profile map admits a
global Lipschitz constant.  The finite odd-profile vector is already
globally Lipschitz coordinatewise; the polynomial resonant deformation is
locally Lipschitz, and compactness upgrades the composite to one global
constant. -/
theorem exists_lipschitzWith_finiteResonantProfileMap
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) :
    ∃ C : NNReal, LipschitzWith C
      (finiteResonantProfileMap boundary N lam) := by
  let P : X → Fin (N + 1) → ℂ := fun x k ↦
    oddProfileFourierMap boundary (oddMode k) x
  have hP : LipschitzWith (4 : NNReal) P := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (mul_nonneg (by norm_num) dist_nonneg)).2
    intro k
    exact
      (oddProfileFourierMap_lipschitzWith hboundary (oddMode k)).dist_le_mul
        x y
  have hnonlinear : LocallyLipschitz
      (finiteResonantNonlinearMap (N := N) lam) :=
    (contDiff_finiteResonantNonlinearMap (N := N) lam 1).locallyLipschitz
  have hlocal : LocallyLipschitz
      (finiteResonantProfileMap boundary N lam) := by
    change LocallyLipschitz (finiteResonantNonlinearMap lam ∘ P)
    exact hnonlinear.comp hP.locallyLipschitz
  obtain ⟨C, hC⟩ :=
    hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_univ
  exact ⟨C, lipschitzOnWith_univ.mp hC⟩

private lemma star_complex_exp_mul_I (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) =
      Complex.exp ((-t : ℂ) * Complex.I) := by
  change (starRingEnd ℂ) (Complex.exp ((t : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  simp

private lemma resonant_complex_exp_identity (m : ℕ) (s : ℝ) :
    star (Complex.exp ((s : ℂ) * Complex.I)) ^ 2 *
        Complex.exp (((((m + 2 : ℕ) : ℝ) * s : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((((m : ℝ) * s : ℝ) : ℂ) * Complex.I) := by
  rw [star_complex_exp_mul_I, pow_two, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact resonant Fourier trace on the isometric boundary. -/
theorem finiteResonantProfileMap_on_boundary
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam : ℝ) (s : ℝ) :
    finiteResonantProfileMap boundary N lam
        (boundary (angleToUnitAddCircle s)) =
      fun n : Fin N ↦
        -(resonantBoundaryCoefficient lam n : ℂ) *
          Complex.exp
            (((((oddMode n : ℝ) * s : ℝ) : ℂ) * Complex.I)) := by
  funext n
  unfold finiteResonantProfileMap finiteResonantNonlinearMap
  change
    oddProfileFourierMap boundary (oddMode (n.castSucc : ℕ))
          (boundary (angleToUnitAddCircle s)) +
        (lam : ℂ) *
          star (oddProfileFourierMap boundary (oddMode 0)
            (boundary (angleToUnitAddCircle s))) ^ 2 *
          oddProfileFourierMap boundary (oddMode (n.succ : ℕ))
            (boundary (angleToUnitAddCircle s)) = _
  rw [oddProfileFourierMap_on_boundary_of_odd hboundary
      (oddMode n.castSucc) (odd_oddMode n.castSucc) s,
    oddProfileFourierMap_on_boundary_of_odd hboundary
      (oddMode 0) (odd_oddMode 0) s,
    oddProfileFourierMap_on_boundary_of_odd hboundary
      (oddMode n.succ) (odd_oddMode n.succ) s]
  have hcast : oddMode (n.castSucc : ℕ) = oddMode (n : ℕ) := rfl
  have hzero : oddMode 0 = 1 := by rfl
  have hsucc : oddMode (n.succ : ℕ) = oddMode (n : ℕ) + 2 := by
    unfold oddMode
    simp
    ring_nf
  rw [hcast, hzero, hsucc]
  simp [resonantBoundaryCoefficient, star_complex_exp_mul_I]
  have hexp :
      Complex.exp (-((s : ℂ) * Complex.I)) ^ 2 *
          Complex.exp
            ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I +
              (s : ℂ) * Complex.I * 2) =
        Complex.exp
          ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I) := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hshiftExp :
      Complex.exp
          (((oddMode (n : ℕ) : ℂ) + 2) * (s : ℂ) * Complex.I) =
        Complex.exp
          ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I +
            (s : ℂ) * Complex.I * 2) := by
    congr 1
    ring
  have hnonlinear :
      ((boundaryRadius 1 : ℂ) *
            Complex.exp (-((s : ℂ) * Complex.I))) ^ 2 *
          ((boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
            Complex.exp
              (((oddMode (n : ℕ) : ℂ) + 2) *
                (s : ℂ) * Complex.I)) =
        (boundaryRadius 1 : ℂ) ^ 2 *
          (boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
          Complex.exp
            ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I) := by
    rw [hshiftExp]
    calc
      _ = (boundaryRadius 1 : ℂ) ^ 2 *
          (boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
          (Complex.exp (-((s : ℂ) * Complex.I)) ^ 2 *
            Complex.exp
              ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I +
                (s : ℂ) * Complex.I * 2)) := by ring
      _ = _ := by rw [hexp]
  have hscaled :
      (lam : ℂ) *
          ((boundaryRadius 1 : ℂ) *
            Complex.exp (-((s : ℂ) * Complex.I))) ^ 2 *
          ((boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
            Complex.exp
              (((oddMode (n : ℕ) : ℂ) + 2) *
                (s : ℂ) * Complex.I)) =
        (lam : ℂ) * (boundaryRadius 1 : ℂ) ^ 2 *
          (boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
          Complex.exp
            ((oddMode (n : ℕ) : ℂ) * (s : ℂ) * Complex.I) := by
    calc
      _ = (lam : ℂ) *
          (((boundaryRadius 1 : ℂ) *
              Complex.exp (-((s : ℂ) * Complex.I))) ^ 2 *
            ((boundaryRadius (oddMode (n : ℕ) + 2) : ℂ) *
              Complex.exp
                (((oddMode (n : ℕ) : ℂ) + 2) *
                  (s : ℂ) * Complex.I))) := by ring
      _ = _ := by
        rw [hnonlinear]
        ring
  rw [hscaled]
  simp [oddMode]
  ring

/-- The explicit finite resonant Fourier loop appearing as the boundary trace
of `finiteResonantProfileMap`. -/
def finiteResonantBoundaryCurve (N : ℕ) (lam t : ℝ) : Fin N → ℂ :=
  fun n ↦ -(resonantBoundaryCoefficient lam n : ℂ) *
    Complex.exp
      (((((oddMode n : ℝ) * t : ℝ) : ℂ) * Complex.I))

/-- The explicit velocity of the finite resonant Fourier loop. -/
def finiteResonantBoundaryVelocity (N : ℕ) (lam t : ℝ) : Fin N → ℂ :=
  fun n ↦ ((oddMode n : ℝ) : ℂ) * Complex.I *
    finiteResonantBoundaryCurve N lam t n

/-- The metric finite resonant profile has the explicit resonant Fourier loop
as its boundary trace. -/
theorem finiteResonantProfileMap_boundary_eq_curve
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam t : ℝ) :
    finiteResonantProfileMap boundary N lam
        (boundary (angleToUnitAddCircle t)) =
      finiteResonantBoundaryCurve N lam t := by
  rw [finiteResonantProfileMap_on_boundary hboundary N lam t]
  funext n
  unfold finiteResonantBoundaryCurve
  ring

/-- The displayed velocity is the genuine real derivative of the explicit
finite resonant boundary loop. -/
theorem hasDerivAt_finiteResonantBoundaryCurve
    (N : ℕ) (lam t : ℝ) :
    HasDerivAt (finiteResonantBoundaryCurve N lam)
      (finiteResonantBoundaryVelocity N lam t) t := by
  rw [hasDerivAt_pi]
  intro n
  have hreal : HasDerivAt
      (fun s : ℝ ↦ (oddMode n : ℝ) * s)
      (oddMode n : ℝ) t :=
    by simpa using (hasDerivAt_id t).const_mul (oddMode n : ℝ)
  have hphase : HasDerivAt
      (fun s : ℝ ↦
        ((((oddMode n : ℝ) * s : ℝ) : ℂ) * Complex.I))
      ((oddMode n : ℂ) * Complex.I) t :=
    hreal.ofReal_comp.mul_const Complex.I
  have hexp := hphase.cexp
  have hcurve := hexp.const_mul
    (-(resonantBoundaryCoefficient lam n : ℂ))
  convert hcurve using 1
  all_goals
    simp [finiteResonantBoundaryVelocity, finiteResonantBoundaryCurve]
    ring

private lemma im_star_mul_real_I_mul (r : ℝ) (z : ℂ) :
    (star z * ((r : ℂ) * Complex.I * z)).im =
      r * Complex.normSq z := by
  simp [Complex.mul_im, Complex.normSq_apply]
  ring

private lemma normSq_finiteResonantBoundaryCurve
    (N : ℕ) (lam t : ℝ) (n : Fin N) :
    Complex.normSq (finiteResonantBoundaryCurve N lam t n) =
      resonantBoundaryCoefficient lam n ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  simp only [finiteResonantBoundaryCurve, norm_mul, norm_neg]
  have hexpnorm :
      ‖Complex.exp
        (((((oddMode n : ℝ) * t : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexpnorm, mul_one]
  simp [sq_abs]

/-- The symplectic primitive evaluated on the explicit loop and its velocity
is constant in the boundary parameter. -/
theorem standardComplexSymplecticPrimitive_resonantBoundary
    (N : ℕ) (lam t : ℝ) :
    standardComplexSymplecticPrimitive
        (finiteResonantBoundaryCurve N lam t)
        (finiteResonantBoundaryVelocity N lam t) =
      (1 / 2 : ℝ) * ∑ n : Fin N,
        (oddMode n : ℝ) * resonantBoundaryCoefficient lam n ^ 2 := by
  rw [standardComplexSymplecticPrimitive_apply]
  unfold standardComplexSymplectic finiteResonantBoundaryVelocity
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [im_star_mul_real_I_mul,
    normSq_finiteResonantBoundaryCurve]

/-- The standard symplectic primitive action of the explicit finite resonant
boundary loop, parametrized over one full angular period. -/
def finiteResonantSymplecticBoundaryAction (N : ℕ) (lam : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    standardComplexSymplecticPrimitive
      (finiteResonantBoundaryCurve N lam t)
      (finiteResonantBoundaryVelocity N lam t)

/-- The genuine symplectic boundary action is exactly the finite Green-area
quantity already used by the resonant certificate. -/
theorem finiteResonantSymplecticBoundaryAction_eq_fourierGreenArea
    (N : ℕ) (lam : ℝ) :
    finiteResonantSymplecticBoundaryAction N lam =
      fourierGreenArea
        (fun n : Fin N ↦ oddMode n)
        (fun n : Fin N ↦ resonantBoundaryCoefficient lam n) := by
  unfold finiteResonantSymplecticBoundaryAction
  simp_rw [standardComplexSymplecticPrimitive_resonantBoundary]
  rw [intervalIntegral.integral_const,
    fourierGreenArea_eq
      (m := fun n : Fin N ↦ oddMode n)
      (a := fun n : Fin N ↦ resonantBoundaryCoefficient lam n)
      (oddMode_injective.comp Fin.val_injective)]
  simp
  ring

#print axioms finiteResonantTangentCLM_apply
#print axioms hasFDerivAt_finiteResonantNonlinearMap
#print axioms fderiv_finiteResonantNonlinearMap
#print axioms contDiff_finiteResonantNonlinearMap
#print axioms continuous_finiteResonantProfileMap
#print axioms exists_lipschitzWith_finiteResonantProfileMap
#print axioms finiteResonantProfileMap_on_boundary
#print axioms finiteResonantProfileMap_boundary_eq_curve
#print axioms hasDerivAt_finiteResonantBoundaryCurve
#print axioms standardComplexSymplecticPrimitive_resonantBoundary
#print axioms finiteResonantSymplecticBoundaryAction_eq_fourierGreenArea

end FiniteResonantDifferential

end

end GromovFilling
