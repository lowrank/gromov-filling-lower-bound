import GromovFilling.FiniteResonantStokes
import GromovFilling.LipschitzWeakStokes

/-!
# Finite complex weak Stokes in Euclidean charts

This file lifts the scalar planar weak Stokes theorem to the finite standard
complex symplectic target used by the resonant calibration.  The weak complex
derivative is assembled from the Rademacher line derivatives of the real and
imaginary coordinate functions.  At every differentiability point it agrees
with the ordinary vector-valued line derivative.

The final theorem says that the integral of the pulled-back finite standard
symplectic density is zero for a compactly supported globally Lipschitz map on
a finite-dimensional real vector space.  It is a local Euclidean theorem;
globalization across oriented surface charts and recovery of the boundary
action remain separate obligations.
-/

open Function MeasureTheory
open scoped BigOperators NNReal

namespace GromovFilling

noncomputable section

/-- The weak line derivative of a finite complex-valued map, assembled from
the scalar Rademacher derivatives of its real and imaginary coordinates. -/
def finiteComplexWeakLineDerivative
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (F : E → ι → ℂ) (x p : E) : ι → ℂ :=
  fun i ↦
    ⟨lineDeriv ℝ (fun y ↦ (F y i).re) x p,
      lineDeriv ℝ (fun y ↦ (F y i).im) x p⟩

/-- The finite standard symplectic density of the weak derivative is the sum
of the scalar weak Jacobians of the complex coordinates. -/
theorem standardComplexSymplectic_finiteComplexWeakLineDerivative
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (F : E → ι → ℂ) (x p q : E) :
    standardComplexSymplectic
        (finiteComplexWeakLineDerivative F x p)
        (finiteComplexWeakLineDerivative F x q) =
      Finset.univ.sum (fun i : ι ↦
        lineDeriv ℝ (fun y ↦ (F y i).re) x p *
            lineDeriv ℝ (fun y ↦ (F y i).im) x q -
          lineDeriv ℝ (fun y ↦ (F y i).re) x q *
            lineDeriv ℝ (fun y ↦ (F y i).im) x p) := by
  unfold standardComplexSymplectic finiteComplexWeakLineDerivative
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_im]
  simp
  ring

/-- At a differentiability point, the coordinatewise weak derivative agrees
with the ordinary vector-valued line derivative. -/
theorem finiteComplexWeakLineDerivative_eq_lineDeriv
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (F : E → ι → ℂ) {x : E}
    (hF : DifferentiableAt ℝ F x) (p : E) :
    finiteComplexWeakLineDerivative F x p = lineDeriv ℝ F x p := by
  funext i
  apply Complex.ext
  · change lineDeriv ℝ (fun y ↦ (F y i).re) x p =
      (lineDeriv ℝ F x p i).re
    have hre :=
      (Complex.reCLM.hasFDerivAt.comp x
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp
          x hF.hasFDerivAt)).hasLineDerivAt p
    calc
      lineDeriv ℝ (fun y ↦ (F y i).re) x p =
          Complex.reCLM ((fderiv ℝ F x) p i) := by
        simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply]
          using hre.lineDeriv
      _ = ((fderiv ℝ F x) p i).re := Complex.reCLM_apply _
      _ = (lineDeriv ℝ F x p i).re := by rw [hF.lineDeriv_eq_fderiv]
  · change lineDeriv ℝ (fun y ↦ (F y i).im) x p =
      (lineDeriv ℝ F x p i).im
    have him :=
      (Complex.imCLM.hasFDerivAt.comp x
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp
          x hF.hasFDerivAt)).hasLineDerivAt p
    calc
      lineDeriv ℝ (fun y ↦ (F y i).im) x p =
          Complex.imCLM ((fderiv ℝ F x) p i) := by
        simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply]
          using him.lineDeriv
      _ = ((fderiv ℝ F x) p i).im := Complex.imCLM_apply _
      _ = (lineDeriv ℝ F x p i).im := by rw [hF.lineDeriv_eq_fderiv]

/-- A globally Lipschitz finite complex map has Lipschitz real coordinate
functions with the same constant. -/
private theorem lipschitzWith_real_coordinate
    {E ι : Type*} [PseudoEMetricSpace E] [Fintype ι]
    {F : E → ι → ℂ} {C : ℝ≥0} (hF : LipschitzWith C F) (i : ι) :
    LipschitzWith C (fun x ↦ (F x i).re) := by
  simpa only [Function.comp_apply, one_mul] using
    (RCLike.lipschitzWith_re (K := ℂ)).comp
      ((LipschitzWith.eval i).comp hF)

/-- A globally Lipschitz finite complex map has Lipschitz imaginary
coordinate functions with the same constant. -/
private theorem lipschitzWith_imaginary_coordinate
    {E ι : Type*} [PseudoEMetricSpace E] [Fintype ι]
    {F : E → ι → ℂ} {C : ℝ≥0} (hF : LipschitzWith C F) (i : ι) :
    LipschitzWith C (fun x ↦ (F x i).im) := by
  simpa only [Function.comp_apply, one_mul] using
    (RCLike.lipschitzWith_im (K := ℂ)).comp
      ((LipschitzWith.eval i).comp hF)

/-- Compact support of a finite complex map passes to each imaginary
coordinate. -/
private theorem hasCompactSupport_imaginary_coordinate
    {E ι : Type*} [TopologicalSpace E] [Fintype ι]
    {F : E → ι → ℂ} (hF : HasCompactSupport F) (i : ι) :
    HasCompactSupport (fun x ↦ (F x i).im) := by
  have hcoord : HasCompactSupport (fun x ↦ F x i) := by
    simpa only [Function.comp_apply] using
      hF.comp_left (g := Function.eval i) rfl
  simpa only [Function.comp_apply] using
    hcoord.comp_left (g := Complex.im) rfl

/-- Finite complex weak Stokes in a Euclidean chart: a compactly supported
globally Lipschitz map has zero integrated standard symplectic density. -/
theorem integral_standardComplexSymplectic_finiteComplexWeakLineDerivative_eq_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Fintype ι] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : E → ι → ℂ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFCompact : HasCompactSupport F)
    (p q : E) :
    ∫ x : E,
        standardComplexSymplectic
          (finiteComplexWeakLineDerivative F x p)
          (finiteComplexWeakLineDerivative F x q) ∂mu = 0 := by
  simp_rw [standardComplexSymplectic_finiteComplexWeakLineDerivative]
  rw [integral_finset_sum Finset.univ]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_lipschitz_lipschitz_jacobian_eq_zero mu
      (lipschitzWith_real_coordinate hF i)
      (lipschitzWith_imaginary_coordinate hF i)
      (hasCompactSupport_imaginary_coordinate hFCompact i) p q
  · intro i _
    exact (integrable_lineDeriv_mul_lineDeriv_of_lipschitzWith mu
      (lipschitzWith_real_coordinate hF i)
      (lipschitzWith_imaginary_coordinate hF i)
      (hasCompactSupport_imaginary_coordinate hFCompact i) p q).sub
      (integrable_lineDeriv_mul_lineDeriv_of_lipschitzWith mu
        (lipschitzWith_real_coordinate hF i)
        (lipschitzWith_imaginary_coordinate hF i)
        (hasCompactSupport_imaginary_coordinate hFCompact i) q p)

/-- The same local weak Stokes theorem expressed using the vector-valued
Rademacher line derivative. -/
theorem integral_standardComplexSymplectic_lineDeriv_eq_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Fintype ι] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : E → ι → ℂ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFCompact : HasCompactSupport F)
    (p q : E) :
    ∫ x : E,
        standardComplexSymplectic
          (lineDeriv ℝ F x p) (lineDeriv ℝ F x q) ∂mu = 0 := by
  rw [← integral_standardComplexSymplectic_finiteComplexWeakLineDerivative_eq_zero
    mu hF hFCompact p q]
  apply integral_congr_ae
  filter_upwards [hF.ae_differentiableAt (μ := mu)] with x hx
  rw [finiteComplexWeakLineDerivative_eq_lineDeriv F hx p,
    finiteComplexWeakLineDerivative_eq_lineDeriv F hx q]

/-- The local weak Stokes theorem in the form used by chartwise pullbacks:
the integral of the standard symplectic pairing of the two columns of the
Fréchet derivative is zero.  At the null set of nondifferentiability points,
Mathlib's `fderiv` is defined to be zero. -/
theorem integral_standardComplexSymplectic_fderiv_eq_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Fintype ι] (mu : Measure E) [mu.IsAddHaarMeasure]
    {F : E → ι → ℂ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFCompact : HasCompactSupport F)
    (p q : E) :
    ∫ x : E,
        standardComplexSymplectic
          ((fderiv ℝ F x) p) ((fderiv ℝ F x) q) ∂mu = 0 := by
  rw [← integral_standardComplexSymplectic_lineDeriv_eq_zero
    mu hF hFCompact p q]
  apply integral_congr_ae
  filter_upwards [hF.ae_differentiableAt (μ := mu)] with x hx
  rw [hx.lineDeriv_eq_fderiv, hx.lineDeriv_eq_fderiv]

#print axioms standardComplexSymplectic_finiteComplexWeakLineDerivative
#print axioms finiteComplexWeakLineDerivative_eq_lineDeriv
#print axioms integral_standardComplexSymplectic_finiteComplexWeakLineDerivative_eq_zero
#print axioms integral_standardComplexSymplectic_lineDeriv_eq_zero
#print axioms integral_standardComplexSymplectic_fderiv_eq_zero

end

end GromovFilling
