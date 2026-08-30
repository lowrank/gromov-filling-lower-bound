import GromovFilling.HalfPlaneWeakStokes
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Lipschitz weak Stokes on a complex half-plane

This module transports the product-coordinate half-plane theorem to the
complex coordinate plane.  The real axis is the oriented boundary of the
right half-plane, and the standard positive complex frame is `(1, I)`.
The transport is volume preserving and retains the exact outward-normal
minus sign.
-/

open Function MeasureTheory Set
open scoped NNReal

namespace GromovFilling

noncomputable section

/-- The canonical real-product-to-complex linear equivalence. -/
def complexOfRealProd : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm

@[simp] theorem complexOfRealProd_apply (p : ℝ × ℝ) :
    complexOfRealProd p = p.1 + p.2 * Complex.I := by
  exact Complex.equivRealProdCLM_symm_apply p

@[simp] theorem complexOfRealProd_one_zero :
    complexOfRealProd (1, 0) = 1 := by
  simp

@[simp] theorem complexOfRealProd_zero_one :
    complexOfRealProd (0, 1) = Complex.I := by
  simp

@[simp] theorem complexOfRealProd_zero (y : ℝ) :
    complexOfRealProd (0, y) = y * Complex.I := by
  simp

/-- The open right half-plane in complex coordinates. -/
def complexRightOpenHalfPlane : Set ℂ :=
  {z | 0 < z.re}

theorem preimage_complexRightOpenHalfPlane :
    complexOfRealProd ⁻¹' complexRightOpenHalfPlane =
      planarRightOpenHalfPlane := by
  ext p
  simp [complexRightOpenHalfPlane, planarRightOpenHalfPlane]

/-- Lebesgue integration is unchanged by the canonical
real-product-to-complex equivalence. -/
theorem setIntegral_comp_complexOfRealProd_preimage
    (g : ℂ → ℝ) (s : Set ℂ) :
    (∫ p in complexOfRealProd ⁻¹' s, g (complexOfRealProd p)) =
      ∫ z in s, g z := by
  simpa only [complexOfRealProd, Complex.measurableEquivRealProd] using
    Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding g s

/-- Real-product motion in the first coordinate becomes complex motion in
the real direction. -/
theorem lineDeriv_comp_complexOfRealProd_one
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℂ → Y) (p : ℝ × ℝ) :
    lineDeriv ℝ (f ∘ complexOfRealProd) p (1, 0) =
      lineDeriv ℝ f (complexOfRealProd p) 1 := by
  unfold lineDeriv
  congr 1
  funext t
  simp only [Function.comp_apply, map_add, map_smul,
    complexOfRealProd_one_zero]
  rfl

/-- Real-product motion in the second coordinate becomes complex motion in
the imaginary direction. -/
theorem lineDeriv_comp_complexOfRealProd_I
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : ℂ → Y) (p : ℝ × ℝ) :
    lineDeriv ℝ (f ∘ complexOfRealProd) p (0, 1) =
      lineDeriv ℝ f (complexOfRealProd p) Complex.I := by
  unfold lineDeriv
  congr 1
  funext t
  simp only [Function.comp_apply, map_add, map_smul,
    complexOfRealProd_zero_one]
  rfl

/-- Weak finite complex derivative in the real product direction agrees
with weak differentiation in the complex real direction. -/
theorem finiteComplexWeakLineDerivative_comp_complexOfRealProd_one
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (p : ℝ × ℝ) :
    finiteComplexWeakLineDerivative (F ∘ complexOfRealProd) p (1, 0) =
      finiteComplexWeakLineDerivative F (complexOfRealProd p) 1 := by
  funext i
  apply Complex.ext
  · exact lineDeriv_comp_complexOfRealProd_one
      (fun z ↦ (F z i).re) p
  · exact lineDeriv_comp_complexOfRealProd_one
      (fun z ↦ (F z i).im) p

/-- Weak finite complex derivative in the second product direction agrees
with weak differentiation in the complex imaginary direction. -/
theorem finiteComplexWeakLineDerivative_comp_complexOfRealProd_I
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (p : ℝ × ℝ) :
    finiteComplexWeakLineDerivative (F ∘ complexOfRealProd) p (0, 1) =
      finiteComplexWeakLineDerivative F (complexOfRealProd p) Complex.I := by
  funext i
  apply Complex.ext
  · exact lineDeriv_comp_complexOfRealProd_I
      (fun z ↦ (F z i).re) p
  · exact lineDeriv_comp_complexOfRealProd_I
      (fun z ↦ (F z i).im) p

/-- Weak finite symplectic density in the standard positive complex frame. -/
def finiteComplexWeakSymplecticDensityComplex
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (z : ℂ) : ℝ :=
  standardComplexSymplectic
    (finiteComplexWeakLineDerivative F z 1)
    (finiteComplexWeakLineDerivative F z Complex.I)

/-- The product-coordinate density is the pullback of the complex density. -/
theorem finiteComplexWeakSymplecticDensity_comp_complexOfRealProd
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (p : ℝ × ℝ) :
    finiteComplexWeakSymplecticDensity (F ∘ complexOfRealProd) p =
      finiteComplexWeakSymplecticDensityComplex F (complexOfRealProd p) := by
  unfold finiteComplexWeakSymplecticDensity
    finiteComplexWeakSymplecticDensityComplex
  rw [finiteComplexWeakLineDerivative_comp_complexOfRealProd_one,
    finiteComplexWeakLineDerivative_comp_complexOfRealProd_I]

/-- Cutoff-derivative primitive error in the standard complex frame. -/
def finiteComplexWeakPrimitiveErrorComplex
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ)
    (F : ℂ → ι → ℂ) (z : ℂ) : ℝ :=
  lineDeriv ℝ ρ z Complex.I *
      standardComplexSymplecticPrimitive
        (F z) (finiteComplexWeakLineDerivative F z 1) -
    lineDeriv ℝ ρ z 1 *
      standardComplexSymplecticPrimitive
        (F z) (finiteComplexWeakLineDerivative F z Complex.I)

/-- Product-coordinate primitive error is the pullback of the complex
primitive error. -/
theorem finiteComplexWeakPrimitiveError_comp_complexOfRealProd
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ)
    (F : ℂ → ι → ℂ) (p : ℝ × ℝ) :
    finiteComplexWeakPrimitiveError
        (ρ ∘ complexOfRealProd) (F ∘ complexOfRealProd) p =
      finiteComplexWeakPrimitiveErrorComplex ρ F (complexOfRealProd p) := by
  unfold finiteComplexWeakPrimitiveError
    finiteComplexWeakPrimitiveErrorComplex
  rw [lineDeriv_comp_complexOfRealProd_one,
    lineDeriv_comp_complexOfRealProd_I,
    finiteComplexWeakLineDerivative_comp_complexOfRealProd_one,
    finiteComplexWeakLineDerivative_comp_complexOfRealProd_I]
  rfl

/-- Boundary action density on the imaginary axis with increasing imaginary
coordinate. -/
def finiteComplexWeakBoundaryActionDensityComplex
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ)
    (F : ℂ → ι → ℂ) (y : ℝ) : ℝ :=
  ρ (y * Complex.I) * standardComplexSymplecticPrimitive
    (F (y * Complex.I))
    (finiteComplexWeakLineDerivative
      (fun t : ℝ ↦ F (t * Complex.I)) y 1)

/-- The product-coordinate boundary density is the complex imaginary-axis
boundary density. -/
theorem finiteComplexWeakBoundaryActionDensity_comp_complexOfRealProd
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ)
    (F : ℂ → ι → ℂ) (y : ℝ) :
    finiteComplexWeakBoundaryActionDensity
        (ρ ∘ complexOfRealProd) (F ∘ complexOfRealProd) y =
      finiteComplexWeakBoundaryActionDensityComplex ρ F y := by
  simp [finiteComplexWeakBoundaryActionDensity,
    finiteComplexWeakBoundaryActionDensityComplex, Function.comp_def]

/-- **Localized Lipschitz weak Stokes on the complex right half-plane.**
The increasing imaginary-axis parametrization carries the displayed
outward-normal minus sign. -/
theorem integral_complexRightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    (∫ z in complexRightOpenHalfPlane,
        ρ z * finiteComplexWeakSymplecticDensityComplex F z) =
      (∫ z in complexRightOpenHalfPlane,
        finiteComplexWeakPrimitiveErrorComplex ρ F z) -
        ∫ y : ℝ, finiteComplexWeakBoundaryActionDensityComplex ρ F y := by
  let e : (ℝ × ℝ) ≃L[ℝ] ℂ := complexOfRealProd
  have hρe : LipschitzWith
      (Cρ * ‖e.toContinuousLinearMap‖₊) (ρ ∘ e) :=
    hρ.comp e.lipschitz
  have hFe : LipschitzWith
      (CF * ‖e.toContinuousLinearMap‖₊) (F ∘ e) :=
    hF.comp e.lipschitz
  have hρeCompact : HasCompactSupport (ρ ∘ e) :=
    hρCompact.comp_homeomorph e.toHomeomorph
  have hproduct :=
    integral_rightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq
      hρe hρeCompact hFe
  have hdensity :
      (∫ p in planarRightOpenHalfPlane,
          (ρ ∘ e) p *
            finiteComplexWeakSymplecticDensity (F ∘ e) p) =
        ∫ p in e ⁻¹' complexRightOpenHalfPlane,
          (fun z ↦ ρ z *
            finiteComplexWeakSymplecticDensityComplex F z) (e p) := by
    rw [preimage_complexRightOpenHalfPlane]
    apply setIntegral_congr_fun measurableSet_planarRightOpenHalfPlane
    intro p _hp
    change ρ (complexOfRealProd p) *
        finiteComplexWeakSymplecticDensity
          (F ∘ complexOfRealProd) p =
      ρ (complexOfRealProd p) *
        finiteComplexWeakSymplecticDensityComplex
          F (complexOfRealProd p)
    rw [finiteComplexWeakSymplecticDensity_comp_complexOfRealProd]
  have herror :
      (∫ p in planarRightOpenHalfPlane,
          finiteComplexWeakPrimitiveError (ρ ∘ e) (F ∘ e) p) =
        ∫ p in e ⁻¹' complexRightOpenHalfPlane,
          finiteComplexWeakPrimitiveErrorComplex ρ F (e p) := by
    rw [preimage_complexRightOpenHalfPlane]
    apply setIntegral_congr_fun measurableSet_planarRightOpenHalfPlane
    intro p _hp
    rw [finiteComplexWeakPrimitiveError_comp_complexOfRealProd]
  rw [hdensity, herror,
    setIntegral_comp_complexOfRealProd_preimage
      (fun z ↦ ρ z * finiteComplexWeakSymplecticDensityComplex F z)
      complexRightOpenHalfPlane,
    setIntegral_comp_complexOfRealProd_preimage
      (finiteComplexWeakPrimitiveErrorComplex ρ F)
      complexRightOpenHalfPlane] at hproduct
  simpa only [e,
    finiteComplexWeakBoundaryActionDensity_comp_complexOfRealProd] using hproduct

#print axioms lineDeriv_comp_complexOfRealProd_one
#print axioms lineDeriv_comp_complexOfRealProd_I
#print axioms setIntegral_comp_complexOfRealProd_preimage
#print axioms finiteComplexWeakSymplecticDensity_comp_complexOfRealProd
#print axioms finiteComplexWeakPrimitiveError_comp_complexOfRealProd
#print axioms finiteComplexWeakBoundaryActionDensity_comp_complexOfRealProd
#print axioms integral_complexRightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq

end

end GromovFilling
