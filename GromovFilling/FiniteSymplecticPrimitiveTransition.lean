import GromovFilling.ComplexHalfPlaneWeakStokes
import GromovFilling.FiniteSymplecticChartTransition

/-!
# Signed chart transitions for the finite symplectic primitive error

The localized weak-Stokes identity contains, besides the pulled-back
symplectic density, the wedge of the cutoff differential with the standard
symplectic primitive.  This module proves that this primitive-error density
obeys the same signed determinant law as the symplectic density itself.

The result is the coordinate-invariance needed to cancel partition-of-unity
derivative terms on overlaps of an oriented surface atlas.
-/

open Function MeasureTheory Set

namespace GromovFilling

noncomputable section

/-- The alternating pairing of two real covectors on the complex plane
transforms by the signed determinant.  The order is chosen to match the
cutoff-primitive error in localized weak Stokes. -/
theorem alternatingContinuousLinearPair_comp_eq_det_mul
    (a b : ℂ →L[ℝ] ℝ) (T : ℂ →L[ℝ] ℂ) :
    a (T Complex.I) * b (T 1) - a (T 1) * b (T Complex.I) =
      T.det * (a Complex.I * b 1 - a 1 * b Complex.I) := by
  have hT1 : T 1 =
      (T 1).re • (1 : ℂ) + (T 1).im • Complex.I := by
    rw [← Complex.re_add_im (T 1)]
    simp
  have hTI : T Complex.I =
      (T Complex.I).re • (1 : ℂ) +
        (T Complex.I).im • Complex.I := by
    rw [← Complex.re_add_im (T Complex.I)]
    simp
  rw [hT1, hTI, map_add, map_add, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    map_smul, map_smul, map_smul, map_smul,
    det_eq_complex_orientedJacobian]
  simp only [smul_eq_mul]
  ring

/-- The Fréchet-derivative version of the cutoff differential wedged with
the finite standard symplectic primitive in the positive complex frame. -/
def finiteSymplecticFDerivPrimitiveError
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ)
    (F : ℂ → ι → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ ρ z) Complex.I *
      standardComplexSymplecticPrimitive (F z) ((fderiv ℝ F z) 1) -
    (fderiv ℝ ρ z) 1 *
      standardComplexSymplecticPrimitive
        (F z) ((fderiv ℝ F z) Complex.I)

/-- The Fréchet primitive-error density obeys the signed determinant chain
rule under a differentiable planar coordinate change. -/
theorem finiteSymplecticFDerivPrimitiveError_comp
    {ι : Type*} [Fintype ι]
    (ρ : ℂ → ℝ) (F : ℂ → ι → ℂ) (e : ℂ → ℂ) (z : ℂ)
    (hρ : DifferentiableAt ℝ ρ (e z))
    (hF : DifferentiableAt ℝ F (e z))
    (he : DifferentiableAt ℝ e z) :
    finiteSymplecticFDerivPrimitiveError (ρ ∘ e) (F ∘ e) z =
      (fderiv ℝ e z).det *
        finiteSymplecticFDerivPrimitiveError ρ F (e z) := by
  unfold finiteSymplecticFDerivPrimitiveError
  rw [fderiv_comp z hρ he, fderiv_comp z hF he]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  exact alternatingContinuousLinearPair_comp_eq_det_mul
    (fderiv ℝ ρ (e z))
    ((standardComplexSymplecticPrimitive (F (e z))).comp
      (fderiv ℝ F (e z)))
    (fderiv ℝ e z)

/-- At a common differentiability point, the Rademacher primitive-error
density agrees with its Fréchet-derivative expression. -/
theorem finiteComplexWeakPrimitiveErrorComplex_eq_fderiv
    {ι : Type*} [Fintype ι]
    (ρ : ℂ → ℝ) (F : ℂ → ι → ℂ) (z : ℂ)
    (hρ : DifferentiableAt ℝ ρ z) (hF : DifferentiableAt ℝ F z) :
    finiteComplexWeakPrimitiveErrorComplex ρ F z =
      finiteSymplecticFDerivPrimitiveError ρ F z := by
  unfold finiteComplexWeakPrimitiveErrorComplex
    finiteSymplecticFDerivPrimitiveError
  rw [hρ.lineDeriv_eq_fderiv (v := Complex.I),
    hρ.lineDeriv_eq_fderiv (v := (1 : ℂ)),
    finiteComplexWeakLineDerivative_eq_lineDeriv F hF 1,
    finiteComplexWeakLineDerivative_eq_lineDeriv F hF Complex.I,
    hF.lineDeriv_eq_fderiv, hF.lineDeriv_eq_fderiv]

/-- At a differentiability point, the weak complex symplectic density is
the ordinary Fréchet pullback density. -/
theorem finiteComplexWeakSymplecticDensityComplex_eq_fderiv
    {ι : Type*} [Fintype ι]
    (F : ℂ → ι → ℂ) (z : ℂ) (hF : DifferentiableAt ℝ F z) :
    finiteComplexWeakSymplecticDensityComplex F z =
      finiteSymplecticFDerivDensity F z := by
  unfold finiteComplexWeakSymplecticDensityComplex
    finiteSymplecticFDerivDensity
  rw [finiteComplexWeakLineDerivative_eq_lineDeriv F hF 1,
    finiteComplexWeakLineDerivative_eq_lineDeriv F hF Complex.I,
    hF.lineDeriv_eq_fderiv, hF.lineDeriv_eq_fderiv]

/-- The complex half-plane weak-Stokes theorem in Fréchet-density form.
Only the one-dimensional boundary trace remains expressed through its
Rademacher derivative, which is the natural regularity of a Lipschitz trace. -/
theorem integral_complexRightHalfPlane_cutoff_mul_finiteSymplecticFDerivDensity_eq
    {ι : Type*} [Fintype ι]
    {ρ : ℂ → ℝ} {F : ℂ → ι → ℂ}
    {Cρ CF : ℝ≥0} (hρ : LipschitzWith Cρ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F) :
    (∫ z in complexRightOpenHalfPlane,
        ρ z * finiteSymplecticFDerivDensity F z) =
      (∫ z in complexRightOpenHalfPlane,
        finiteSymplecticFDerivPrimitiveError ρ F z) -
        ∫ y : ℝ, finiteComplexWeakBoundaryActionDensityComplex ρ F y := by
  have hFae : ∀ᵐ z ∂(volume.restrict complexRightOpenHalfPlane),
      DifferentiableAt ℝ F z :=
    ae_restrict_of_ae (hF.ae_differentiableAt (μ := volume))
  have hρae : ∀ᵐ z ∂(volume.restrict complexRightOpenHalfPlane),
      DifferentiableAt ℝ ρ z :=
    ae_restrict_of_ae (hρ.ae_differentiableAt (μ := volume))
  have hdensity :
      (∫ z in complexRightOpenHalfPlane,
          ρ z * finiteComplexWeakSymplecticDensityComplex F z) =
        ∫ z in complexRightOpenHalfPlane,
          ρ z * finiteSymplecticFDerivDensity F z := by
    apply setIntegral_congr_ae
    filter_upwards [hFae] with z hz
    rw [finiteComplexWeakSymplecticDensityComplex_eq_fderiv F z hz]
  have herror :
      (∫ z in complexRightOpenHalfPlane,
          finiteComplexWeakPrimitiveErrorComplex ρ F z) =
        ∫ z in complexRightOpenHalfPlane,
          finiteSymplecticFDerivPrimitiveError ρ F z := by
    apply setIntegral_congr_ae
    filter_upwards [hρae, hFae] with z hρz hFz
    exact finiteComplexWeakPrimitiveErrorComplex_eq_fderiv
      ρ F z hρz hFz
  calc
    (∫ z in complexRightOpenHalfPlane,
        ρ z * finiteSymplecticFDerivDensity F z) =
        ∫ z in complexRightOpenHalfPlane,
          ρ z * finiteComplexWeakSymplecticDensityComplex F z :=
      hdensity.symm
    _ = (∫ z in complexRightOpenHalfPlane,
          finiteComplexWeakPrimitiveErrorComplex ρ F z) -
        ∫ y : ℝ, finiteComplexWeakBoundaryActionDensityComplex ρ F y :=
      integral_complexRightHalfPlane_cutoff_mul_finiteComplexWeakSymplecticDensity_eq
        hρ hρCompact hF
    _ = (∫ z in complexRightOpenHalfPlane,
          finiteSymplecticFDerivPrimitiveError ρ F z) -
        ∫ y : ℝ, finiteComplexWeakBoundaryActionDensityComplex ρ F y := by
      rw [herror]

/-- The weak primitive-error density therefore has the signed determinant
law wherever the cutoff, map, and coordinate change are differentiable. -/
theorem finiteComplexWeakPrimitiveErrorComplex_comp
    {ι : Type*} [Fintype ι]
    (ρ : ℂ → ℝ) (F : ℂ → ι → ℂ) (e : ℂ → ℂ) (z : ℂ)
    (hρ : DifferentiableAt ℝ ρ (e z))
    (hF : DifferentiableAt ℝ F (e z))
    (he : DifferentiableAt ℝ e z) :
    finiteComplexWeakPrimitiveErrorComplex (ρ ∘ e) (F ∘ e) z =
      (fderiv ℝ e z).det *
        finiteComplexWeakPrimitiveErrorComplex ρ F (e z) := by
  rw [finiteComplexWeakPrimitiveErrorComplex_eq_fderiv
      (ρ ∘ e) (F ∘ e) z (hρ.comp z he) (hF.comp z he),
    finiteComplexWeakPrimitiveErrorComplex_eq_fderiv ρ F (e z) hρ hF]
  exact finiteSymplecticFDerivPrimitiveError_comp ρ F e z hρ hF he

/-- Signed change of variables for the Fréchet primitive-error density under
an injective orientation-preserving planar transition. -/
theorem integral_finiteSymplecticFDerivPrimitiveError_comp
    {ι : Type*} [Fintype ι]
    (ρ : ℂ → ℝ) (F : ℂ → ι → ℂ) (e : ℂ → ℂ) (s : Set ℂ)
    (hs : MeasurableSet s)
    (he : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (heOrientation : ∀ z ∈ s, 0 ≤ (fderiv ℝ e z).det)
    (hρ : ∀ z ∈ s, DifferentiableAt ℝ ρ (e z))
    (hF : ∀ z ∈ s, DifferentiableAt ℝ F (e z)) :
    ∫ z in s, finiteSymplecticFDerivPrimitiveError (ρ ∘ e) (F ∘ e) z =
      ∫ w in e '' s, finiteSymplecticFDerivPrimitiveError ρ F w := by
  calc
    ∫ z in s, finiteSymplecticFDerivPrimitiveError (ρ ∘ e) (F ∘ e) z =
        ∫ z in s, (fderiv ℝ e z).det *
          finiteSymplecticFDerivPrimitiveError ρ F (e z) := by
      apply setIntegral_congr_fun hs
      intro z hz
      exact finiteSymplecticFDerivPrimitiveError_comp
        ρ F e z (hρ z hz) (hF z hz) (he z hz)
    _ = ∫ z in s, |(fderiv ℝ e z).det| •
          finiteSymplecticFDerivPrimitiveError ρ F (e z) := by
      apply setIntegral_congr_fun hs
      intro z hz
      dsimp only
      rw [abs_of_nonneg (heOrientation z hz), smul_eq_mul]
    _ = ∫ w in e '' s, finiteSymplecticFDerivPrimitiveError ρ F w := by
      symm
      exact integral_image_eq_integral_abs_det_fderiv_smul volume hs
        (fun z hz ↦ (he z hz).hasFDerivAt.hasFDerivWithinAt)
        heInj (finiteSymplecticFDerivPrimitiveError ρ F)

#print axioms alternatingContinuousLinearPair_comp_eq_det_mul
#print axioms finiteSymplecticFDerivPrimitiveError_comp
#print axioms finiteComplexWeakPrimitiveErrorComplex_eq_fderiv
#print axioms finiteComplexWeakSymplecticDensityComplex_eq_fderiv
#print axioms integral_complexRightHalfPlane_cutoff_mul_finiteSymplecticFDerivDensity_eq
#print axioms finiteComplexWeakPrimitiveErrorComplex_comp
#print axioms integral_finiteSymplecticFDerivPrimitiveError_comp

end

end GromovFilling
