import GromovFilling.FiniteSymplecticWeakStokes
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Signed chart transitions for finite symplectic densities

The Riemannian area machinery uses absolute Jacobians and therefore does not
record chart orientation.  Stokes requires the signed counterpart.  This
file proves the two-dimensional determinant law for the finite standard
complex symplectic density and derives its change-of-variables formula under
orientation-preserving planar coordinate changes.

These results are local.  They provide the overlap identity needed to glue
oriented chart contributions, but do not themselves construct an oriented
atlas or prove the global manifold-with-boundary Stokes theorem.
-/

open Function MeasureTheory Set
open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The real determinant of a complex-plane endomorphism is the signed
Jacobian of the images of the standard oriented basis `(1, I)`. -/
theorem det_eq_complex_orientedJacobian (T : ℂ →L[ℝ] ℂ) :
    T.det =
      (T 1).re * (T Complex.I).im -
        (T 1).im * (T Complex.I).re := by
  change LinearMap.det T.toLinearMap = _
  rw [show LinearMap.det T.toLinearMap =
      (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        T.toLinearMap).det from
    (LinearMap.det_toMatrix Complex.basisOneI T.toLinearMap).symm]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr]
  congr 1
  rw [mul_comm]
  change (T 1).im * (T Complex.I).re =
    (T 1).im * (T Complex.I).re
  rfl

/-- Pulling a finite standard complex symplectic form back through a real
linear endomorphism of the plane multiplies it by the signed determinant. -/
theorem standardComplexSymplectic_comp_eq_det_mul
    {ι : Type*} [Fintype ι]
    (L : ℂ →L[ℝ] (ι → ℂ)) (T : ℂ →L[ℝ] ℂ) :
    standardComplexSymplectic (L (T 1)) (L (T Complex.I)) =
      T.det * standardComplexSymplectic (L 1) (L Complex.I) := by
  have hT1 : T 1 =
      (T 1).re • (1 : ℂ) + (T 1).im • Complex.I := by
    rw [← Complex.re_add_im (T 1)]
    simp
  have hTI : T Complex.I =
      (T Complex.I).re • (1 : ℂ) +
        (T Complex.I).im • Complex.I := by
    rw [← Complex.re_add_im (T Complex.I)]
    simp
  have hself (p : ι → ℂ) : standardComplexSymplectic p p = 0 := by
    linarith [standardComplexSymplectic_swap p p]
  rw [hT1, hTI, map_add, map_add, map_smul, map_smul, map_smul,
    map_smul, det_eq_complex_orientedJacobian]
  change standardComplexSymplecticBilinear
      ((T 1).re • L 1 + (T 1).im • L Complex.I)
      ((T Complex.I).re • L 1 + (T Complex.I).im • L Complex.I) = _
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    standardComplexSymplecticBilinear_apply]
  rw [hself, hself, standardComplexSymplectic_swap]
  ring

/-- The signed finite symplectic density of the two columns of the Fréchet
derivative in the standard oriented complex basis. -/
def finiteSymplecticFDerivDensity
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (z : ℂ) : ℝ :=
  standardComplexSymplectic
    ((fderiv ℝ F z) 1) ((fderiv ℝ F z) Complex.I)

/-- The signed finite symplectic derivative density obeys the determinant
chain rule under a differentiable planar coordinate change. -/
theorem finiteSymplecticFDerivDensity_comp
    {ι : Type*} [Fintype ι] (F : ℂ → ι → ℂ) (e : ℂ → ℂ) (z : ℂ)
    (hF : DifferentiableAt ℝ F (e z)) (he : DifferentiableAt ℝ e z) :
    finiteSymplecticFDerivDensity (F ∘ e) z =
      (fderiv ℝ e z).det * finiteSymplecticFDerivDensity F (e z) := by
  unfold finiteSymplecticFDerivDensity
  rw [fderiv_comp z hF he]
  simp only [ContinuousLinearMap.comp_apply]
  exact standardComplexSymplectic_comp_eq_det_mul
    (fderiv ℝ F (e z)) (fderiv ℝ e z)

/-- Signed change of variables for the finite symplectic derivative density
under an injective orientation-preserving planar chart transition. -/
theorem integral_finiteSymplecticFDerivDensity_comp
    {ι : Type*} [Fintype ι]
    (F : ℂ → ι → ℂ) (e : ℂ → ℂ) (s : Set ℂ)
    (hs : MeasurableSet s)
    (he : ∀ z ∈ s, DifferentiableAt ℝ e z)
    (heInj : Set.InjOn e s)
    (heOrientation : ∀ z ∈ s, 0 ≤ (fderiv ℝ e z).det)
    (hF : ∀ z ∈ s, DifferentiableAt ℝ F (e z)) :
    ∫ z in s, finiteSymplecticFDerivDensity (F ∘ e) z =
      ∫ w in e '' s, finiteSymplecticFDerivDensity F w := by
  calc
    ∫ z in s, finiteSymplecticFDerivDensity (F ∘ e) z =
        ∫ z in s,
          (fderiv ℝ e z).det * finiteSymplecticFDerivDensity F (e z) := by
      apply setIntegral_congr_fun hs
      intro z hz
      exact finiteSymplecticFDerivDensity_comp F e z (hF z hz) (he z hz)
    _ = ∫ z in s,
          |(fderiv ℝ e z).det| • finiteSymplecticFDerivDensity F (e z) := by
      apply setIntegral_congr_fun hs
      intro z hz
      dsimp only
      rw [abs_of_nonneg (heOrientation z hz), smul_eq_mul]
    _ = ∫ w in e '' s, finiteSymplecticFDerivDensity F w := by
      symm
      exact integral_image_eq_integral_abs_det_fderiv_smul volume hs
        (fun z hz ↦ (he z hz).hasFDerivAt.hasFDerivWithinAt)
        heInj (finiteSymplecticFDerivDensity F)

#print axioms det_eq_complex_orientedJacobian
#print axioms standardComplexSymplectic_comp_eq_det_mul
#print axioms finiteSymplecticFDerivDensity_comp
#print axioms integral_finiteSymplecticFDerivDensity_comp

end

end GromovFilling
