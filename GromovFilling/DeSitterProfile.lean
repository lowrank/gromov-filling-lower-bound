import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# De Sitter identities for distance profiles

This module verifies the algebraic content of Proposition 15.1 in
`fourier_resonant_filling_area_v3.tex`.  The profile value is kept as an
explicit scalar, so every denominator condition is visible and the identities
can later be composed with an almost-everywhere differentiability theorem.
-/

namespace GromovFilling

/-- Three-dimensional Minkowski space with signature `(2, 1)`, represented
without adding a global inner-product-space instance of indefinite signature. -/
structure Lorentz3 where
  x₁ : ℝ
  x₂ : ℝ
  x₃ : ℝ
  deriving Repr

/-- The Lorentz bilinear form of signature `(2, 1)`. -/
def lorentzInner (x y : Lorentz3) : ℝ :=
  x.x₁ * y.x₁ + x.x₂ * y.x₂ - x.x₃ * y.x₃

/-- The de Sitter point associated with angle `α` and profile value `u`.
The third coordinate is written as `cos u / sin u`, i.e. `cot u`. -/
def deSitterProfilePoint (α u : ℝ) : Lorentz3 where
  x₁ := Real.cos α / Real.sin u
  x₂ := Real.sin α / Real.sin u
  x₃ := Real.cos u / Real.sin u

/-- The formal derivative of `deSitterProfilePoint α (f α)` when the profile
derivative at `α` is `du`. -/
def deSitterProfileVelocity (α u du : ℝ) : Lorentz3 where
  x₁ := -Real.sin α / Real.sin u -
    Real.cos α * Real.cos u * du / Real.sin u ^ 2
  x₂ := Real.cos α / Real.sin u -
    Real.sin α * Real.cos u * du / Real.sin u ^ 2
  x₃ := -du / Real.sin u ^ 2

/-- The coefficient kernel intended by `p_{α,β}(f)` in Proposition 15.1. -/
def zustCoefficientKernel (α β u v : ℝ) : ℝ :=
  (1 - Real.cos (β - α) ^ 2 - Real.cos u ^ 2 - Real.cos v ^ 2 +
      2 * Real.cos u * Real.cos v * Real.cos (β - α)) /
    (Real.sin (β - α) ^ 2 * Real.sin u ^ 2 * Real.sin v ^ 2)

/-- Every profile point lies on the unit de Sitter quadric. -/
theorem lorentzInner_deSitterProfilePoint_self
    (α u : ℝ) (hu : Real.sin u ≠ 0) :
    lorentzInner (deSitterProfilePoint α u)
      (deSitterProfilePoint α u) = 1 := by
  unfold lorentzInner deSitterProfilePoint
  dsimp
  field_simp [hu]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq u]

/-- Lorentz speed of the formal profile derivative. -/
theorem lorentzInner_deSitterProfileVelocity_self
    (α u du : ℝ) (hu : Real.sin u ≠ 0) :
    lorentzInner (deSitterProfileVelocity α u du)
      (deSitterProfileVelocity α u du) =
        (1 - du ^ 2) / Real.sin u ^ 2 := by
  unfold lorentzInner deSitterProfileVelocity
  dsimp
  field_simp [hu]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq u]

/-- Exact Lorentz inner product of two profile points. -/
theorem lorentzInner_deSitterProfilePoint
    (α β u v : ℝ) (hu : Real.sin u ≠ 0) (hv : Real.sin v ≠ 0) :
    lorentzInner (deSitterProfilePoint α u)
        (deSitterProfilePoint β v) =
      (Real.cos (β - α) - Real.cos u * Real.cos v) /
        (Real.sin u * Real.sin v) := by
  unfold lorentzInner deSitterProfilePoint
  dsimp
  field_simp [hu, hv]
  rw [Real.cos_sub]
  ring

/-- Züst's coefficient kernel is the normalized Lorentz chord distortion. -/
theorem zustCoefficientKernel_eq_lorentz
    (α β u v : ℝ)
    (hu : Real.sin u ≠ 0) (hv : Real.sin v ≠ 0)
    (hd : Real.sin (β - α) ≠ 0) :
    zustCoefficientKernel α β u v =
      (1 - lorentzInner (deSitterProfilePoint α u)
        (deSitterProfilePoint β v) ^ 2) /
          Real.sin (β - α) ^ 2 := by
  rw [lorentzInner_deSitterProfilePoint α β u v hu hv]
  unfold zustCoefficientKernel
  field_simp [hu, hv, hd]
  ring

end GromovFilling
