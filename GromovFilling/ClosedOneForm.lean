import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.Homotopy.Path

/-!
# Closed one-forms and path homotopy

This file packages the homotopy invariance of curve integrals of closed
`1`-forms in the exact form useful for future oriented-surface arguments.
The underlying analytic result is already in Mathlib for continuous-map
homotopies; here we specialize it to path homotopies with fixed endpoints,
so the vertical boundary terms vanish automatically.
-/

open Set
open scoped unitInterval

namespace GromovFilling

noncomputable section

section PathHomotopy

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  {x₀ x₁ : E} {γ₀ γ₁ : Path x₀ x₁}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Path.Homotopy.curveIntegral_evalAt_zero_eq_zero
    {ω : E → E →L[𝕜] F} (φ : γ₀.Homotopy γ₁) :
    ∫ᶜ x in φ.evalAt (0 : I), ω x = 0 := by
  rw [show φ.evalAt (0 : I) = (Path.refl x₀).cast γ₀.source γ₁.source by
    ext t
    simp [ContinuousMap.Homotopy.evalAt]]
  simp

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Path.Homotopy.curveIntegral_evalAt_one_eq_zero
    {ω : E → E →L[𝕜] F} (φ : γ₀.Homotopy γ₁) :
    ∫ᶜ x in φ.evalAt (1 : I), ω x = 0 := by
  rw [show φ.evalAt (1 : I) = (Path.refl x₁).cast γ₀.target γ₁.target by
    ext t
    simp [ContinuousMap.Homotopy.evalAt]]
  simp

/-- A closed `1`-form has the same curve integral along homotopic paths with
fixed endpoints. This is the path-level version of Mathlib's square-homotopy
identity, with the vertical edge integrals collapsing to zero because a path
homotopy fixes the endpoints. -/
theorem Path.Homotopy.curveIntegral_eq_of_hasFDerivWithinAt
    {t : Set E}
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : γ₀.Homotopy γ₁)
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
      (t := t) (ω := ω) (dω := dω) hφt hω hωc hdω_symm hcontdiff
  have h0 := Path.Homotopy.curveIntegral_evalAt_zero_eq_zero (ω := ω) φ
  have h1 := Path.Homotopy.curveIntegral_evalAt_one_eq_zero (ω := ω) φ
  calc
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x := by
      rw [h1, add_zero]
    _ = ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := h
    _ = ∫ᶜ x in γ₁, ω x := by
      rw [h0, add_zero]

/-- A closed `1`-form has the same curve integral along homotopic paths with
fixed endpoints. This `DiffContOnCl` version is convenient for chart-level
applications. -/
theorem Path.Homotopy.curveIntegral_eq_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    (φ : γ₀.Homotopy γ₁)
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
      (t := t) (ω := ω) hφt hω hdω_symm hcontdiff
  have h0 := Path.Homotopy.curveIntegral_evalAt_zero_eq_zero (ω := ω) φ
  have h1 := Path.Homotopy.curveIntegral_evalAt_one_eq_zero (ω := ω) φ
  calc
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x := by
      rw [h1, add_zero]
    _ = ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := h
    _ = ∫ᶜ x in γ₁, ω x := by
      rw [h0, add_zero]

/-- If a loop is nullhomotopic through a square on which a closed `1`-form is
defined, then its curve integral vanishes. -/
theorem Path.Homotopy.curveIntegral_eq_zero_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    {γ : Path x₀ x₀}
    (φ : γ.Homotopy (Path.refl x₀))
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ, ω x = 0 := by
  have h :=
    Path.Homotopy.curveIntegral_eq_of_diffContOnCl
      (γ₀ := γ) (γ₁ := Path.refl x₀) (t := t) (ω := ω)
      φ hφt hω hdω_symm hcontdiff
  simpa using h

end PathHomotopy

end

end GromovFilling
