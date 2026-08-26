import GromovFilling.ModTwoDegree

/-!
# Radial projection away from an omitted point

This is the continuous first step of Lemma 5.4.  If a planar map omits a
point, normalization about that point gives a continuous circle-valued map
extending the normalized boundary curve.
-/

namespace GromovFilling

noncomputable section

/-- The plane punctured at `y`. -/
abbrev PuncturedPlane (y : ℂ) := {z : ℂ // z ≠ y}

/-- Normalize a point of the punctured plane onto the unit circle centered
at the puncture. -/
def radialProjection (y : ℂ) (z : PuncturedPlane y) : ComplexUnitCircle := by
  refine ⟨(z.1 - y) / (‖z.1 - y‖ : ℂ), ?_⟩
  have hnorm : ‖z.1 - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr z.2)), div_self hnorm]

theorem continuous_radialProjection (y : ℂ) : Continuous (radialProjection y) := by
  apply Continuous.subtype_mk
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z hz
    have hnorm : ‖z.1 - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)
    apply hnorm
    exact_mod_cast hz

/-- Radial projection of a map which omits `y`. -/
def radialMap {X : Type*} (G : X → ℂ) (y : ℂ)
    (havoid : ∀ x, G x ≠ y) : X → ComplexUnitCircle := fun x ↦
  radialProjection y ⟨G x, havoid x⟩

theorem continuous_radialMap {X : Type*} [TopologicalSpace X]
    (G : X → ℂ) (y : ℂ) (havoid : ∀ x, G x ≠ y)
    (hG : Continuous G) : Continuous (radialMap G y havoid) := by
  apply (continuous_radialProjection y).comp
  exact hG.subtype_mk havoid

/-- A point omitted by `G` would produce a circle-valued extension of the
radially projected boundary.  Thus any obstruction to such an extension
forces the point into the image. -/
theorem mem_range_of_no_radial_extension
    {X B : Type*} [TopologicalSpace X]
    (boundary : B → X) (G : X → ℂ) (y : ℂ) (hG : Continuous G)
    (hboundary : ∀ b, G (boundary b) ≠ y)
    (hno : ¬ ∃ (H : X → ComplexUnitCircle), Continuous H ∧
      ∀ b : B, H (boundary b) =
        radialProjection y ⟨G (boundary b), hboundary b⟩) :
    y ∈ Set.range G := by
  by_contra hy
  have havoid : ∀ x, G x ≠ y := by
    exact fun x hx ↦ hy ⟨x, hx⟩
  apply hno
  refine ⟨radialMap G y havoid, continuous_radialMap G y havoid hG, ?_⟩
  intro b
  rfl

end

end GromovFilling
