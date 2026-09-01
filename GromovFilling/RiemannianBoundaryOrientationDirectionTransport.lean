import GromovFilling.RiemannianBoundaryOrientationLifts

/-!
# Transporting directions of local boundary lifts

Two real lifts of the same additive-circle map have the same strict direction
on an interval.  This remains true after precomposing one lift with a local
coordinate transition: a monotone transition preserves the direction and an
antitone transition reverses it.  The results are stated with `ContinuousOn`
because extended-chart transitions are only used on their controlled overlap.

This module is purely one-dimensional.  It is the order-theoretic adapter
between local chart-transition parity and the boundary-cover gluing layer.
-/

open Function Set
open scoped Topology

namespace GromovFilling

noncomputable section

/-- Two real lifts with the same circle projection have constant difference
on a closed interval, assuming only continuity on that interval. -/
theorem real_circle_lifts_sub_eq_on_Icc_of_continuousOn
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc a b))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    lift₁ x - lift₂ x = lift₁ y - lift₂ y := by
  letI : PreconnectedSpace (Set.Icc a b) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hcont₁ : Continuous (fun z : Set.Icc a b ↦ lift₁ z.1) := by
    exact hlift₁.restrict
  have hcont₂ : Continuous (fun z : Set.Icc a b ↦ lift₂ z.1) := by
    exact hlift₂.restrict
  simpa using
    (real_circle_lifts_difference_eq
      (fun z : Set.Icc a b ↦ lift₁ z.1)
      (fun z : Set.Icc a b ↦ lift₂ z.1)
      hcont₁ hcont₂
      (fun z ↦ hproject z.1 z.2)
      ⟨x, hx⟩ ⟨y, hy⟩)

/-- Replacing a continuous-on-interval real lift by another lift of the
same circle map preserves strict increase. -/
theorem strictMonoOn_of_continuousOn_real_circle_lifts_on_Icc
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc a b))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    (hmono : StrictMonoOn lift₂ (Set.Icc a b)) :
    StrictMonoOn lift₁ (Set.Icc a b) := by
  intro x hx y hy hxy
  have hconstant : lift₁ x - lift₂ x = lift₁ y - lift₂ y :=
    real_circle_lifts_sub_eq_on_Icc_of_continuousOn
      hlift₁ hlift₂ hproject hx hy
  have hlt : lift₂ x < lift₂ y := hmono hx hy hxy
  linarith

/-- Replacing a continuous-on-interval real lift by another lift of the
same circle map preserves strict decrease. -/
theorem strictAntiOn_of_continuousOn_real_circle_lifts_on_Icc
    {a b : ℝ} {lift₁ lift₂ : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc a b))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ y : ℝ) : UnitAddCircle))
    (hanti : StrictAntiOn lift₂ (Set.Icc a b)) :
    StrictAntiOn lift₁ (Set.Icc a b) := by
  intro x hx y hy hxy
  have hconstant : lift₁ x - lift₂ x = lift₁ y - lift₂ y :=
    real_circle_lifts_sub_eq_on_Icc_of_continuousOn
      hlift₁ hlift₂ hproject hx hy
  have hlt : lift₂ y < lift₂ x := hanti hx hy hxy
  linarith

/-- A strictly increasing local coordinate transition preserves the increasing
direction of a projected real lift. -/
theorem strictMonoOn_of_projected_real_lifts_comp_strictMonoOn
    {a b c d : ℝ} {lift₁ lift₂ transition : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc c d))
    (htransitionContinuous : ContinuousOn transition (Set.Icc a b))
    (htransitionMaps : Set.MapsTo transition (Set.Icc a b) (Set.Icc c d))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ (transition y) : ℝ) : UnitAddCircle))
    (htransition : StrictMonoOn transition (Set.Icc a b))
    (hlift₂Direction : StrictMonoOn lift₂ (Set.Icc c d)) :
    StrictMonoOn lift₁ (Set.Icc a b) := by
  apply strictMonoOn_of_continuousOn_real_circle_lifts_on_Icc hlift₁
    (hlift₂.comp htransitionContinuous htransitionMaps)
  · intro y hy
    simpa only [Function.comp_apply] using hproject y hy
  · exact hlift₂Direction.comp htransition htransitionMaps

/-- A strictly increasing local coordinate transition preserves the decreasing
direction of a projected real lift. -/
theorem strictAntiOn_of_projected_real_lifts_comp_strictMonoOn
    {a b c d : ℝ} {lift₁ lift₂ transition : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc c d))
    (htransitionContinuous : ContinuousOn transition (Set.Icc a b))
    (htransitionMaps : Set.MapsTo transition (Set.Icc a b) (Set.Icc c d))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ (transition y) : ℝ) : UnitAddCircle))
    (htransition : StrictMonoOn transition (Set.Icc a b))
    (hlift₂Direction : StrictAntiOn lift₂ (Set.Icc c d)) :
    StrictAntiOn lift₁ (Set.Icc a b) := by
  apply strictAntiOn_of_continuousOn_real_circle_lifts_on_Icc hlift₁
    (hlift₂.comp htransitionContinuous htransitionMaps)
  · intro y hy
    simpa only [Function.comp_apply] using hproject y hy
  · exact hlift₂Direction.comp_strictMonoOn htransition htransitionMaps

/-- A strictly decreasing local coordinate transition reverses an increasing
direction of a projected real lift. -/
theorem strictAntiOn_of_projected_real_lifts_comp_strictAntiOn
    {a b c d : ℝ} {lift₁ lift₂ transition : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc c d))
    (htransitionContinuous : ContinuousOn transition (Set.Icc a b))
    (htransitionMaps : Set.MapsTo transition (Set.Icc a b) (Set.Icc c d))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ (transition y) : ℝ) : UnitAddCircle))
    (htransition : StrictAntiOn transition (Set.Icc a b))
    (hlift₂Direction : StrictMonoOn lift₂ (Set.Icc c d)) :
    StrictAntiOn lift₁ (Set.Icc a b) := by
  apply strictAntiOn_of_continuousOn_real_circle_lifts_on_Icc hlift₁
    (hlift₂.comp htransitionContinuous htransitionMaps)
  · intro y hy
    simpa only [Function.comp_apply] using hproject y hy
  · exact hlift₂Direction.comp_strictAntiOn htransition htransitionMaps

/-- A strictly decreasing local coordinate transition reverses a decreasing
direction of a projected real lift. -/
theorem strictMonoOn_of_projected_real_lifts_comp_strictAntiOn
    {a b c d : ℝ} {lift₁ lift₂ transition : ℝ → ℝ}
    (hlift₁ : ContinuousOn lift₁ (Set.Icc a b))
    (hlift₂ : ContinuousOn lift₂ (Set.Icc c d))
    (htransitionContinuous : ContinuousOn transition (Set.Icc a b))
    (htransitionMaps : Set.MapsTo transition (Set.Icc a b) (Set.Icc c d))
    (hproject : ∀ y ∈ Set.Icc a b,
      ((lift₁ y : ℝ) : UnitAddCircle) =
        ((lift₂ (transition y) : ℝ) : UnitAddCircle))
    (htransition : StrictAntiOn transition (Set.Icc a b))
    (hlift₂Direction : StrictAntiOn lift₂ (Set.Icc c d)) :
    StrictMonoOn lift₁ (Set.Icc a b) := by
  apply strictMonoOn_of_continuousOn_real_circle_lifts_on_Icc hlift₁
    (hlift₂.comp htransitionContinuous htransitionMaps)
  · intro y hy
    simpa only [Function.comp_apply] using hproject y hy
  · exact hlift₂Direction.comp htransition htransitionMaps

#print axioms real_circle_lifts_sub_eq_on_Icc_of_continuousOn
#print axioms strictMonoOn_of_continuousOn_real_circle_lifts_on_Icc
#print axioms strictAntiOn_of_continuousOn_real_circle_lifts_on_Icc
#print axioms strictMonoOn_of_projected_real_lifts_comp_strictMonoOn
#print axioms strictAntiOn_of_projected_real_lifts_comp_strictMonoOn
#print axioms strictAntiOn_of_projected_real_lifts_comp_strictAntiOn
#print axioms strictMonoOn_of_projected_real_lifts_comp_strictAntiOn

end

end GromovFilling
