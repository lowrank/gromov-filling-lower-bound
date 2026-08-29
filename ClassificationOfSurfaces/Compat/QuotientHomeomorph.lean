/-
Compatibility backport of the quotient-homeomorphism constructors added after
mathlib v4.29.0.  The definitions are from Mathlib.Topology.Homeomorph.Quotient
at mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.Topology.Homeomorph.Lemmas

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Quot

protected def congr {rX : X → X → Prop} {rY : Y → Y → Prop} (e : X ≃ₜ Y)
    (eq : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) : Quot rX ≃ₜ Quot rY where
  toEquiv := _root_.Quot.congr e eq
  continuous_toFun := continuous_quot_lift _ (continuous_quot_mk.comp e.continuous)
  continuous_invFun := continuous_quot_lift _ (continuous_quot_mk.comp e.symm.continuous)

protected def congrRight {r r' : X → X → Prop} (eq : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) :
    Quot r ≃ₜ Quot r' := Quot.congr (Homeomorph.refl X) eq

protected def congrLeft {r : X → X → Prop} (e : X ≃ₜ Y) :
    Quot r ≃ₜ Quot fun y₁ y₂ ↦ r (e.symm y₁) (e.symm y₂) :=
  Quot.congr e fun _ _ ↦ by simp only [e.symm_apply_apply]

end Quot

namespace Quotient

protected def congr {rX : Setoid X} {rY : Setoid Y} (e : X ≃ₜ Y)
    (eq : ∀ x₁ x₂, rX x₁ x₂ ↔ rY (e x₁) (e x₂)) :
    Quotient rX ≃ₜ Quotient rY := Quot.congr e eq

protected def congrRight {r r' : Setoid X}
    (eq : ∀ x₁ x₂, r x₁ x₂ ↔ r' x₁ x₂) : Quotient r ≃ₜ Quotient r' :=
  Quot.congrRight eq

end Quotient

end Homeomorph
