/-
Compatibility backports for finite powersets added after mathlib v4.29.0.
The declarations below are adapted from Mathlib.Data.Finset.Powerset at
mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.Data.Finset.Powerset

namespace Finset

variable {α : Type*} {s : Finset α}

lemma powersetCard_biUnion [DecidableEq α] {r : ℕ}
    (hr : r ≠ 0) (hrs : r ≤ #s) : (s.powersetCard r).biUnion id = s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [← sup_eq_biUnion]
  exact powersetCard_sup _ _ hrs

lemma eq_of_powersetCard_eq {a b : Finset α} {r : ℕ}
    (hab : #a = #b) (hr₀ : r ≠ 0) (hra : r ≤ #a)
    (h : a.powersetCard r = b.powersetCard r) : a = b := by
  classical
  simpa [powersetCard_biUnion hr₀, ← hab, hra] using congr(($h).biUnion id)

end Finset
