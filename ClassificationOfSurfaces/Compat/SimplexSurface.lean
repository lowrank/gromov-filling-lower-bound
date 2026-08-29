/-
Compatibility backport for the simplex-surface decomposition API added after
mathlib v4.29.0. The declarations below are adapted from
Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic at mathlib commit
81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

noncomputable section

open Finset Function Module
open scoped Affine

namespace Affine
namespace Simplex

variable {k V P : Type*}
variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

section PartialOrder

variable [PartialOrder k]

theorem closedInterior_face_subset_closedInterior [ZeroLEOneClass k] {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) :
    (s.face h).closedInterior ⊆ s.closedInterior := by
  intro p hp
  have hp' : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hp <|
      (s.face h).closedInterior_subset_affineSpan.trans <|
        affineSpan_mono k <| by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i ∈ fs <;> aesop

@[simp]
theorem point_mem_closedInterior_face_iff [Nontrivial k] [ZeroLEOneClass k]
    {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) {j : Fin (n + 1)} :
    s.points j ∈ (s.face h).closedInterior ↔ j ∈ fs := by
  refine ⟨fun hj ↦ ?_, fun hfs ↦ ?_⟩
  · suffices s.points j ∈ affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
  · obtain ⟨i, rfl⟩ : ∃ i, fs.orderEmbOfFin h i = j :=
      range_orderEmbOfFin fs h |>.ge hfs
    exact point_mem_closedInterior _ _

theorem closedInterior_face_ssubset_closedInterior [Nontrivial k]
    [ZeroLEOneClass k] {n : ℕ} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ) {m : ℕ}
    (h : #fs = m + 1) :
    (s.face h).closedInterior ⊂ s.closedInterior := by
  obtain ⟨a, ha⟩ := Classical.not_forall.mp <| Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a,
    fun hs ↦ ha (by simpa using hs)⟩

theorem disjoint_interior_closedInterior_face {n : ℕ}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs ≠ .univ)
    {m : ℕ} (h : #fs = m + 1) :
    Disjoint s.interior (s.face h).closedInterior := by
  refine Set.disjoint_left.mpr fun p hleft hright ↦ ?_
  have hp : p ∈ affineSpan k (Set.range s.points) :=
    Set.mem_of_mem_of_subset hleft <| s.interior_subset_closedInterior.trans <|
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff,
    affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]
theorem point_mem_closedInterior_faceOpposite_iff [Nontrivial k]
    [ZeroLEOneClass k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    {i j : Fin (n + 1)} :
    s.points j ∈ (s.faceOpposite i).closedInterior ↔ j ≠ i := by
  simp [faceOpposite]

theorem closedInterior_faceOpposite_subset_closedInterior [ZeroLEOneClass k]
    {n : ℕ} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊆ s.closedInterior :=
  s.closedInterior_face_subset_closedInterior _

theorem closedInterior_faceOpposite_ssubset_closedInterior [Nontrivial k]
    [ZeroLEOneClass k] {n : ℕ} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊂ s.closedInterior :=
  s.closedInterior_face_ssubset_closedInterior (by simp) _

theorem disjoint_interior_closedInterior_faceOpposite {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Disjoint s.interior (s.faceOpposite i).closedInterior :=
  s.disjoint_interior_closedInterior_face (by simp) _

end PartialOrder

section LinearOrder

variable [LinearOrder k]

/-- The closed interior is the union of the open interior and the surface. -/
theorem closedInterior_eq_interior_union [IsOrderedAddMonoid k]
    [ZeroLEOneClass k] {n : ℕ} [NeZero n] (s : Simplex k P n) :
    s.closedInterior =
      s.interior ∪ ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union, or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1,
          ← Finset.sum_erase_add _ _ (show i ∈ Finset.univ by simp),
          add_eq_right,
          Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite,
      affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ ↦ hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior
      (Set.iUnion_subset fun i ↦ ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i

theorem closedInterior_sdiff_interior [IsOrderedAddMonoid k]
    [ZeroLEOneClass k] {n : ℕ} [NeZero n] (s : Simplex k P n) :
    s.closedInterior \ s.interior =
      ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  simpa [closedInterior_eq_interior_union] using
    fun i ↦ (s.disjoint_interior_closedInterior_faceOpposite i).symm

end LinearOrder

end Simplex
end Affine
