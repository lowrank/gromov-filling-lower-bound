/-
Compatibility backport of the circle-arc API added after mathlib v4.29.0.
The declarations below are adapted from
Mathlib.Analysis.SpecialFunctions.Complex.Circle at mathlib commit
81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.PathConnected

open Complex Function Set
open Real

namespace Circle

lemma exp_surjective : Surjective exp := fun z => ⟨z.val.arg, exp_arg z⟩

lemma exp_injOn_of_forall_sub_mem_Ioo {s : Set ℝ}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ Ioo (-2 * π) (2 * π)) : InjOn exp s := by
  intro t₁ ht₁ t₂ ht₂ heq
  obtain ⟨h1, h2⟩ := hs t₁ ht₁ t₂ ht₂
  rw [neg_mul] at h1
  rw [← sub_eq_zero, ← cos_eq_one_iff_of_lt_of_lt h1 h2, ← exp_ofReal_mul_I_re]
  replace heq : cexp _ = cexp _ := congrArg Subtype.val heq
  rw [exp_eq_exp_iff_exp_sub_eq_one, ← sub_mul, ← ofReal_sub, Complex.ext_iff] at heq
  exact heq.1

lemma exp_injOn_Icc {a b : ℝ} (h : b - a < 2 * π) : InjOn exp (Icc a b) :=
  exp_injOn_of_forall_sub_mem_Ioo <| fun x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ ↦ by
    constructor <;> linarith

variable {x y : Circle}

/-- Length of the anti-clockwise arc from `x` to `y`. -/
noncomputable def angleDiff (x y : Circle) : ℝ :=
  if x.val.arg ≤ y.val.arg then y.val.arg - x.val.arg else 2 * π + y.val.arg - x.val.arg

@[simp]
lemma angleDiff_nonneg (x y : Circle) : 0 ≤ angleDiff x y := by
  unfold angleDiff
  split_ifs with hxy
  · linarith
  · linarith [neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma angleDiff_pos (h : x ≠ y) : 0 < angleDiff x y := by
  have harg : x.val.arg ≠ y.val.arg := fun harg => h (injective_arg harg)
  unfold angleDiff
  split_ifs with hxy
  · exact sub_pos.mpr (lt_of_le_of_ne hxy harg)
  · linarith [neg_pi_lt_arg y.val, arg_le_pi x.val]

lemma angleDiff_lt_two_pi (x y : Circle) : angleDiff x y < 2 * π := by
  unfold angleDiff
  split_ifs with hxy
  · linarith [neg_pi_lt_arg x.val, arg_le_pi y.val]
  · linarith

@[simp]
lemma exp_angleDiff_mul : exp (angleDiff x y) * x = y := by
  rw [← exp_arg x, ← exp_add, angleDiff]
  split_ifs with hxy <;> simp

lemma Icc_union_Icc_angleDiff_add_arg (h : x ≠ y) :
    Icc x.val.arg (angleDiff x y + x.val.arg) ∪ Icc y.val.arg (angleDiff y x + y.val.arg) =
    Icc (min x.val.arg y.val.arg) (min x.val.arg y.val.arg + 2 * π) := by
  have harg : x.val.arg ≠ y.val.arg := fun harg => h (injective_arg harg)
  ext z
  simp only [mem_union, mem_Icc]
  by_cases hxy : x.val.arg ≤ y.val.arg
  · have hlt : x.val.arg < y.val.arg := lt_of_le_of_ne hxy harg
    simp only [angleDiff, if_pos hxy, if_neg (not_le.mpr hlt), min_eq_left hxy]
    ring_nf
    constructor
    · rintro (hz | hz) <;> constructor <;>
        linarith [neg_pi_lt_arg x.val, arg_le_pi y.val]
    · intro hz
      by_cases hzy : z ≤ y.val.arg
      · exact Or.inl ⟨hz.1, hzy⟩
      · exact Or.inr ⟨le_of_not_ge hzy, hz.2⟩
  · have hyx : y.val.arg ≤ x.val.arg := le_of_not_ge hxy
    have hlt : y.val.arg < x.val.arg := lt_of_le_of_ne hyx harg.symm
    simp only [angleDiff, if_neg hxy, if_pos hyx, min_eq_right hyx]
    ring_nf
    constructor
    · rintro (hz | hz) <;> constructor <;>
        linarith [neg_pi_lt_arg y.val, arg_le_pi x.val]
    · intro hz
      by_cases hzx : z ≤ x.val.arg
      · exact Or.inr ⟨hz.1, hzx⟩
      · exact Or.inl ⟨le_of_not_ge hzx, hz.2⟩

/-- Path from `x` to `y` on the circle traversing in anti-clockwise direction. -/
noncomputable def path (x y : Circle) : Path x y :=
  (Path.segment x.val.arg <| angleDiff x y + x.val.arg).map exp.continuous
    |>.cast (by simp) (by simp)

@[simp]
lemma path_apply (x y : Circle) (a : unitInterval) :
    path x y a = exp (Path.segment x.val.arg (x.angleDiff y + x.val.arg) a) := by
  simp [path]

@[simp]
lemma coe_path (x y : Circle) : (path x y : _ → _) =
    exp ∘ ⇑(Path.segment x.val.arg (x.angleDiff y + x.val.arg)) := by
  ext t
  rw [path_apply, comp_apply]

lemma path_injective_of_ne (hne : x ≠ y) : Injective (path x y) := by
  intro s t hst
  have hend : x.val.arg ≠ angleDiff x y + x.val.arg := by
    linarith [angleDiff_pos hne]
  have hseg : Injective (Path.segment x.val.arg (angleDiff x y + x.val.arg)) := by
    intro u v huv
    apply Subtype.ext
    exact (AffineMap.lineMap_injective ℝ hend) huv
  apply hseg
  apply exp_injOn_Icc (a := x.val.arg) (b := angleDiff x y + x.val.arg)
      (by simp [angleDiff_lt_two_pi])
  · rw [← segment_eq_Icc (by linarith [angleDiff_pos hne]), ← Path.range_segment]
    exact Set.mem_range_self s
  · rw [← segment_eq_Icc (by linarith [angleDiff_pos hne]), ← Path.range_segment]
    exact Set.mem_range_self t
  · simpa only [path_apply] using hst

lemma range_path (x y : Circle) :
    range (path x y) = exp '' Icc x.val.arg (angleDiff x y + x.val.arg) := by
  rw [coe_path, range_comp, Path.range_segment, segment_eq_Icc (by simp)]

lemma range_path_union_range_path (h : x ≠ y) : range (path x y) ∪ range (path y x) = univ := by
  rw [range_path, range_path, ← image_union, Icc_union_Icc_angleDiff_add_arg h,
    periodic_exp.image_Icc two_pi_pos]
  apply range_eq_univ.mpr
  exact fun z => ⟨z.val.arg, exp_arg z⟩

end Circle
