import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Compactly supported Lipschitz extensions

Localized half-plane Stokes requires a globally Lipschitz, compactly supported
scalar cutoff while preserving its values on a controlled chart domain.  A
plain zero-extension would destroy the boundary trace.  Instead, this module
first extends Lipschitzly, clamps the result to `[0, 1]`, and multiplies by a
smooth bump which is identically one on the prescribed closed ball.
-/

open Function Metric Set
open scoped NNReal Topology

namespace GromovFilling

noncomputable section

/-- The pointwise product of two real-valued Lipschitz functions bounded in
absolute value by one is Lipschitz. -/
theorem LipschitzWith.mul_real_of_abs_le_one
    {α : Type*} [PseudoMetricSpace α]
    {f g : α → ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfBound : ∀ x, |f x| ≤ 1) (hgBound : ∀ x, |g x| ≤ 1) :
    LipschitzWith (Kf + Kg) fun x ↦ f x * g x := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  calc
    |f x * g x - f y * g y| =
        |f x * (g x - g y) + (f x - f y) * g y| := by
          congr 1
          ring
    _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| :=
      abs_add_le _ _
    _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by
      rw [abs_mul, abs_mul]
    _ ≤ 1 * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * 1 := by
      gcongr
      · exact hfBound x
      · simpa only [Real.dist_eq] using hg.dist_le_mul x y
      · simpa only [Real.dist_eq] using hf.dist_le_mul x y
      · exact hgBound y
    _ = ((Kf + Kg : ℝ≥0) : ℝ) * dist x y := by
      simp only [one_mul, mul_one, NNReal.coe_add]
      ring

/-- A `[0, 1]`-valued Lipschitz function on a subset of a closed ball admits
a globally Lipschitz, compactly supported `[0, 1]`-valued extension.  The
extension is not forced to vanish across any hyperplane, so boundary traces
inside the ball are preserved exactly. -/
theorem exists_lipschitzWith_hasCompactSupport_extension_Icc
    {s : Set ℂ} {f : ℂ → ℝ} {K : ℝ≥0} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hs : s ⊆ closedBall c r)
    (hf : LipschitzOnWith K f s)
    (hf_nonneg : ∀ z ∈ s, 0 ≤ f z)
    (hf_le_one : ∀ z ∈ s, f z ≤ 1) :
    ∃ C : ℝ≥0, ∃ g : ℂ → ℝ,
      LipschitzWith C g ∧ HasCompactSupport g ∧ EqOn g f s ∧
        (∀ z, 0 ≤ g z) ∧ ∀ z, g z ≤ 1 := by
  obtain ⟨e, heLip, he⟩ := hf.extend_finite_dimension
  let u : ℂ → ℝ := fun z ↦ min (max (e z) 0) 1
  have huLip : LipschitzWith (lipschitzExtensionConstant ℝ * K) u := by
    exact (heLip.max_const 0).min_const 1
  have hu_nonneg (z : ℂ) : 0 ≤ u z := by
    exact le_min (le_max_right _ _) zero_le_one
  have hu_le_one (z : ℂ) : u z ≤ 1 :=
    min_le_right _ _
  have huBound (z : ℂ) : |u z| ≤ 1 := by
    rw [abs_of_nonneg (hu_nonneg z)]
    exact hu_le_one z
  have hu_eq : EqOn u f s := by
    intro z hz
    simp only [u]
    rw [← he hz, max_eq_left (hf_nonneg z hz),
      min_eq_left (hf_le_one z hz)]
  let φ : ContDiffBump c :=
    ⟨r, r + 1, hr, lt_add_of_pos_right r zero_lt_one⟩
  obtain ⟨Kφ, hφLip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      φ.hasCompactSupport (φ.contDiff : ContDiff ℝ 1 φ) one_ne_zero
  have hφBound (z : ℂ) : |φ z| ≤ 1 := by
    rw [abs_of_nonneg φ.nonneg]
    exact φ.le_one
  let g : ℂ → ℝ := fun z ↦ φ z * u z
  have hgLip : LipschitzWith (Kφ + lipschitzExtensionConstant ℝ * K) g := by
    exact LipschitzWith.mul_real_of_abs_le_one
      hφLip huLip hφBound huBound
  have hgCompact : HasCompactSupport g := by
    change HasCompactSupport ((φ : ℂ → ℝ) * u)
    exact φ.hasCompactSupport.mul_right
  have hg_eq : EqOn g f s := by
    intro z hz
    change φ z * u z = f z
    rw [φ.one_of_mem_closedBall (hs hz), one_mul, hu_eq hz]
  refine ⟨Kφ + lipschitzExtensionConstant ℝ * K, g,
    hgLip, hgCompact, hg_eq, ?_, ?_⟩
  · intro z
    exact mul_nonneg φ.nonneg (hu_nonneg z)
  · intro z
    exact mul_le_one₀ φ.le_one (hu_nonneg z) (hu_le_one z)

#print axioms LipschitzWith.mul_real_of_abs_le_one
#print axioms exists_lipschitzWith_hasCompactSupport_extension_Icc

end

end GromovFilling
