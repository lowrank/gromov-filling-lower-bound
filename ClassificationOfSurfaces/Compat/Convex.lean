/-
Compatibility backport for the closed-segment membership helper added after
mathlib v4.29.0.  The statement and proof are adapted from
Mathlib.Analysis.Convex.Segment at mathlib commit
81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.Analysis.Convex.PathConnected

open Set

variable {𝕜 E : Type*}
variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

theorem lineMap_mem_segment (a b : E) {t : 𝕜} (ht : t ∈ Icc 0 1) :
    AffineMap.lineMap a b t ∈ segment 𝕜 a b :=
  segment_eq_image_lineMap 𝕜 a b ▸ mem_image_of_mem _ ht

namespace Path

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- A nonconstant straight segment is injective.  Backported from mathlib
after v4.29.0. -/
theorem segment_injective_of_ne {a b : E} (hne : a ≠ b) :
    Function.Injective (Path.segment a b) :=
  (AffineMap.lineMap_injective ℝ hne).comp Subtype.coe_injective

end Path
