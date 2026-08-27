import GromovFilling.CircleDegree
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Odd boundary-distance profiles

This file formalizes the elementary metric part of Sections 2--3 of the
note.  The unit additive circle is scaled by `2π`, so an isometric boundary
has circumference `2π`.
-/

open scoped NNReal

namespace GromovFilling

noncomputable section

/-- A parametrized boundary circle of circumference `2π` is isometric when
the ambient distance is `2π` times the standard distance on `ℝ / ℤ`. -/
def IsometricCircleBoundary {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ s t, dist (boundary s) (boundary t) =
    2 * Real.pi * dist s t

/-- Distance to a point on the parametrized boundary. -/
def boundaryDistance {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) (x : X) : ℝ :=
  dist x (boundary θ)

/-- The odd part of the pair of antipodal boundary-distance functions. -/
def oddDistanceProfile {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) (x : X) : ℝ :=
  (boundaryDistance boundary θ x -
    boundaryDistance boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)) x) / 2

/-- The discarded even part of the antipodal distance pair. -/
def distanceSlack {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) (x : X) : ℝ :=
  (boundaryDistance boundary θ x +
    boundaryDistance boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)) x -
      Real.pi) / 2

lemma unitAddCircle_dist_add_half (θ : UnitAddCircle) :
    dist θ (θ + ((1 / 2 : ℝ) : UnitAddCircle)) = 1 / 2 := by
  rw [dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  simpa using AddCircle.norm_half_period_eq (1 : ℝ)

lemma unitAddCircle_add_half_add_half (θ : UnitAddCircle) :
    θ + ((1 / 2 : ℝ) : UnitAddCircle) +
      ((1 / 2 : ℝ) : UnitAddCircle) = θ := by
  rw [add_assoc, ← AddCircle.coe_add]
  norm_num

/-- Distance to the antipode is the complementary half-circle distance. -/
lemma unitAddCircle_dist_add_half_eq (s θ : UnitAddCircle) :
    dist s (θ + ((1 / 2 : ℝ) : UnitAddCircle)) =
      1 / 2 - dist s θ := by
  rw [dist_eq_norm, dist_eq_norm]
  rw [show s - (θ + ((1 / 2 : ℝ) : UnitAddCircle)) =
      (s - θ) - ((1 / 2 : ℝ) : UnitAddCircle) by abel]
  let z : UnitAddCircle := s - θ
  change ‖z - ((1 / 2 : ℝ) : UnitAddCircle)‖ = 1 / 2 - ‖z‖
  obtain ⟨t, ht, htcoe⟩ := AddCircle.eq_coe_Ico
    (z + ((1 / 2 : ℝ) : UnitAddCircle))
  let r : ℝ := t - 1 / 2
  have hrlo : -(1 / 2 : ℝ) ≤ r := by dsimp only [r]; linarith [ht.1]
  have hrhi : r < 1 / 2 := by dsimp only [r]; linarith [ht.2]
  have hrabs : |r| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    exact ⟨hrlo, hrhi.le⟩
  have hrcoe : (r : UnitAddCircle) = z := by
    calc
      (r : UnitAddCircle) = (t : UnitAddCircle) -
          ((1 / 2 : ℝ) : UnitAddCircle) := by
        rw [← AddCircle.coe_sub]
      _ = (z + ((1 / 2 : ℝ) : UnitAddCircle)) -
          ((1 / 2 : ℝ) : UnitAddCircle) := by rw [htcoe]
      _ = z := by abel
  have hnormr : ‖(r : UnitAddCircle)‖ = |r| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hrabs)
  rw [← hrcoe, hnormr, ← AddCircle.coe_sub]
  by_cases hr0 : 0 ≤ r
  · have hdiffNonpos : r - 1 / 2 ≤ 0 := by linarith
    have hdiffAbs : |r - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_of_nonpos hdiffNonpos]
      linarith
    rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hdiffAbs),
      abs_of_nonpos hdiffNonpos, abs_of_nonneg hr0]
    ring
  · have hrneg : r < 0 := lt_of_not_ge hr0
    have heq : ((r - 1 / 2 : ℝ) : UnitAddCircle) =
        ((r + 1 / 2 : ℝ) : UnitAddCircle) := by
      rw [← AddCircle.coe_add_period (1 : ℝ) (r - 1 / 2)]
      congr 1
      ring
    rw [heq]
    have hsumNonneg : 0 ≤ r + 1 / 2 := by linarith
    have hsumAbs : |r + 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_of_nonneg hsumNonneg]
      linarith
    rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by simpa using hsumAbs),
      abs_of_nonneg hsumNonneg, abs_of_nonpos hrneg.le]
    ring

/-- Every fixed boundary-distance function is one-Lipschitz in the filling
variable. -/
theorem boundaryDistance_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) :
    LipschitzWith 1 (boundaryDistance boundary θ) := by
  exact LipschitzWith.dist_left (boundary θ)

/-- The odd distance profile is also one-Lipschitz in the filling
variable. -/
theorem oddDistanceProfile_lipschitzWith
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) :
    LipschitzWith 1 (oddDistanceProfile boundary θ) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.dist_eq]
  unfold oddDistanceProfile boundaryDistance
  have hθ : |dist x (boundary θ) - dist y (boundary θ)| ≤
      dist x y := by
    simpa only [Real.dist_eq] using
      dist_dist_dist_le_left x y (boundary θ)
  have hhalf :
      |dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))) -
        dist y (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))| ≤
          dist x y := by
    simpa only [Real.dist_eq] using dist_dist_dist_le_left x y
      (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))
  calc
    |(dist x (boundary θ) -
          dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
        (dist y (boundary θ) -
          dist y (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2| =
        |(dist x (boundary θ) - dist y (boundary θ)) -
          (dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist y (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))))| / 2 := by
          rw [show
            (dist x (boundary θ) -
                dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 -
              (dist y (boundary θ) -
                dist y (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))) / 2 =
              ((dist x (boundary θ) - dist y (boundary θ)) -
                (dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))) -
                  dist y (boundary
                    (θ + ((1 / 2 : ℝ) : UnitAddCircle))))) / 2 by ring]
          rw [abs_div]
          congr 1
          · ring
    _ ≤ (|dist x (boundary θ) - dist y (boundary θ)| +
          |dist x (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle))) -
            dist y (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))|) / 2 := by
          gcongr
          exact abs_sub _ _
    _ ≤ dist x y := by linarith

/-- Shifting the boundary parameter by half a turn negates the odd
profile. -/
theorem oddDistanceProfile_add_half
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) (x : X) :
    oddDistanceProfile boundary
      (θ + ((1 / 2 : ℝ) : UnitAddCircle)) x =
      -oddDistanceProfile boundary θ x := by
  unfold oddDistanceProfile
  rw [unitAddCircle_add_half_add_half]
  ring

/-- Shifting the boundary parameter by half a turn preserves the slack. -/
theorem distanceSlack_add_half
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (θ : UnitAddCircle) (x : X) :
    distanceSlack boundary
      (θ + ((1 / 2 : ℝ) : UnitAddCircle)) x =
      distanceSlack boundary θ x := by
  unfold distanceSlack
  rw [unitAddCircle_add_half_add_half]
  ring

/-- The antipodal slack is nonnegative.  This is exactly the triangle
inequality together with the isometric boundary condition. -/
theorem distanceSlack_nonneg
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (θ : UnitAddCircle) (x : X) :
    0 ≤ distanceSlack boundary θ x := by
  have htriangle := dist_triangle (boundary θ) x
    (boundary (θ + ((1 / 2 : ℝ) : UnitAddCircle)))
  rw [hboundary, unitAddCircle_dist_add_half] at htriangle
  unfold distanceSlack boundaryDistance
  rw [dist_comm (boundary θ) x] at htriangle
  nlinarith [Real.pi_pos]

/-- The odd profile restricts on an isometric boundary to the centered
triangle wave. -/
theorem oddDistanceProfile_on_boundary
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (θ s : UnitAddCircle) :
    oddDistanceProfile boundary θ (boundary s) =
      2 * Real.pi * dist s θ - Real.pi / 2 := by
  unfold oddDistanceProfile boundaryDistance
  rw [hboundary, hboundary, unitAddCircle_dist_add_half_eq]
  ring

/-- The antipodal slack vanishes on an isometric boundary. -/
theorem distanceSlack_on_boundary
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hboundary : IsometricCircleBoundary boundary)
    (θ s : UnitAddCircle) :
    distanceSlack boundary θ (boundary s) = 0 := by
  unfold distanceSlack boundaryDistance
  rw [hboundary, hboundary, unitAddCircle_dist_add_half_eq]
  ring

end

end GromovFilling
