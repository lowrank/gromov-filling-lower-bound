import GromovFilling.DominantHarmonic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

/-!
# The disk bounded by a dominant-harmonic curve

The strict chord estimate used on the boundary also makes the associated
complex polynomial injective on the entire closed unit disk.  This file
identifies the image of the open disk with the connected component of zero
in the complement of the boundary curve.  It is the topological half of
the bridge from the Fourier Green calculation to actual Lebesgue area.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The polynomial whose restriction to the unit circle is
`dominantHarmonicCurve`. -/
def dominantHarmonicPolynomial {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ℂ) : ℂ :=
  a₁ * z + ∑ k, a k * z ^ m k

@[simp]
theorem dominantHarmonicPolynomial_coe_unitCircle
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) (z : ComplexUnitCircle) :
    dominantHarmonicPolynomial a₁ m a z =
      dominantHarmonicCurve a₁ m a z := rfl

/-- Derivative-weighted dominance makes the polynomial injective on the
closed unit disk, not merely on its boundary. -/
theorem dominantHarmonicPolynomial_injOn_closedBall
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    Set.InjOn (dominantHarmonicPolynomial a₁ m a)
      (Metric.closedBall 0 1) := by
  intro z hz w hw hpoly
  by_contra hne
  have hzw : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hwNorm : ‖w‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  have heq :
      a₁ * (z - w) =
        -(∑ k, (a k * z ^ m k - a k * w ^ m k)) := by
    unfold dominantHarmonicPolynomial at hpoly
    rw [Finset.sum_sub_distrib]
    linear_combination hpoly
  have hterm (k : ι) :
      ‖a k * z ^ m k - a k * w ^ m k‖ ≤
        ((m k : ℝ) * ‖a k‖) * ‖z - w‖ := by
    rw [← mul_sub, norm_mul]
    calc
      ‖a k‖ * ‖z ^ m k - w ^ m k‖ ≤
          ‖a k‖ * ((m k : ℝ) * ‖z - w‖) := by
            gcongr
            exact norm_pow_sub_pow_le z w hzNorm hwNorm (m k)
      _ = ((m k : ℝ) * ‖a k‖) * ‖z - w‖ := by ring
  have hupper :
      ‖a₁‖ * ‖z - w‖ ≤
        (∑ k, (m k : ℝ) * ‖a k‖) * ‖z - w‖ := by
    calc
      ‖a₁‖ * ‖z - w‖ = ‖a₁ * (z - w)‖ := (norm_mul _ _).symm
      _ = ‖∑ k, (a k * z ^ m k - a k * w ^ m k)‖ := by
            rw [heq, norm_neg]
      _ ≤ ∑ k, ‖a k * z ^ m k - a k * w ^ m k‖ :=
            norm_sum_le _ _
      _ ≤ ∑ k, (((m k : ℝ) * ‖a k‖) * ‖z - w‖) :=
            Finset.sum_le_sum fun k _ ↦ hterm k
      _ = (∑ k, (m k : ℝ) * ‖a k‖) * ‖z - w‖ := by
            rw [Finset.sum_mul]
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hdom hzw)) hupper

theorem continuous_dominantHarmonicPolynomial
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) :
    Continuous (dominantHarmonicPolynomial a₁ m a) := by
  unfold dominantHarmonicPolynomial
  fun_prop

theorem analyticOnNhd_dominantHarmonicPolynomial
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ) :
    AnalyticOnNhd ℂ (dominantHarmonicPolynomial a₁ m a) Set.univ := by
  unfold dominantHarmonicPolynomial
  exact (analyticOnNhd_const.mul analyticOnNhd_id).add
    (Finset.analyticOnNhd_fun_sum Finset.univ fun k _ ↦
      analyticOnNhd_const.mul (analyticOnNhd_id.pow (m k)))

/-- A dominant-harmonic polynomial is a nonconstant holomorphic map and
hence is open on the complex plane. -/
theorem dominantHarmonicPolynomial_isOpenMap
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    IsOpenMap (dominantHarmonicPolynomial a₁ m a) := by
  have hanalytic := analyticOnNhd_dominantHarmonicPolynomial a₁ m a
  rcases hanalytic.is_constant_or_isOpenMap with hconstant | hopen
  · obtain ⟨c, hc⟩ := hconstant
    have hinj := dominantHarmonicPolynomial_injOn_closedBall a₁ m a hdom
    have hzero : (0 : ℂ) ∈ Metric.closedBall 0 1 := by simp
    have hone : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
    have : (0 : ℂ) = 1 := hinj hzero hone (by rw [hc 0, hc 1])
    norm_num at this
  · exact hopen

/-- An open continuous map which is injective on the closed disk sends the
open disk onto the connected component of the image of its boundary. -/
theorem image_openBall_eq_connectedComponentIn_image_sphere
    (f : ℂ → ℂ) (hf : Continuous f) (hfOpen : IsOpenMap f)
    (hfInj : Set.InjOn f (Metric.closedBall 0 1)) (hfzero : f 0 = 0) :
    f '' Metric.ball 0 1 =
      connectedComponentIn (f '' Metric.sphere 0 1)ᶜ 0 := by
  let D : Set ℂ := f '' Metric.ball 0 1
  let K : Set ℂ := f '' Metric.closedBall 0 1
  let C : Set ℂ := f '' Metric.sphere 0 1
  have hzeroD : 0 ∈ D := ⟨0, Metric.mem_ball_self (by norm_num), hfzero⟩
  have hDOpen : IsOpen D := hfOpen _ Metric.isOpen_ball
  have hKClosed : IsClosed K :=
    ((isCompact_closedBall (0 : ℂ) 1).image hf).isClosed
  have hK : K = D ∪ C := by
    dsimp only [K, D, C]
    rw [← Set.image_union, Metric.ball_union_sphere]
  have hDsubK : D ⊆ K := by
    rw [hK]
    exact Set.subset_union_left
  have hDCompl : D ⊆ Cᶜ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hfw⟩
    have hzClosed : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall hz
    have hwClosed : w ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall hw
    have hzw : z = w := hfInj hzClosed hwClosed hfw.symm
    subst w
    have hzlt : dist z 0 < 1 := hz
    have hzeq : dist z 0 = 1 := hw
    linarith
  apply Set.Subset.antisymm
  · have hDConnected : IsConnected D :=
      (Metric.isConnected_ball (x := (0 : ℂ)) (r := 1) (by norm_num)).image
        f hf.continuousOn
    exact hDConnected.isPreconnected.subset_connectedComponentIn
      hzeroD hDCompl
  · have hcomponentZero :
        0 ∈ connectedComponentIn Cᶜ 0 :=
      mem_connectedComponentIn (hDCompl hzeroD)
    have hcomponentSubset :
        connectedComponentIn Cᶜ 0 ⊆ D ∪ Kᶜ := by
      intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inl hxD
      · right
        intro hxK
        rw [hK] at hxK
        rcases hxK with hxD' | hxC
        · exact hxD hxD'
        · exact (connectedComponentIn_subset Cᶜ 0 hx) hxC
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hDOpen hKClosed.isOpen_compl
      (Set.disjoint_left.mpr fun _ hxD hxK ↦ hxK (hDsubK hxD))
      hcomponentSubset ⟨0, hcomponentZero, hzeroD⟩

/-- If all higher exponents are positive, the open-disk image of a
dominant-harmonic polynomial is precisely the zero component outside its
unit-circle image. -/
theorem dominantHarmonicPolynomial_image_ball_eq_component
    {ι : Type*} [Fintype ι]
    (a₁ : ℂ) (m : ι → ℕ) (a : ι → ℂ)
    (hm : ∀ k, 1 ≤ m k)
    (hdom : (∑ k, (m k : ℝ) * ‖a k‖) < ‖a₁‖) :
    dominantHarmonicPolynomial a₁ m a '' Metric.ball 0 1 =
      connectedComponentIn
        (dominantHarmonicPolynomial a₁ m a '' Metric.sphere 0 1)ᶜ 0 := by
  apply image_openBall_eq_connectedComponentIn_image_sphere
    (dominantHarmonicPolynomial a₁ m a)
    (continuous_dominantHarmonicPolynomial a₁ m a)
    (dominantHarmonicPolynomial_isOpenMap a₁ m a hdom)
    (dominantHarmonicPolynomial_injOn_closedBall a₁ m a hdom)
  unfold dominantHarmonicPolynomial
  simp only [mul_zero]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k _
    rw [zero_pow (Nat.ne_of_gt (hm k)), mul_zero]

end

end GromovFilling
