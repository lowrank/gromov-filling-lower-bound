import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrated finite-to-infinite comass limits

The sharp nonlinear comass estimate is obtained pointwise as a limit of
finite resonant densities.  A measurable choice of the auxiliary infinite
Fourier field is neither available nor needed.  Instead, this module uses
the positive excess of each finite density above the limiting comass.  The
excess is defined directly from the finite density, and a pointwise
vanishing error forces it to tend to zero.  Dominated convergence then
passes the sharp bound through the surface integral.
-/

open Filter MeasureTheory
open scoped Topology

namespace GromovFilling

noncomputable section

/-- The nonnegative amount by which the absolute value of a scalar density
exceeds a proposed comass bound. -/
def comassPositiveExcess (C r : ℝ) : ℝ :=
  max (|r| - C) 0

theorem comassPositiveExcess_nonneg (C r : ℝ) :
    0 ≤ comassPositiveExcess C r := by
  exact le_max_right _ _

/-- Every scalar is bounded by the proposed comass plus its positive
excess. -/
theorem abs_le_comass_add_positiveExcess (C r : ℝ) :
    |r| ≤ C + comassPositiveExcess C r := by
  unfold comassPositiveExcess
  calc
    |r| = C + (|r| - C) := by ring
    _ ≤ C + max (|r| - C) 0 := by
      exact add_le_add le_rfl (le_max_left _ _)

/-- A pointwise comass estimate up to an error tending to zero makes the
positive excess of the finite densities tend to zero.  This formulation
eliminates the auxiliary error from the function that will be integrated. -/
theorem tendsto_comassPositiveExcess_zero_of_abs_le_add_error
    {f e : ℕ → ℝ} {C : ℝ}
    (he : Tendsto e atTop (nhds 0))
    (hbound : ∀ n, |f n| ≤ C + |e n|) :
    Tendsto (fun n ↦ comassPositiveExcess C (f n))
      atTop (nhds 0) := by
  have heabs : Tendsto (fun n ↦ |e n|) atTop (nhds 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto 0).comp he
  refine squeeze_zero
    (f := fun n ↦ comassPositiveExcess C (f n))
    (g := fun n ↦ |e n|) ?_ ?_ heabs
  · exact fun n ↦ comassPositiveExcess_nonneg C (f n)
  · intro n
    unfold comassPositiveExcess
    apply max_le
    · linarith [hbound n]
    · exact abs_nonneg (e n)

/-- Dominated convergence for the positive comass excess.  The assumptions
are phrased almost everywhere so the theorem applies directly to weak
derivative densities on a Riemannian surface. -/
theorem tendsto_integral_comassPositiveExcess
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℕ → X → ℝ} {C K : ℝ}
    (hmeas : ∀ n,
      AEStronglyMeasurable
        (fun x ↦ comassPositiveExcess C (F n x)) μ)
    (hK : Integrable (fun _x : X ↦ K) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      ‖comassPositiveExcess C (F n x)‖ ≤ K)
    (hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ comassPositiveExcess C (F n x))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ ∫ x, comassPositiveExcess C (F n x) ∂μ)
      atTop (nhds 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n x ↦ comassPositiveExcess C (F n x))
    (f := fun _x : X ↦ (0 : ℝ)) (fun _x : X ↦ K)
    hmeas hK hbound hlim
  simpa only [integral_zero] using h

/-- If finite calibration values converge, every one is bounded by the
integral of a finite density, and the positive comass excess vanishes under
an integrable domination, then the limiting calibration is bounded by the
sharp comass times the declared area. -/
theorem calibration_le_comass_mul_area_of_dominated_positiveExcess
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℕ → X → ℝ} {b : ℕ → ℝ} {B C K area : ℝ}
    (hb : Tendsto b atTop (nhds B))
    (hfinite : ∀ n, b n ≤ ∫ x, |F n x| ∂μ)
    (hFint : ∀ n, Integrable (fun x ↦ |F n x|) μ)
    (hmeas : ∀ n,
      AEStronglyMeasurable
        (fun x ↦ comassPositiveExcess C (F n x)) μ)
    (hK : Integrable (fun _x : X ↦ K) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      ‖comassPositiveExcess C (F n x)‖ ≤ K)
    (hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ comassPositiveExcess C (F n x))
        atTop (nhds 0))
    (hC : Integrable (fun _x : X ↦ C) μ)
    (harea : ∫ _x : X, C ∂μ ≤ C * area) :
    B ≤ C * area := by
  have hExcessInt (n : ℕ) :
      Integrable (fun x ↦ comassPositiveExcess C (F n x)) μ := by
    exact hK.mono' (hmeas n) (hbound n)
  have hExcessLim : Tendsto
      (fun n ↦ ∫ x, comassPositiveExcess C (F n x) ∂μ)
      atTop (nhds 0) :=
    tendsto_integral_comassPositiveExcess μ hmeas hK hbound hlim
  have hfinite' (n : ℕ) :
      b n ≤ C * area +
        ∫ x, comassPositiveExcess C (F n x) ∂μ := by
    calc
      b n ≤ ∫ x, |F n x| ∂μ := hfinite n
      _ ≤ ∫ x, C + comassPositiveExcess C (F n x) ∂μ := by
        apply integral_mono_ae (hFint n)
          (hC.add (hExcessInt n))
        filter_upwards with x
        exact abs_le_comass_add_positiveExcess C (F n x)
      _ = (∫ _x : X, C ∂μ) +
          ∫ x, comassPositiveExcess C (F n x) ∂μ := by
        rw [integral_add hC (hExcessInt n)]
      _ ≤ C * area +
          ∫ x, comassPositiveExcess C (F n x) ∂μ := by
        exact add_le_add harea le_rfl
  have hupper : Tendsto
      (fun n ↦ C * area +
        ∫ x, comassPositiveExcess C (F n x) ∂μ)
      atTop (nhds (C * area)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hExcessLim
  exact le_of_tendsto_of_tendsto' hb hupper hfinite'

end

end GromovFilling

#print axioms GromovFilling.comassPositiveExcess
#print axioms
  GromovFilling.tendsto_comassPositiveExcess_zero_of_abs_le_add_error
#print axioms GromovFilling.tendsto_integral_comassPositiveExcess
#print axioms
  GromovFilling.calibration_le_comass_mul_area_of_dominated_positiveExcess
