import GromovFilling.FiniteSymplecticPrimitiveTransition
import GromovFilling.RiemannianBoundaryPartition

/-!
# Finite partition-of-unity gluing for symplectic Stokes

This module records the finite algebra that globalizes the localized weak
Stokes identities.  Pointwise partition sums recover the unlocalized
integral, while the derivatives of the cutoffs add to zero and therefore
cancel the symplectic primitive-error terms exactly.
-/

open Function MeasureTheory
open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Integrating the finitely many localized densities recovers the original
density whenever the cutoffs add pointwise to one. -/
theorem sum_integral_partition_mul_eq_integral
    {κ X : Type*} [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) (ρ : κ → X → ℝ) (g : X → ℝ)
    (hsum : ∀ x, ∑ i, ρ i x = 1)
    (hint : ∀ i, Integrable (fun x ↦ ρ i x * g x) μ) :
    (∑ i, ∫ x, ρ i x * g x ∂μ) = ∫ x, g x ∂μ := by
  calc
    (∑ i, ∫ x, ρ i x * g x ∂μ) =
        ∫ x, ∑ i, ρ i x * g x ∂μ := by
      symm
      rw [integral_finset_sum Finset.univ]
      intro i _hi
      exact hint i
    _ = ∫ x, g x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← Finset.sum_mul, hsum x, one_mul]

/-- The finite symplectic primitive errors cancel pointwise when the
differentiable cutoffs add to one. -/
theorem sum_finiteSymplecticFDerivPrimitiveError_eq_zero
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (ρ : κ → ℂ → ℝ) (F : ℂ → ι → ℂ) (z : ℂ)
    (hρ : ∀ j, DifferentiableAt ℝ (ρ j) z)
    (hsum : ∀ w, ∑ j, ρ j w = 1) :
    ∑ j, finiteSymplecticFDerivPrimitiveError (ρ j) F z = 0 := by
  have hD := sum_fderiv_eq_zero_of_sum_eq_one ρ z hρ hsum
  have hDI : (∑ j, fderiv ℝ (ρ j) z Complex.I) = 0 := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L Complex.I) hD
    simpa only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.zero_apply] using h
  have hDOne : (∑ j, fderiv ℝ (ρ j) z 1) = 0 := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L 1) hD
    simpa only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.zero_apply] using h
  let A : ℝ := standardComplexSymplecticPrimitive
    (F z) ((fderiv ℝ F z) 1)
  let B : ℝ := standardComplexSymplecticPrimitive
    (F z) ((fderiv ℝ F z) Complex.I)
  change (∑ j, fderiv ℝ (ρ j) z Complex.I * A -
    fderiv ℝ (ρ j) z 1 * B) = 0
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    hDI, hDOne]
  ring

/-- Once every localized Stokes identity has the form `Lᵢ = Eᵢ - Bᵢ`,
vanishing of the total primitive error leaves precisely the signed total
boundary action. -/
theorem sum_localized_eq_neg_sum_boundary_of_error_cancellation
    {κ : Type*} [Fintype κ] (L E B : κ → ℝ)
    (hlocal : ∀ i, L i = E i - B i)
    (herror : ∑ i, E i = 0) :
    ∑ i, L i = -(∑ i, B i) := by
  simp_rw [hlocal]
  rw [Finset.sum_sub_distrib, herror]
  ring

end

end GromovFilling

#print axioms GromovFilling.sum_integral_partition_mul_eq_integral
#print axioms
  GromovFilling.sum_finiteSymplecticFDerivPrimitiveError_eq_zero
#print axioms
  GromovFilling.sum_localized_eq_neg_sum_boundary_of_error_cancellation
