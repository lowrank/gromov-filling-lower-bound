import GromovFilling.OneHighLeg

/-!
# Finite nonlinear symplectic calculus

This file verifies the finite algebraic core of the resonant deformation used
in Lemma 10.1 of the manuscript.  An output truncation with `N` coordinates
uses `N + 1` input coordinates, so that the shifted coordinate `n + 2` is
available.  We prove an exact line expansion of the nonlinear map and the
exact constant, linear, and quadratic decomposition of its pulled-back
standard symplectic density.

These are finite identities.  The infinite-coordinate limit, the quantitative
correlation estimates, and the global Stokes/comass argument on an arbitrary
Riemannian filling remain separate analytic and geometric obligations.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- The first-order variation of
`z_n ↦ z_n + λ * conj(z_1)^2 * z_{n+2}` in a tangent vector `p`.

The distinguished scalar `a` represents `z_1`, while `y n` represents the
shifted coordinate `z_{n+2}`. -/
def resonantDifferentialVariation {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ) (p : Fin (N + 1) → ℂ) (n : Fin N) : ℂ :=
  2 * star a * y n * star (p 0) + star a ^ 2 * p n.succ

/-- The finite resonant nonlinear map, retaining the first `N` output
coordinates and the one additional input coordinate required by the shift. -/
def finiteResonantNonlinearMap {N : ℕ} (lam : ℝ)
    (z : Fin (N + 1) → ℂ) (n : Fin N) : ℂ :=
  z n.castSucc + (lam : ℂ) * star (z 0) ^ 2 * z n.succ

/-- The tangent map obtained from the displayed resonant differential. -/
def finiteResonantTangentMap {N : ℕ} (lam : ℝ)
    (a : ℂ) (y : Fin N → ℂ) (p : Fin (N + 1) → ℂ) (n : Fin N) : ℂ :=
  p n.castSucc + (lam : ℂ) * resonantDifferentialVariation a y p n

/-- Exact polynomial expansion along a real line.  In particular, the
coefficient of `t` is the claimed differential of the nonlinear map. -/
theorem finiteResonantNonlinearMap_line_expansion {N : ℕ}
    (lam t : ℝ) (z p : Fin (N + 1) → ℂ) (n : Fin N) :
    finiteResonantNonlinearMap lam (fun k ↦ z k + (t : ℂ) * p k) n =
      finiteResonantNonlinearMap lam z n +
        (t : ℂ) * finiteResonantTangentMap lam (z 0)
          (fun j ↦ z j.succ) p n +
        (lam : ℂ) * (t : ℂ) ^ 2 *
          (star (p 0) ^ 2 * z n.succ +
            2 * star (z 0) * star (p 0) * p n.succ) +
        (lam : ℂ) * (t : ℂ) ^ 3 * star (p 0) ^ 2 * p n.succ := by
  simp [finiteResonantNonlinearMap, finiteResonantTangentMap,
    resonantDifferentialVariation]
  ring

/-- The undeformed finite symplectic density. -/
def finiteBaseSymplecticDensity {N : ℕ}
    (p q : Fin (N + 1) → ℂ) : ℝ :=
  ∑ n : Fin N, (star (p n.castSucc) * q n.castSucc).im

/-- The coefficient of `λ` in the pulled-back finite symplectic density. -/
def finiteResonantFirstVariation {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (p q : Fin (N + 1) → ℂ) : ℝ :=
  ∑ n : Fin N,
    (star (resonantDifferentialVariation a y p n) * q n.castSucc +
      star (p n.castSucc) * resonantDifferentialVariation a y q n).im

/-- The coefficient of `λ²` in the pulled-back finite symplectic density. -/
def finiteResonantQuadraticVariation {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (p q : Fin (N + 1) → ℂ) : ℝ :=
  standardComplexSymplectic
    (resonantDifferentialVariation a y p)
    (resonantDifferentialVariation a y q)

private lemma symplectic_deformation_pointwise
    (lam : ℝ) (p q rp rq : ℂ) :
    (star (p + (lam : ℂ) * rp) * (q + (lam : ℂ) * rq)).im =
      (star p * q).im +
        lam * (star rp * q + star p * rq).im +
        lam ^ 2 * (star rp * rq).im := by
  simp [Complex.mul_im]
  ring

/-- Exact finite decomposition of the pulled-back standard symplectic form
into its base, first-variation, and quadratic terms. -/
theorem finiteResonant_symplectic_expansion {N : ℕ}
    (lam : ℝ) (a : ℂ) (y : Fin N → ℂ)
    (p q : Fin (N + 1) → ℂ) :
    standardComplexSymplectic
        (finiteResonantTangentMap lam a y p)
        (finiteResonantTangentMap lam a y q) =
      finiteBaseSymplecticDensity p q +
        lam * finiteResonantFirstVariation a y p q +
        lam ^ 2 * finiteResonantQuadraticVariation a y p q := by
  unfold finiteBaseSymplecticDensity finiteResonantFirstVariation
    finiteResonantQuadraticVariation finiteResonantTangentMap
  unfold standardComplexSymplectic
  simp_rw [symplectic_deformation_pointwise]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The real tangent vector reconstructed from its positive- and
negative-frequency coefficients. -/
def finiteFourierTangentVector {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) (k : Fin (N + 1)) : ℂ :=
  cNeg k + star (cPos k)

/-- The quarter-turned real tangent vector reconstructed from the same
positive- and negative-frequency coefficients. -/
def finiteFourierQuarterTurnVector {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) (k : Fin (N + 1)) : ℂ :=
  Complex.I * (star (cPos k) - cNeg k)

private lemma fourier_symplecticDensity_pointwise (c b : ℂ) :
    (star (b + star c) * (Complex.I * (star c - b))).im =
      Complex.normSq c - Complex.normSq b := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Exact finite version of the base-density identity
`Ω₀ = ∑ (|c_n|² - |c_{-n}|²)`. -/
theorem finiteBaseSymplecticDensity_fourier {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) :
    finiteBaseSymplecticDensity
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg) =
      ∑ n : Fin N,
        (Complex.normSq (cPos n.castSucc) -
          Complex.normSq (cNeg n.castSucc)) := by
  unfold finiteBaseSymplecticDensity
  apply Finset.sum_congr rfl
  intro n _
  exact fourier_symplecticDensity_pointwise
    (cPos n.castSucc) (cNeg n.castSucc)

private lemma resonant_fourier_firstVariation_pointwise
    (a y c0 b0 cn bn cs bs : ℂ) :
    (star
          (2 * star a * y * star (b0 + star c0) +
            star a ^ 2 * (bs + star cs)) *
          (Complex.I * (star cn - bn)) +
        star (bn + star cn) *
          (2 * star a * y * star (Complex.I * (star c0 - b0)) +
            star a ^ 2 * (Complex.I * (star cs - bs)))).im =
      2 * (star a ^ 2 * (cn * star cs - star bn * bs)).re +
        4 * (star a * y * (-star bn * c0 + star b0 * cn)).re := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- The same-sign shift correlation in the first variation. -/
def finiteResonantShiftCorrelation {N : ℕ}
    (cPos cNeg : Fin (N + 1) → ℂ) : ℂ :=
  ∑ n : Fin N,
    (cPos n.castSucc * star (cPos n.succ) -
      star (cNeg n.castSucc) * cNeg n.succ)

/-- The mixed first-mode/shifted-mode correlation in the first variation. -/
def finiteResonantMixedCorrelation {N : ℕ}
    (y : Fin N → ℂ) (cPos cNeg : Fin (N + 1) → ℂ) : ℂ :=
  ∑ n : Fin N, y n *
    (-star (cNeg n.castSucc) * cPos 0 +
      star (cNeg 0) * cPos n.castSucc)

/-- The manuscript's finite signed-correlation formula for the linear term
in the pulled-back symplectic density. -/
def finiteResonantCorrelationFirstVariation {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ) : ℝ :=
  2 * (star a ^ 2 * finiteResonantShiftCorrelation cPos cNeg).re +
    4 * (star a * finiteResonantMixedCorrelation y cPos cNeg).re

/-- Exact finite first-variation identity in Fourier coefficients.  The two
terms retain their signs; no triangle inequality or absolute-Jacobian bound
has been inserted. -/
theorem finiteResonant_firstVariation_eq_correlations {N : ℕ}
    (a : ℂ) (y : Fin N → ℂ)
    (cPos cNeg : Fin (N + 1) → ℂ) :
    finiteResonantFirstVariation a y
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg) =
      finiteResonantCorrelationFirstVariation a y cPos cNeg := by
  calc
    finiteResonantFirstVariation a y
          (finiteFourierTangentVector cPos cNeg)
          (finiteFourierQuarterTurnVector cPos cNeg) =
        ∑ n : Fin N,
          (2 *
              (star a ^ 2 *
                (cPos n.castSucc * star (cPos n.succ) -
                  star (cNeg n.castSucc) * cNeg n.succ)).re +
            4 *
              (star a * y n *
                (-star (cNeg n.castSucc) * cPos 0 +
                  star (cNeg 0) * cPos n.castSucc)).re) := by
      unfold finiteResonantFirstVariation
      apply Finset.sum_congr rfl
      intro n _
      simpa [finiteFourierTangentVector, finiteFourierQuarterTurnVector,
        resonantDifferentialVariation] using
        resonant_fourier_firstVariation_pointwise
          a (y n) (cPos 0) (cNeg 0)
            (cPos n.castSucc) (cNeg n.castSucc)
            (cPos n.succ) (cNeg n.succ)
    _ = finiteResonantCorrelationFirstVariation a y cPos cNeg := by
      unfold finiteResonantCorrelationFirstVariation
        finiteResonantShiftCorrelation finiteResonantMixedCorrelation
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum,
        mul_assoc]

#print axioms finiteResonantNonlinearMap_line_expansion
#print axioms finiteResonant_symplectic_expansion
#print axioms finiteBaseSymplecticDensity_fourier
#print axioms finiteResonant_firstVariation_eq_correlations

end

end GromovFilling
