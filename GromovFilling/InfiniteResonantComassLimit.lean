import GromovFilling.InfiniteResonantComassOrientation

/-!
# Sharp comass control after finite resonant truncation

The sharp correlation-deficit estimate belongs to the full odd Fourier
field and generally does not hold for every raw finite prefix.  This module
records the lossless replacement needed by the Stokes limit: a finite
resonant density is bounded by the sharp infinite comass constant plus the
base/first-variation truncation error, and that error tends to zero.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Difference between the finite and infinite base-plus-first-variation
parts of the resonant density. -/
def finiteTruncationResonantBaseFirstError
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ) : ℝ :=
  (finiteTruncationOddBaseDensity c N +
      lam * finiteTruncationResonantFirstVariation a y c N) -
    (infiniteOddBaseDensity c +
      lam * infiniteResonantFirstVariation a y c)

/-- A finite density is the infinite base/linear density with its own
quadratic truncation, plus the explicit base/linear truncation error. -/
theorem finiteTruncationResonantDensity_eq_infinite_add_baseFirstError
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ) :
    finiteTruncationResonantDensity lam a y c N =
      infiniteResonantDensity lam a y c
          (finiteTruncationResonantQuadraticVariation a y c N) +
        finiteTruncationResonantBaseFirstError lam a y c N := by
  unfold finiteTruncationResonantDensity infiniteResonantDensity
    finiteTruncationResonantBaseFirstError
  ring

/-- The explicit base/first-variation truncation error vanishes. -/
theorem tendsto_finiteTruncationResonantBaseFirstError
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hpos : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))))
    (hneg : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ))))) :
    Tendsto (finiteTruncationResonantBaseFirstError lam a y c)
      atTop (nhds 0) := by
  have hbaseFirst := tendsto_finiteTruncationResonantBaseFirst
    lam a y c hy hpos hneg
  simpa only [finiteTruncationResonantBaseFirstError, sub_self] using
    hbaseFirst.sub tendsto_const_nhds

/-- Abstract sharp finite-truncation estimate.  It only asks for the sharp
infinite comass bound for every admissible quadratic value and the uniform
quadratic truncation bound. -/
theorem abs_finiteTruncationResonantDensity_le_comassBound_add_error
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (c : ℤ → ℂ) (N : ℕ)
    (hinfinite : ∀ q : ℝ, |q| ≤ Qstar →
      |infiniteResonantDensity lam a y c q| ≤ comassBound lam)
    (hquadratic :
      |finiteTruncationResonantQuadraticVariation a y c N| ≤ Qstar) :
    |finiteTruncationResonantDensity lam a y c N| ≤
      comassBound lam +
        |finiteTruncationResonantBaseFirstError lam a y c N| := by
  rw [finiteTruncationResonantDensity_eq_infinite_add_baseFirstError]
  calc
    |infiniteResonantDensity lam a y c
          (finiteTruncationResonantQuadraticVariation a y c N) +
        finiteTruncationResonantBaseFirstError lam a y c N| ≤
        |infiniteResonantDensity lam a y c
          (finiteTruncationResonantQuadraticVariation a y c N)| +
          |finiteTruncationResonantBaseFirstError lam a y c N| :=
      abs_add_le _ _
    _ ≤ comassBound lam +
          |finiteTruncationResonantBaseFirstError lam a y c N| :=
      add_le_add_right
        (hinfinite
          (finiteTruncationResonantQuadraticVariation a y c N)
          hquadratic) _

/-- For genuine antiperiodic tangent-profile Fourier data, every finite
resonant density obeys the sharp comass bound up to the explicit vanishing
base/first-variation error. -/
theorem abs_finiteTruncationResonantDensity_fourierCoeffOn_le_comassBound_add_error
    (lam : ℝ) (a : ℂ) (y : ℕ → ℂ) (f : ℝ → ℂ) (N : ℕ)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hy : Summable (fun k ↦ Complex.normSq (y k)))
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hanti : Function.Antiperiodic f Real.pi)
    (hunit : ∀ᵐ x ∂volume.restrict (Ioc (-Real.pi) Real.pi),
      Complex.normSq (f x) ≤ 1)
    (hprofile : ‖a‖ ^ 2 + 9 * infiniteComplexEnergy y ≤ 2)
    (hapi : ‖a‖ ≤ 4 / Real.pi) :
    let c : ℤ → ℂ := fun n ↦ fourierCoeffOn
      (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n
    |finiteTruncationResonantDensity lam a y c N| ≤
      comassBound lam +
        |finiteTruncationResonantBaseFirstError lam a y c N| := by
  dsimp only
  let hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  let c : ℤ → ℂ := fun n ↦ fourierCoeffOn hab f n
  obtain ⟨hpos, hneg⟩ := summable_odd_fourierCoeffOn_energies f hf
  have hpos' : Summable
      (fun k ↦ Complex.normSq (c (oddMode k : ℤ))) := by
    simpa [c] using hpos
  have hneg' : Summable
      (fun k ↦ Complex.normSq (c (-(oddMode k : ℤ)))) := by
    simpa [c] using hneg
  have hcoeff : infinitePositiveOddEnergy c +
      infiniteNegativeOddEnergy c ≤ 1 := by
    simpa [c] using
      infiniteOddEnergies_fourierCoeffOn_le_one f hf hanti hunit
  have hquadratic :
      |finiteTruncationResonantQuadraticVariation a y c N| ≤ Qstar :=
    abs_finiteTruncationResonantQuadraticVariation_le_Qstar
      a y c N hy hpos' hneg' hcoeff hprofile hapi
  have hinfinite : ∀ q : ℝ, |q| ≤ Qstar →
      |infiniteResonantDensity lam a y c q| ≤ comassBound lam := by
    intro q hq
    simpa [c] using
      abs_infiniteResonantDensity_fourierCoeffOn_le_comassBound
        lam a y f q hlam0 hlam hy hf hanti hunit hprofile hapi hq
  change |finiteTruncationResonantDensity lam a y c N| ≤
    comassBound lam +
      |finiteTruncationResonantBaseFirstError lam a y c N|
  exact abs_finiteTruncationResonantDensity_le_comassBound_add_error
    lam a y c N hinfinite hquadratic

end

end GromovFilling

#print axioms
  GromovFilling.finiteTruncationResonantDensity_eq_infinite_add_baseFirstError
#print axioms
  GromovFilling.tendsto_finiteTruncationResonantBaseFirstError
#print axioms
  GromovFilling.abs_finiteTruncationResonantDensity_le_comassBound_add_error
#print axioms
  GromovFilling.abs_finiteTruncationResonantDensity_fourierCoeffOn_le_comassBound_add_error
