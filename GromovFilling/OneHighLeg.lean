import GromovFilling.ResonanceTrace
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Finite one-high-leg resonance algebra

This file verifies the finite algebraic core of the high-mode test and the
Rayleigh-quotient step in Section 14 of the note.  The distinguished index
`none` represents the unperturbed coordinate and `some j` represents the
`j`-th normalized one-high-leg resonance.

The high Hardy mode is exhibited explicitly, its unit norm and
anti-periodicity are proved, and the resulting orthogonal output vector has
standard symplectic value `1 + ∑ j, μ j ^ 2`.  The final theorem proves the
finite Rayleigh ceiling for any positive-semidefinite matrix and proves that
the Rayleigh supremum used there is an eigenvalue.

The finite matrix is defined by the manuscript's convergent odd-mode series
and proved positive semidefinite through an explicit weighted Gram
factorization.  What remains outside this module is the analytic
identification of these finite coordinate formulas with the derivative of the
full normalized nonlinear map on its infinite coefficient space, and the
bridge from anti-periodic fields to a global ambient comass.
-/

open scoped BigOperators
open Matrix Module.End

namespace GromovFilling

noncomputable section

/-- The positive odd frequency used to test a hierarchy with `J` resonances. -/
def oneHighLegTestFrequency (J : ℕ) : ℕ := 2 * J + 1

lemma oneHighLegTestFrequency_gt (J : ℕ) :
    2 * J < oneHighLegTestFrequency J := by
  unfold oneHighLegTestFrequency
  omega

lemma oneHighLegTestFrequency_odd (J : ℕ) :
    Odd (oneHighLegTestFrequency J) := by
  refine ⟨J, ?_⟩
  unfold oneHighLegTestFrequency
  omega

/-- The positive Hardy mode `exp(i m θ)` used in the manuscript's high-mode
test. -/
def positiveHardyMode (m : ℕ) (θ : ℝ) : ℂ :=
  Complex.exp (((((m : ℝ) * θ : ℝ) : ℂ)) * Complex.I)

lemma norm_positiveHardyMode (m : ℕ) (θ : ℝ) :
    ‖positiveHardyMode m θ‖ = 1 := by
  simpa [positiveHardyMode] using
    Complex.norm_exp_ofReal_mul_I ((m : ℝ) * θ)

/-- The chosen odd Hardy mode is anti-periodic under `θ ↦ θ + π`. -/
theorem positiveHardyMode_add_pi (J : ℕ) (θ : ℝ) :
    positiveHardyMode (oneHighLegTestFrequency J) (θ + Real.pi) =
      -positiveHardyMode (oneHighLegTestFrequency J) θ := by
  have harg :
      (((((oneHighLegTestFrequency J : ℕ) : ℝ) * (θ + Real.pi) : ℝ) : ℂ) *
          Complex.I) =
        (((((oneHighLegTestFrequency J : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) +
          (J : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I := by
    unfold oneHighLegTestFrequency
    push_cast
    ring
  unfold positiveHardyMode
  rw [harg, Complex.exp_add, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

/-- The standard symplectic form on a finite complex coordinate space. -/
def standardComplexSymplectic {ι : Type*} [Fintype ι]
    (p q : ι → ℂ) : ℝ :=
  ∑ i, (star (p i) * q i).im

private lemma im_star_mul_I_mul (z : ℂ) :
    (star z * (Complex.I * z)).im = Complex.normSq z := by
  rw [Complex.mul_im, Complex.normSq_apply]
  simp

lemma standardComplexSymplectic_I_mul {ι : Type*} [Fintype ι]
    (p : ι → ℂ) :
    standardComplexSymplectic p (fun i ↦ Complex.I * p i) =
      ∑ i, Complex.normSq (p i) := by
  unfold standardComplexSymplectic
  apply Finset.sum_congr rfl
  intro i _
  exact im_star_mul_I_mul (p i)

/-- Occupied output coordinates of the differential on the high-mode test
plane.  `none` is the original mode and `some j` is its `j`-th shifted copy. -/
def oneHighLegHighModeOutput {J : ℕ} (μ : Fin J → ℝ) (a : ℂ) :
    Option (Fin J) → ℂ
  | none => a
  | some j => (μ j : ℂ) * a

@[simp] lemma oneHighLegHighModeOutput_none {J : ℕ}
    (μ : Fin J → ℝ) (a : ℂ) :
    oneHighLegHighModeOutput μ a none = a := rfl

@[simp] lemma oneHighLegHighModeOutput_some {J : ℕ}
    (μ : Fin J → ℝ) (a : ℂ) (j : Fin J) :
    oneHighLegHighModeOutput μ a (some j) = (μ j : ℂ) * a := rfl

lemma oneHighLegHighModeOutput_I {J : ℕ} (μ : Fin J → ℝ) :
    oneHighLegHighModeOutput μ Complex.I =
      fun i ↦ Complex.I * oneHighLegHighModeOutput μ 1 i := by
  funext i
  cases i <;> simp [oneHighLegHighModeOutput, mul_comm]

/-- Exact symplectic value of the manuscript's orthogonal high-mode output
vectors. -/
theorem oneHighLegHighMode_symplecticValue {J : ℕ} (μ : Fin J → ℝ) :
    standardComplexSymplectic
        (oneHighLegHighModeOutput μ 1)
        (oneHighLegHighModeOutput μ Complex.I) =
      1 + ∑ j, μ j ^ 2 := by
  rw [oneHighLegHighModeOutput_I,
    standardComplexSymplectic_I_mul, Fintype.sum_option]
  simp [oneHighLegHighModeOutput, Complex.normSq_ofReal, pow_two]

/-- Any proposed ambient comass constant which bounds the exhibited high-mode
plane is at least `1 + ∑ j, μ j²`.  The analytic ambient-comass interface is
deliberately an explicit premise. -/
theorem oneHighLeg_highModeTest {J : ℕ} (μ : Fin J → ℝ) (C : ℝ)
    (hC : standardComplexSymplectic
        (oneHighLegHighModeOutput μ 1)
        (oneHighLegHighModeOutput μ Complex.I) ≤ C) :
    1 + ∑ j, μ j ^ 2 ≤ C := by
  rw [oneHighLegHighMode_symplecticValue] at hC
  exact hC

/-- Index type for the base coordinate together with `J` resonances. -/
abbrev OneHighLegIndex (J : ℕ) := Option (Fin J)

/-- Manuscript shift index: the base coordinate has shift zero and the
`j`-th parameter has shift `j+1`. -/
def oneHighLegShift {J : ℕ} : OneHighLegIndex J → ℕ
  | none => 0
  | some j => j.1 + 1

/-- The `r`-th odd-mode contribution to the `(j,k)` entry of the resonance
matrix from equation (14.5) of the note. -/
def resonanceMatrixSummand (j k r : ℕ) : ℝ :=
  (16 / Real.pi) * (oddMode r : ℝ) /
    (((oddMode r + 2 * j : ℕ) : ℝ) ^ 2 *
      ((oddMode r + 2 * k : ℕ) : ℝ) ^ 2)

lemma resonanceMatrixSummand_nonneg (j k r : ℕ) :
    0 ≤ resonanceMatrixSummand j k r := by
  unfold resonanceMatrixSummand oddMode
  positivity

lemma resonanceMatrixSummand_comm (j k r : ℕ) :
    resonanceMatrixSummand j k r = resonanceMatrixSummand k j r := by
  unfold resonanceMatrixSummand
  ring

private lemma resonanceMatrixSummand_le_oddCubic (j k r : ℕ) :
    resonanceMatrixSummand j k r ≤
      (16 / Real.pi) * oddCubicTerm r := by
  unfold resonanceMatrixSummand oddCubicTerm oddMode
  push_cast
  have hr : 0 < (2 * (r : ℝ) + 1) := by positivity
  have hj : 2 * (r : ℝ) + 1 ≤ 2 * (r : ℝ) + 1 + 2 * (j : ℝ) := by
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (Nat.cast_nonneg j : 0 ≤ (j : ℝ)))
  have hk : 2 * (r : ℝ) + 1 ≤ 2 * (r : ℝ) + 1 + 2 * (k : ℝ) := by
    exact le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (Nat.cast_nonneg k : 0 ≤ (k : ℝ)))
  have hjpos : 0 < 2 * (r : ℝ) + 1 + 2 * (j : ℝ) := lt_of_lt_of_le hr hj
  have hkpos : 0 < 2 * (r : ℝ) + 1 + 2 * (k : ℝ) := lt_of_lt_of_le hr hk
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 16 / Real.pi)
  apply (div_le_div_iff₀
    (mul_pos (sq_pos_of_pos hjpos) (sq_pos_of_pos hkpos))
    (pow_pos hr 3)).2
  calc
    (2 * (r : ℝ) + 1) * (2 * (r : ℝ) + 1) ^ 3 =
        (2 * (r : ℝ) + 1) ^ 2 * (2 * (r : ℝ) + 1) ^ 2 := by ring
    _ ≤ (2 * (r : ℝ) + 1 + 2 * (j : ℝ)) ^ 2 *
        (2 * (r : ℝ) + 1 + 2 * (k : ℝ)) ^ 2 := by
      exact mul_le_mul (pow_le_pow_left₀ hr.le hj 2)
        (pow_le_pow_left₀ hr.le hk 2) (sq_nonneg _) (sq_nonneg _)
    _ = 1 * ((2 * (r : ℝ) + 1 + 2 * (j : ℝ)) ^ 2 *
        (2 * (r : ℝ) + 1 + 2 * (k : ℝ)) ^ 2) := by ring

/-- Absolute summability of every resonance-matrix entry series. -/
lemma summable_resonanceMatrixSummand (j k : ℕ) :
    Summable (resonanceMatrixSummand j k) := by
  apply Summable.of_nonneg_of_le
  · exact fun r ↦ resonanceMatrixSummand_nonneg j k r
  · exact fun r ↦ resonanceMatrixSummand_le_oddCubic j k r
  · exact summable_oddCubicTerm.mul_left (16 / Real.pi)

/-- An entry of the infinite-series resonance matrix. -/
def resonanceMatrixEntry (j k : ℕ) : ℝ :=
  ∑' r : ℕ, resonanceMatrixSummand j k r

/-- Entry formula exactly as displayed in equation (14.5), with positive odd
modes parametrized by `oddMode r`. -/
theorem resonanceMatrixEntry_eq_manuscript (j k : ℕ) :
    resonanceMatrixEntry j k =
      (16 / Real.pi) * ∑' r : ℕ,
        (oddMode r : ℝ) /
          (((oddMode r + 2 * j : ℕ) : ℝ) ^ 2 *
            ((oddMode r + 2 * k : ℕ) : ℝ) ^ 2) := by
  unfold resonanceMatrixEntry
  rw [← tsum_mul_left]
  apply tsum_congr
  intro r
  unfold resonanceMatrixSummand
  ring

lemma resonanceMatrixEntry_comm (j k : ℕ) :
    resonanceMatrixEntry j k = resonanceMatrixEntry k j := by
  apply tsum_congr
  exact resonanceMatrixSummand_comm j k

/-- The principal `(J+1) × (J+1)` resonance matrix, indexed by a base
coordinate and `J` normalized one-high-leg resonances. -/
def finiteResonanceMatrix (J : ℕ) :
    Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ :=
  fun j k ↦ resonanceMatrixEntry (oneHighLegShift j) (oneHighLegShift k)

/-- Each entry of the principal matrix is the corresponding displayed
odd-mode series from equation (14.5). -/
theorem finiteResonanceMatrix_apply_eq_manuscript (J : ℕ)
    (j k : OneHighLegIndex J) :
    finiteResonanceMatrix J j k =
      (16 / Real.pi) * ∑' r : ℕ,
        (oddMode r : ℝ) /
          (((oddMode r + 2 * oneHighLegShift j : ℕ) : ℝ) ^ 2 *
            ((oddMode r + 2 * oneHighLegShift k : ℕ) : ℝ) ^ 2) := by
  simpa [finiteResonanceMatrix] using
    resonanceMatrixEntry_eq_manuscript
      (oneHighLegShift j) (oneHighLegShift k)

lemma finiteResonanceMatrix_isHermitian (J : ℕ) :
    (finiteResonanceMatrix J).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro j k
  simp [finiteResonanceMatrix, resonanceMatrixEntry_comm]

/-- Reciprocal-square feature whose weighted Gram matrix is the resonance
matrix. -/
def resonanceFeature (j r : ℕ) : ℝ :=
  1 / (((oddMode r + 2 * j : ℕ) : ℝ) ^ 2)

lemma boundaryRadius_oddMode_shift_eq_feature (j r : ℕ) :
    boundaryRadius (oddMode r + 2 * j) =
      (4 / Real.pi) * resonanceFeature j r := by
  unfold boundaryRadius resonanceFeature
  ring

/-- Positive weight in the resonance Gram representation. -/
def resonanceWeight (r : ℕ) : ℝ :=
  (16 / Real.pi) * (oddMode r : ℝ)

lemma resonanceWeight_nonneg (r : ℕ) : 0 ≤ resonanceWeight r := by
  unfold resonanceWeight oddMode
  positivity

lemma resonanceMatrixSummand_eq_gram (j k r : ℕ) :
    resonanceMatrixSummand j k r =
      resonanceWeight r * resonanceFeature j r * resonanceFeature k r := by
  unfold resonanceMatrixSummand resonanceWeight resonanceFeature
  ring

/-- The `r`-th scalar quadratic contribution of an arbitrary finite vector. -/
def resonanceQuadraticSummand {J : ℕ}
    (x : OneHighLegIndex J → ℝ) (r : ℕ) : ℝ :=
  ∑ j, ∑ k,
    x j * resonanceMatrixSummand (oneHighLegShift j) (oneHighLegShift k) r * x k

lemma summable_resonanceQuadraticSummand {J : ℕ}
    (x : OneHighLegIndex J → ℝ) :
    Summable (resonanceQuadraticSummand x) := by
  unfold resonanceQuadraticSummand
  apply summable_sum
  intro j _
  apply summable_sum
  intro k _
  exact ((summable_resonanceMatrixSummand
    (oneHighLegShift j) (oneHighLegShift k)).mul_left (x j)).mul_right (x k)

/-- Every mode contribution is a nonnegative weighted square, making the
Gram positivity transparent. -/
theorem resonanceQuadraticSummand_eq_sq {J : ℕ}
    (x : OneHighLegIndex J → ℝ) (r : ℕ) :
    resonanceQuadraticSummand x r =
      resonanceWeight r *
        (∑ j, x j * resonanceFeature (oneHighLegShift j) r) ^ 2 := by
  unfold resonanceQuadraticSummand
  rw [pow_two, Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [resonanceMatrixSummand_eq_gram]
  ring

/-- The quadratic form of the finite resonance matrix is the convergent sum
of its odd-mode Gram contributions. -/
theorem finiteResonanceMatrix_quadratic_eq_tsum {J : ℕ}
    (x : OneHighLegIndex J → ℝ) :
    dotProduct x (finiteResonanceMatrix J *ᵥ x) =
      ∑' r, resonanceQuadraticSummand x r := by
  classical
  calc
    dotProduct x (finiteResonanceMatrix J *ᵥ x) =
        ∑ j, ∑ k,
          x j * (∑' r, resonanceMatrixSummand
            (oneHighLegShift j) (oneHighLegShift k) r) * x k := by
      simp only [dotProduct, Matrix.mulVec, finiteResonanceMatrix,
        resonanceMatrixEntry]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, ∑ k, ∑' r,
          x j * resonanceMatrixSummand
            (oneHighLegShift j) (oneHighLegShift k) r * x k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [← tsum_mul_left, ← tsum_mul_right]
    _ = ∑ j, ∑' r, ∑ k,
          x j * resonanceMatrixSummand
            (oneHighLegShift j) (oneHighLegShift k) r * x k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Summable.tsum_finsetSum]
      intro k _
      exact ((summable_resonanceMatrixSummand
        (oneHighLegShift j) (oneHighLegShift k)).mul_left (x j)).mul_right (x k)
    _ = ∑' r, ∑ j, ∑ k,
          x j * resonanceMatrixSummand
            (oneHighLegShift j) (oneHighLegShift k) r * x k := by
      rw [Summable.tsum_finsetSum]
      intro j _
      apply summable_sum
      intro k _
      exact ((summable_resonanceMatrixSummand
        (oneHighLegShift j) (oneHighLegShift k)).mul_left (x j)).mul_right (x k)
    _ = ∑' r, resonanceQuadraticSummand x r := by
      rfl

/-- The manuscript's finite principal resonance matrix is positive
semidefinite because it is an infinite positive weighted Gram sum. -/
theorem finiteResonanceMatrix_posSemidef (J : ℕ) :
    (finiteResonanceMatrix J).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (finiteResonanceMatrix_isHermitian J)
  intro x
  simp only [star_trivial]
  rw [finiteResonanceMatrix_quadratic_eq_tsum]
  apply tsum_nonneg
  intro r
  rw [resonanceQuadraticSummand_eq_sq]
  exact mul_nonneg (resonanceWeight_nonneg r) (sq_nonneg _)

/-- The augmented real parameter vector `x = (1, μ₁, …, μ_J)`. -/
def oneHighLegRealVector {J : ℕ} (μ : Fin J → ℝ) :
    OneHighLegIndex J → ℝ
  | none => 1
  | some j => μ j

/-- The boundary action in equation (14.4), written directly as its
convergent positive odd-mode series. -/
def finiteOneHighLegBoundaryAction {J : ℕ} (μ : Fin J → ℝ) : ℝ :=
  Real.pi * ∑' r : ℕ,
    (oddMode r : ℝ) *
      (∑ j : OneHighLegIndex J,
        oneHighLegRealVector μ j *
          boundaryRadius (oddMode r + 2 * oneHighLegShift j)) ^ 2

/-- The augmented parameter vector in Euclidean space. -/
def oneHighLegEuclideanVector {J : ℕ} (μ : Fin J → ℝ) :
    EuclideanSpace ℝ (OneHighLegIndex J) :=
  WithLp.toLp 2 (oneHighLegRealVector μ)

@[simp] lemma oneHighLegEuclideanVector_apply {J : ℕ}
    (μ : Fin J → ℝ) (i : OneHighLegIndex J) :
    oneHighLegEuclideanVector μ i = oneHighLegRealVector μ i := rfl

lemma oneHighLegEuclideanVector_ne_zero {J : ℕ} (μ : Fin J → ℝ) :
    oneHighLegEuclideanVector μ ≠ 0 := by
  intro h
  have hnone := congrArg (fun x : EuclideanSpace ℝ (OneHighLegIndex J) ↦ x none) h
  simp [oneHighLegEuclideanVector, oneHighLegRealVector] at hnone

/-- The normalization cost is exactly the Euclidean square norm of the
augmented parameter vector. -/
theorem norm_sq_oneHighLegEuclideanVector {J : ℕ} (μ : Fin J → ℝ) :
    ‖oneHighLegEuclideanVector μ‖ ^ 2 = 1 + ∑ j, μ j ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
  simp [oneHighLegEuclideanVector, oneHighLegRealVector]

/-- Quadratic boundary action associated with a finite matrix. -/
def finiteOneHighLegQuadratic {J : ℕ}
    (M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ)
    (μ : Fin J → ℝ) : ℝ :=
  dotProduct (oneHighLegRealVector μ)
    (M *ᵥ oneHighLegRealVector μ)

private lemma oneHighLegBoundaryActionSummand_eq {J : ℕ}
    (μ : Fin J → ℝ) (r : ℕ) :
    Real.pi * ((oddMode r : ℝ) *
      (∑ j : OneHighLegIndex J,
        oneHighLegRealVector μ j *
          boundaryRadius (oddMode r + 2 * oneHighLegShift j)) ^ 2) =
      resonanceQuadraticSummand (oneHighLegRealVector μ) r := by
  rw [resonanceQuadraticSummand_eq_sq]
  have hsum :
      (∑ j : OneHighLegIndex J,
        oneHighLegRealVector μ j *
          boundaryRadius (oddMode r + 2 * oneHighLegShift j)) =
        (4 / Real.pi) *
          ∑ j : OneHighLegIndex J,
            oneHighLegRealVector μ j *
              resonanceFeature (oneHighLegShift j) r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [boundaryRadius_oddMode_shift_eq_feature]
    ring
  rw [hsum]
  unfold resonanceWeight
  field_simp [Real.pi_ne_zero]
  ring

/-- Summability of the positive odd-mode series defining the finite boundary
action. -/
lemma summable_finiteOneHighLegBoundaryActionCore {J : ℕ}
    (μ : Fin J → ℝ) :
    Summable (fun r : ℕ ↦
      (oddMode r : ℝ) *
        (∑ j : OneHighLegIndex J,
          oneHighLegRealVector μ j *
            boundaryRadius (oddMode r + 2 * oneHighLegShift j)) ^ 2) := by
  refine ((summable_resonanceQuadraticSummand
    (oneHighLegRealVector μ)).mul_left (1 / Real.pi)).congr ?_
  intro r
  rw [← oneHighLegBoundaryActionSummand_eq μ r]
  field_simp [Real.pi_ne_zero]

/-- Exact identification of the manuscript boundary series with the quadratic
form of its finite principal resonance matrix. -/
theorem finiteOneHighLegBoundaryAction_eq_quadratic {J : ℕ}
    (μ : Fin J → ℝ) :
    finiteOneHighLegBoundaryAction μ =
      finiteOneHighLegQuadratic (finiteResonanceMatrix J) μ := by
  unfold finiteOneHighLegBoundaryAction finiteOneHighLegQuadratic
  rw [finiteResonanceMatrix_quadratic_eq_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  exact oneHighLegBoundaryActionSummand_eq μ

/-- The largest Rayleigh value of a finite matrix.  Symmetry will imply below
that this value is an actual eigenvalue. -/
def finiteLargestRayleighValue {J : ℕ}
    (M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ) : ℝ :=
  let T := M.toEuclideanLin.toContinuousLinearMap
  ⨆ x : {x : EuclideanSpace ℝ (OneHighLegIndex J) // x ≠ 0},
    T.rayleighQuotient x

private lemma finiteOneHighLegQuadratic_eq_reApplyInnerSelf {J : ℕ}
    (M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ)
    (μ : Fin J → ℝ) :
    finiteOneHighLegQuadratic M μ =
      M.toEuclideanLin.toContinuousLinearMap.reApplyInnerSelf
        (oneHighLegEuclideanVector μ) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change
    dotProduct (oneHighLegRealVector μ) (M *ᵥ oneHighLegRealVector μ) =
      dotProduct (oneHighLegRealVector μ)
        (star (M *ᵥ oneHighLegRealVector μ))
  simp

private lemma finiteLargestRayleighValue_bddAbove {J : ℕ}
    (M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ) :
    BddAbove (Set.range (fun x :
        {x : EuclideanSpace ℝ (OneHighLegIndex J) // x ≠ 0} ↦
      M.toEuclideanLin.toContinuousLinearMap.rayleighQuotient x)) := by
  let T := M.toEuclideanLin.toContinuousLinearMap
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact le_trans (le_abs_self _) (T.rayleighQuotient_le_norm x)

/-- For a symmetric finite matrix, the largest Rayleigh value is an actual
eigenvalue. -/
theorem finiteLargestRayleighValue_hasEigenvalue {J : ℕ}
    {M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ}
    (hM : M.IsHermitian) :
    HasEigenvalue M.toEuclideanLin (finiteLargestRayleighValue M) := by
  have hsymmetric : M.toEuclideanLin.IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hM
  simpa [finiteLargestRayleighValue,
    ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply] using
      hsymmetric.hasEigenvalue_iSup_of_finiteDimensional

/-- Finite Rayleigh ceiling: a positive-semidefinite quadratic boundary action
divided by any comass bound at least `1 + ∑ j, μ j²` is bounded by the
matrix's largest eigenvalue. -/
theorem finiteOneHighLeg_rayleighCeiling {J : ℕ}
    (M : Matrix (OneHighLegIndex J) (OneHighLegIndex J) ℝ)
    (hM : M.PosSemidef) (μ : Fin J → ℝ) (C : ℝ)
    (hC : 1 + ∑ j, μ j ^ 2 ≤ C) :
    finiteOneHighLegQuadratic M μ / C ≤ finiteLargestRayleighValue M := by
  let x := oneHighLegEuclideanVector μ
  let T := M.toEuclideanLin.toContinuousLinearMap
  have hx : x ≠ 0 := oneHighLegEuclideanVector_ne_zero μ
  have hnorm : ‖x‖ ^ 2 = 1 + ∑ j, μ j ^ 2 :=
    norm_sq_oneHighLegEuclideanVector μ
  have hnorm_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hnorm_le : ‖x‖ ^ 2 ≤ C := by simpa [hnorm] using hC
  have hquadratic_nonneg : 0 ≤ finiteOneHighLegQuadratic M μ := by
    simpa [finiteOneHighLegQuadratic] using
      hM.dotProduct_mulVec_nonneg (oneHighLegRealVector μ)
  calc
    finiteOneHighLegQuadratic M μ / C ≤
        finiteOneHighLegQuadratic M μ / ‖x‖ ^ 2 :=
      div_le_div_of_nonneg_left hquadratic_nonneg hnorm_pos hnorm_le
    _ = T.rayleighQuotient x := by
      rw [ContinuousLinearMap.rayleighQuotient,
        ← finiteOneHighLegQuadratic_eq_reApplyInnerSelf M μ]
    _ ≤ finiteLargestRayleighValue M := by
      unfold finiteLargestRayleighValue
      exact le_ciSup (finiteLargestRayleighValue_bddAbove M) ⟨x, hx⟩

/-- The largest Rayleigh value of the manuscript's finite resonance matrix is
an eigenvalue of that matrix. -/
theorem finiteResonanceMatrix_largestRayleigh_hasEigenvalue (J : ℕ) :
    HasEigenvalue (finiteResonanceMatrix J).toEuclideanLin
      (finiteLargestRayleighValue (finiteResonanceMatrix J)) :=
  finiteLargestRayleighValue_hasEigenvalue
    (finiteResonanceMatrix_isHermitian J)

/-- Finite one-high-leg ceiling at the explicit high-mode interface.  A
global ambient comass bound supplies the premise by bounding this exhibited
admissible plane. -/
theorem finiteOneHighLeg_ceiling_of_highModeBound {J : ℕ}
    (μ : Fin J → ℝ) (C : ℝ)
    (hC : standardComplexSymplectic
        (oneHighLegHighModeOutput μ 1)
        (oneHighLegHighModeOutput μ Complex.I) ≤ C) :
    finiteOneHighLegBoundaryAction μ / C ≤
      finiteLargestRayleighValue (finiteResonanceMatrix J) := by
  rw [finiteOneHighLegBoundaryAction_eq_quadratic]
  exact finiteOneHighLeg_rayleighCeiling
    (finiteResonanceMatrix J) (finiteResonanceMatrix_posSemidef J) μ C
      (oneHighLeg_highModeTest μ C hC)

end

end GromovFilling
