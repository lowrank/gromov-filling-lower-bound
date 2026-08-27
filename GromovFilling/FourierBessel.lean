import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Dual
import GromovFilling.ComplexJacobianBudget
import GromovFilling.Universal

/-!
# Finite Fourier--Bessel inequalities

This file extracts the finite inequalities used in the derivative-energy
part of Lemma 5.4 from mathlib's Parseval theorem on an interval.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GromovFilling

noncomputable section

/-- Every finite collection of interval Fourier coefficients is bounded by
the normalized `L²` energy.  This is the exact finite Bessel inequality
obtained from Parseval, with no convergence assumption beyond `MemLp`. -/
theorem finset_sum_norm_fourierCoeffOn_sq_le
    {a b : ℝ} {f : ℝ → ℂ} (hab : a < b)
    (hL2 : MemLp f 2 (volume.restrict (Ioc a b))) (s : Finset ℤ) :
    (∑ i ∈ s, ‖fourierCoeffOn hab f i‖ ^ 2) ≤
      (b - a)⁻¹ • ∫ x in a..b, ‖f x‖ ^ 2 := by
  have hparseval := hasSum_sq_fourierCoeffOn hab hL2
  rw [← hparseval.tsum_eq]
  exact hparseval.summable.sum_le_tsum s
    (fun i _ ↦ sq_nonneg ‖fourierCoeffOn hab f i‖)

private theorem fourierCoeff_neg_eq_conj_of_conj_eq
    {T : ℝ} [Fact (0 < T)] (g : AddCircle T → ℂ)
    (hreal : ∀ x, conj (g x) = g x) (n : ℤ) :
    fourierCoeff g (-n) = conj (fourierCoeff g n) := by
  unfold fourierCoeff
  simp only [neg_neg, smul_eq_mul]
  calc
    (∫ t, fourier n t * g t ∂AddCircle.haarAddCircle) =
        ∫ t, conj (fourier (-n) t * g t)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [map_mul, hreal]
      simp
    _ = conj (∫ t, fourier (-n) t * g t
          ∂AddCircle.haarAddCircle) := integral_conj

/-- Fourier coefficients of a real-valued function have the usual
conjugate symmetry.  The statement is kept at the interval-coefficient
level so its normalization agrees definitionally with Parseval above. -/
theorem fourierCoeffOn_neg_eq_conj_of_real
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (n : ℤ) :
    fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-n) =
      conj (fourierCoeffOn hab (fun x ↦ (f x : ℂ)) n) := by
  letI : Fact (0 < b - a) := ⟨by linarith⟩
  unfold fourierCoeffOn
  apply fourierCoeff_neg_eq_conj_of_conj_eq
  intro x
  change conj ((AddCircle.liftIoc (b - a) a
    (fun y ↦ (f y : ℂ))) x) = _
  rw [show (fun y ↦ (f y : ℂ)) = Complex.ofReal ∘ f by rfl,
    AddCircle.liftIoc_comp_apply]
  simp

/-- In particular, opposite real Fourier modes have equal norm. -/
theorem norm_fourierCoeffOn_neg_eq_of_real
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) (n : ℤ) :
    ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-n)‖ =
      ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) n‖ := by
  rw [fourierCoeffOn_neg_eq_conj_of_real hab f n, Complex.norm_conj]

/-- Sharp finite Bessel inequality for any injective family of positive
real Fourier modes.  Both signs are inserted into Parseval; conjugate
symmetry then turns their combined contribution into twice the energy of
the chosen negative coefficients. -/
theorem two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hL2 : MemLp (fun x ↦ (f x : ℂ)) 2
      (volume.restrict (Ioc a b)))
    (m : ι → ℕ) (hm : Function.Injective m)
    (hmpos : ∀ k, 0 < m k) :
    2 * (∑ k : ι,
      ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-(m k : ℤ))‖ ^ 2) ≤
      (b - a)⁻¹ • ∫ x in a..b, ‖(f x : ℂ)‖ ^ 2 := by
  classical
  let p : Finset ℤ := Finset.univ.image (fun k : ι ↦ (m k : ℤ))
  let q : Finset ℤ := Finset.univ.image (fun k : ι ↦ -(m k : ℤ))
  have hmInt : Function.Injective (fun k : ι ↦ (m k : ℤ)) := by
    intro k l hkl
    apply hm
    exact Int.ofNat_inj.mp hkl
  have hmNeg : Function.Injective (fun k : ι ↦ -(m k : ℤ)) := by
    intro k l hkl
    apply hmInt
    exact neg_injective hkl
  have hpq : Disjoint p q := by
    rw [Finset.disjoint_left]
    intro z hzp hzq
    rw [Finset.mem_image] at hzp hzq
    obtain ⟨k, _hk, rfl⟩ := hzp
    obtain ⟨l, _hl, hkl⟩ := hzq
    have hkpos : (0 : ℤ) < (m k : ℤ) := by exact_mod_cast hmpos k
    have hlpos : (0 : ℤ) < (m l : ℤ) := by exact_mod_cast hmpos l
    omega
  have hpSum :
      (∑ i ∈ p,
        ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) i‖ ^ 2) =
        ∑ k : ι,
          ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (m k : ℤ)‖ ^ 2 := by
    unfold p
    rw [Finset.sum_image
      (fun k _hk l _hl hkl ↦ hmInt hkl)]
  have hqSum :
      (∑ i ∈ q,
        ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) i‖ ^ 2) =
        ∑ k : ι,
          ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-(m k : ℤ))‖ ^ 2 := by
    unfold q
    rw [Finset.sum_image
      (fun k _hk l _hl hkl ↦ hmNeg hkl)]
  have hposSum :
      (∑ k : ι,
        ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (m k : ℤ)‖ ^ 2) =
        ∑ k : ι,
          ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-(m k : ℤ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [norm_fourierCoeffOn_neg_eq_of_real hab f (m k : ℤ)]
  calc
    2 * (∑ k : ι,
        ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) (-(m k : ℤ))‖ ^ 2) =
        (∑ i ∈ p,
          ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) i‖ ^ 2) +
        ∑ i ∈ q,
          ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) i‖ ^ 2 := by
      rw [hpSum, hqSum, hposSum]
      ring
    _ = ∑ i ∈ p ∪ q,
        ‖fourierCoeffOn hab (fun x ↦ (f x : ℂ)) i‖ ^ 2 := by
      rw [Finset.sum_union hpq]
    _ ≤ (b - a)⁻¹ • ∫ x in a..b, ‖(f x : ℂ)‖ ^ 2 :=
      finset_sum_norm_fourierCoeffOn_sq_le hab hL2 (p ∪ q)

/-- The normalization step in the derivative-energy proof of Lemma 5.4.
If the two columns of a family of complex derivatives are twice the
negative odd Fourier coefficients of two real `L²` fields, then their
total Hilbert--Schmidt energy is at most `2` as soon as the normalized
energies of those fields satisfy the displayed unit bound. -/
theorem sum_complexDerivativeEnergy_le_two_of_fourierCoeffOn
    {a b : ℝ} (hab : a < b) (N : ℕ)
    (f₁ fI : ℝ → ℝ)
    (hL2₁ : MemLp (fun x ↦ (f₁ x : ℂ)) 2
      (volume.restrict (Ioc a b)))
    (hL2I : MemLp (fun x ↦ (fI x : ℂ)) 2
      (volume.restrict (Ioc a b)))
    (L : Fin N → ℂ →L[ℝ] ℂ)
    (hLone : ∀ k,
      L k 1 = 2 * fourierCoeffOn hab (fun x ↦ (f₁ x : ℂ))
        (-(oddMode k : ℤ)))
    (hLI : ∀ k,
      L k Complex.I = 2 * fourierCoeffOn hab (fun x ↦ (fI x : ℂ))
        (-(oddMode k : ℤ)))
    (hfieldEnergy :
      2 * ((b - a)⁻¹ * ∫ x in a..b, ‖(f₁ x : ℂ)‖ ^ 2) +
      2 * ((b - a)⁻¹ * ∫ x in a..b, ‖(fI x : ℂ)‖ ^ 2) ≤ 2) :
    (∑ k : Fin N, complexDerivativeEnergy (L k)) ≤ 2 := by
  have hoddinj : Function.Injective (fun k : Fin N ↦ oddMode k) := by
    intro k l hkl
    apply Fin.val_injective
    have hval : 2 * k.val + 1 = 2 * l.val + 1 := by
      simpa only [oddMode] using hkl
    omega
  have hoddpos : ∀ k : Fin N, 0 < oddMode k := by
    intro k
    unfold oddMode
    omega
  have hb₁ := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab f₁ hL2₁ (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  have hbI := two_mul_sum_norm_fourierCoeffOn_neg_sq_le
    hab fI hL2I (fun k : Fin N ↦ oddMode k) hoddinj hoddpos
  simp only [smul_eq_mul] at hb₁ hbI
  have hrewrite :
      (∑ k : Fin N, complexDerivativeEnergy (L k)) =
        4 * (∑ k : Fin N,
          ‖fourierCoeffOn hab (fun x ↦ (f₁ x : ℂ))
            (-(oddMode k : ℤ))‖ ^ 2) +
        4 * (∑ k : Fin N,
          ‖fourierCoeffOn hab (fun x ↦ (fI x : ℂ))
            (-(oddMode k : ℤ))‖ ^ 2) := by
    simp_rw [complexDerivativeEnergy, Complex.normSq_eq_norm_sq,
      hLone, hLI, norm_mul]
    simp_rw [mul_pow]
    norm_num
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hrewrite]
  linarith

/-- The squared norm of a real covector on `ℂ` is the sum of its squares
on the standard orthonormal basis `(1,I)`. -/
theorem realCovector_apply_one_sq_add_apply_I_sq
    (D : ℂ →L[ℝ] ℝ) :
    (D 1) ^ 2 + (D Complex.I) ^ 2 = ‖D‖ ^ 2 := by
  have h := Complex.orthonormalBasisOneI.norm_dual D
  rw [Complex.coe_orthonormalBasisOneI] at h
  simpa [Fin.sum_univ_two] using h.symm

/-- A real covector of operator norm at most one has at most unit total
energy on `(1,I)`. -/
theorem realCovector_basis_energy_le_one
    (D : ℂ →L[ℝ] ℝ) (hD : ‖D‖ ≤ 1) :
    (D 1) ^ 2 + (D Complex.I) ^ 2 ≤ 1 := by
  rw [realCovector_apply_one_sq_add_apply_I_sq]
  nlinarith [norm_nonneg D]

end

end GromovFilling
