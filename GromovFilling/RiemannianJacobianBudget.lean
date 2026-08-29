import GromovFilling.RiemannianInteriorAtlasArea
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Intrinsic Riemannian Jacobian budgets

This file supplies the coordinate-free energy-to-Jacobian bridge used by
the Fourier budget on a Riemannian surface.  In any orthonormal source
basis, the intrinsic two-Jacobian is at most half the Hilbert--Schmidt
energy.  The pointwise inequality is then summed over a finite family and
integrated against an arbitrary measure.
-/

open Bundle MeasureTheory
open scoped BigOperators Bundle ENNReal InnerProductSpace Manifold NNReal

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The intrinsic two-Jacobian is at most half the Hilbert--Schmidt energy
computed in any orthonormal source basis. -/
theorem twoJacobian_le_half_orthonormalBasis_energy
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (e : OrthonormalBasis (Fin 2) ℝ E) (L : E →L[ℝ] F) :
    twoJacobian L ≤ (‖L (e 0)‖ ^ 2 + ‖L (e 1)‖ ^ 2) / 2 := by
  let o : Orientation ℝ F (Fin 2) :=
    (canonicalOrthonormalBasisTwo F).toBasis.orientation
  rw [twoJacobian_eq_abs_areaForm e o]
  calc
    |o.areaForm (L (e 0)) (L (e 1))| ≤
        ‖L (e 0)‖ * ‖L (e 1)‖ :=
      o.abs_areaForm_le _ _
    _ ≤ (‖L (e 0)‖ ^ 2 + ‖L (e 1)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖L (e 0)‖ - ‖L (e 1)‖)]

/-- The manifold differential of a complex-valued function, with the
Euclidean target tangent fiber canonically identified with `ℂ`. -/
def riemannianComplexMFDeriv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (G : M → ℂ) (x : M) : TangentSpace I x →L[ℝ] ℂ :=
  (NormedSpace.fromTangentSpace (G x)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, ℂ) G x)

/-- Hilbert--Schmidt energy of a complex-valued manifold differential in a
chosen orthonormal tangent basis. -/
def riemannianComplexDerivativeEnergy
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (x : M) (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (G : M → ℂ) : ℝ :=
  ‖riemannianComplexMFDeriv I G x (e 0)‖ ^ 2 +
    ‖riemannianComplexMFDeriv I G x (e 1)‖ ^ 2

/-- Intrinsic surface specialization of the half-energy Jacobian bound. -/
theorem riemannianTwoJacobian_le_half_derivativeEnergy
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (G : M → ℂ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x)) :
    riemannianTwoJacobian I G x ≤
      riemannianComplexDerivativeEnergy I x e G / 2 := by
  letI : Fact (Module.finrank ℝ (TangentSpace I x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I x⟩
  letI : Fact (Module.finrank ℝ ℂ = 2) :=
    Complex.finrank_real_complex_fact
  unfold riemannianTwoJacobian riemannianComplexDerivativeEnergy
  exact twoJacobian_le_half_orthonormalBasis_energy e
    (riemannianComplexMFDeriv I G x)

/-- A total Hilbert--Schmidt energy budget of two gives a unit intrinsic
two-Jacobian budget for every finite family of surface maps. -/
theorem sum_riemannianTwoJacobian_le_one_of_derivativeEnergy
    {ι E H M : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (G : ι → M → ℂ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (henergy :
      (∑ j, riemannianComplexDerivativeEnergy I x e (G j)) ≤ 2) :
    (∑ j, riemannianTwoJacobian I (G j) x) ≤ 1 := by
  have hJ : (∑ j, riemannianTwoJacobian I (G j) x) ≤
      (∑ j, riemannianComplexDerivativeEnergy I x e (G j)) / 2 := by
    calc
      (∑ j, riemannianTwoJacobian I (G j) x) ≤
          ∑ j, riemannianComplexDerivativeEnergy I x e (G j) / 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact riemannianTwoJacobian_le_half_derivativeEnergy I (G j) x e
      _ = (∑ j, riemannianComplexDerivativeEnergy I x e (G j)) / 2 := by
        rw [Finset.sum_div]
  linarith

/-- An almost-everywhere unit intrinsic Jacobian budget integrates to the
mass of the underlying measure.  Almost-everywhere measurability is an
explicit input because later applications obtain it from controlled
Riemannian charts. -/
theorem sum_lintegral_riemannianTwoJacobian_le_measure
    {ι E H M : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [MeasurableSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (μ : Measure M) (G : ι → M → ℂ)
    (hmeas : ∀ j, AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I (G j) x)) μ)
    (hbudget : ∀ᵐ x ∂μ,
      (∑ j, riemannianTwoJacobian I (G j) x) ≤ 1) :
    (∑ j, ∫⁻ x,
      ENNReal.ofReal (riemannianTwoJacobian I (G j) x) ∂μ) ≤
      μ Set.univ := by
  rw [← lintegral_finset_sum' Finset.univ (fun j _ ↦ hmeas j)]
  calc
    (∫⁻ x, ∑ j,
        ENNReal.ofReal (riemannianTwoJacobian I (G j) x) ∂μ) ≤
        ∫⁻ _x, ENNReal.ofReal 1 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbudget] with x hx
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal hx
      · intro j _
        exact riemannianTwoJacobian_nonneg I (G j) x
    _ = μ Set.univ := by simp

/-- The intrinsic two-Jacobian of a globally Lipschitz complex-valued map is
almost everywhere measurable for the canonical Riemannian surface-area
measure. -/
theorem aemeasurable_riemannianTwoJacobian_surfaceAreaMeasure_of_lipschitzWith
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    (G : M → ℂ) {KG : ℝ≥0} (hG : LipschitzWith KG G) :
    AEMeasurable
      (fun x ↦ ENNReal.ofReal (riemannianTwoJacobian I G x))
      (riemannianSurfaceAreaMeasure I) := by
  let A : ControlledInteriorAtlas I M :=
    Classical.choice (inferInstance : Nonempty (ControlledInteriorAtlas I M))
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  exact AEMeasurable.sum_measure fun i ↦
    A.aemeasurable_riemannianTwoJacobian_of_lipschitzWith I G hG i

/-- Canonical-surface specialization of the integrated finite-family
Jacobian budget.  Measurability is discharged automatically from global
Lipschitz regularity. -/
theorem sum_lintegral_riemannianTwoJacobian_le_surfaceAreaMeasure
    {ι E H M : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    (G : ι → M → ℂ) (K : ι → ℝ≥0)
    (hG : ∀ j, LipschitzWith (K j) (G j))
    (hbudget : ∀ᵐ x ∂riemannianSurfaceAreaMeasure I,
      (∑ j, riemannianTwoJacobian I (G j) x) ≤ 1) :
    (∑ j, ∫⁻ x,
      ENNReal.ofReal (riemannianTwoJacobian I (G j) x)
        ∂riemannianSurfaceAreaMeasure I) ≤
      riemannianSurfaceAreaMeasure I (Set.univ : Set M) := by
  exact sum_lintegral_riemannianTwoJacobian_le_measure I
    (riemannianSurfaceAreaMeasure I) G
    (fun j ↦
      aemeasurable_riemannianTwoJacobian_surfaceAreaMeasure_of_lipschitzWith
        I (G j) (hG j)) hbudget

end

end GromovFilling

#print axioms GromovFilling.riemannianTwoJacobian_le_half_derivativeEnergy
#print axioms GromovFilling.sum_riemannianTwoJacobian_le_one_of_derivativeEnergy
#print axioms GromovFilling.sum_lintegral_riemannianTwoJacobian_le_measure
#print axioms GromovFilling.sum_lintegral_riemannianTwoJacobian_le_surfaceAreaMeasure
