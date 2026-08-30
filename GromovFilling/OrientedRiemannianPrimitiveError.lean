import GromovFilling.OrientedRiemannianDensity

/-!
# Intrinsic oriented primitive-error densities

The partition-of-unity localization of finite symplectic Stokes produces a
cutoff-derivative term.  This module expresses that term intrinsically on a
Riemannian surface and proves its finite pointwise cancellation when the
cutoffs add to one.

Chart pullback and integration are kept separate: the result here is the
coordinate-free algebraic cancellation needed by the global oriented
boundary-atlas argument.
-/

open Bundle Manifold
open scoped BigOperators Bundle InnerProductSpace Manifold

namespace GromovFilling

noncomputable section

/-- The manifold differential of a real-valued function, with the Euclidean
target tangent fiber canonically identified with `ℝ`. -/
def riemannianRealMFDeriv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (ρ : M → ℝ) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  (NormedSpace.fromTangentSpace (ρ x)).toContinuousLinearMap.comp
    (mfderiv I 𝓘(ℝ, ℝ) ρ x)

/-- The pullback of the standard finite symplectic primitive by the
Riemannian differential of a finite complex-valued map. -/
def finiteComplexRiemannianPrimitive
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (G : M → ι → ℂ) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  (standardComplexSymplecticPrimitive (G x)).comp
    (finiteComplexRiemannianDerivative I G x)

/-- The oriented scalar density of `dρ ∧ G⁎α`, where `α` is the standard
finite symplectic primitive.  The selected positive orthonormal frame fixes
the sign; the alternating expression itself is frame-independent. -/
def orientedFiniteComplexRiemannianPrimitiveErrorDensity
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : M → ℝ) (G : M → ι → ℂ) (x : M) : ℝ :=
  let e := o.positiveOrthonormalBasis I x
  riemannianRealMFDeriv I ρ x (e 1) *
      finiteComplexRiemannianPrimitive I G x (e 0) -
    riemannianRealMFDeriv I ρ x (e 0) *
      finiteComplexRiemannianPrimitive I G x (e 1)

/-- The Riemannian differentials of finitely many differentiable real
cutoffs sum to zero when the cutoffs add pointwise to one. -/
theorem sum_riemannianRealMFDeriv_eq_zero_of_sum_eq_one
    {E H M κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype κ]
    (ρ : κ → M → ℝ) (x : M)
    (hρ : ∀ j, MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ j) x)
    (hsum : ∀ y, ∑ j, ρ j y = 1) :
    ∑ j, riemannianRealMFDeriv I (ρ j) x = 0 := by
  have hhas : HasMFDerivAt I 𝓘(ℝ, ℝ)
      (∑ j : κ, ρ j) x
      (∑ j : κ, mfderiv I 𝓘(ℝ, ℝ) (ρ j) x) := by
    exact HasMFDerivAt.sum fun j _hj ↦ (hρ j).hasMFDerivAt
  have hfun : (∑ j : κ, ρ j) = fun _y : M ↦ (1 : ℝ) := by
    funext y
    exact hsum y
  have hraw : (∑ j : κ, mfderiv I 𝓘(ℝ, ℝ) (ρ j) x) = 0 := by
    rw [← hhas.mfderiv, hfun, mfderiv_const]
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg
    (fun L : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (1 : ℝ) ↦ L v)
    hraw
  simpa only [riemannianRealMFDeriv,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, NormedSpace.fromTangentSpace] using hv

/-- The intrinsic primitive-error densities of a finite differentiable
partition of unity cancel pointwise. -/
theorem sum_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero
    {E H M κ ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype κ]
    [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : κ → M → ℝ) (G : M → ι → ℂ) (x : M)
    (hρ : ∀ j, MDifferentiableAt I 𝓘(ℝ, ℝ) (ρ j) x)
    (hsum : ∀ y, ∑ j, ρ j y = 1) :
    ∑ j, orientedFiniteComplexRiemannianPrimitiveErrorDensity
      I o (ρ j) G x = 0 := by
  let e := o.positiveOrthonormalBasis I x
  let A := finiteComplexRiemannianPrimitive I G x
  have hD := sum_riemannianRealMFDeriv_eq_zero_of_sum_eq_one
    I ρ x hρ hsum
  have hD0 : (∑ j, riemannianRealMFDeriv I (ρ j) x (e 0)) = 0 := by
    have h := congrArg
      (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L (e 0)) hD
    simpa only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.zero_apply] using h
  have hD1 : (∑ j, riemannianRealMFDeriv I (ρ j) x (e 1)) = 0 := by
    have h := congrArg
      (fun L : TangentSpace I x →L[ℝ] ℝ ↦ L (e 1)) hD
    simpa only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.zero_apply] using h
  change (∑ j, riemannianRealMFDeriv I (ρ j) x (e 1) * A (e 0) -
    riemannianRealMFDeriv I (ρ j) x (e 0) * A (e 1)) = 0
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    hD1, hD0]
  ring

#print axioms riemannianRealMFDeriv
#print axioms finiteComplexRiemannianPrimitive
#print axioms orientedFiniteComplexRiemannianPrimitiveErrorDensity
#print axioms sum_riemannianRealMFDeriv_eq_zero_of_sum_eq_one
#print axioms
  sum_orientedFiniteComplexRiemannianPrimitiveErrorDensity_eq_zero

end

end GromovFilling
