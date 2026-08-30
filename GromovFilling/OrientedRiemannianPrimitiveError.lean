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

private theorem fromTangentSpace_real_toContinuousLinearMap (a : ℝ) :
    (NormedSpace.fromTangentSpace a).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ ℝ := by
  rfl

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
  classical
  have hhas : HasMFDerivAt I 𝓘(ℝ, ℝ)
      (∑ j : κ, ρ j) x
      (∑ j : κ, mfderiv I 𝓘(ℝ, ℝ) (ρ j) x) := by
    have hfinite : ∀ s : Finset κ,
        HasMFDerivAt I 𝓘(ℝ, ℝ)
          (∑ j ∈ s, ρ j) x
          (∑ j ∈ s,
            (mfderiv I 𝓘(ℝ, ℝ) (ρ j) x :
              TangentSpace I x →L[ℝ] ℝ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using
            (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ))
              (0 : ℝ) x)
      | @insert j s hj ih =>
          have hfun_insert :
              (∑ k ∈ insert j s, ρ k) =
                ρ j + ∑ k ∈ s, ρ k := by
            rw [Finset.sum_insert hj]
          have hderiv_insert :
              (∑ k ∈ insert j s,
                  (mfderiv I 𝓘(ℝ, ℝ) (ρ k) x :
                    TangentSpace I x →L[ℝ] ℝ)) =
                (mfderiv I 𝓘(ℝ, ℝ) (ρ j) x :
                    TangentSpace I x →L[ℝ] ℝ) +
                  ∑ k ∈ s,
                    (mfderiv I 𝓘(ℝ, ℝ) (ρ k) x :
                      TangentSpace I x →L[ℝ] ℝ) := by
            rw [Finset.sum_insert hj]
          have hadd := (hρ j).hasMFDerivAt.add ih
          rw [← hfun_insert, ← hderiv_insert] at hadd
          exact hadd
    simpa using hfinite Finset.univ
  have hfun : (∑ j : κ, ρ j) = fun _y : M ↦ (1 : ℝ) := by
    funext y
    simpa only [Finset.sum_apply] using hsum y
  have hraw : (∑ j : κ,
      (mfderiv I 𝓘(ℝ, ℝ) (ρ j) x : TangentSpace I x →L[ℝ] ℝ)) =
      (0 : TangentSpace I x →L[ℝ] ℝ) := by
    calc
      (∑ j : κ, mfderiv I 𝓘(ℝ, ℝ) (ρ j) x) =
          mfderiv I 𝓘(ℝ, ℝ) (∑ j : κ, ρ j) x := hhas.mfderiv.symm
      _ = mfderiv I 𝓘(ℝ, ℝ) (fun _y : M ↦ (1 : ℝ)) x := by rw [hfun]
      _ = 0 := mfderiv_const
  simpa only [riemannianRealMFDeriv,
    fromTangentSpace_real_toContinuousLinearMap,
    ContinuousLinearMap.id_comp] using hraw

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
  change (∑ j, (riemannianRealMFDeriv I (ρ j) x (e 1) * A (e 0) -
    riemannianRealMFDeriv I (ρ j) x (e 0) * A (e 1))) = 0
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
