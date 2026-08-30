import GromovFilling.FiniteSymplecticPrimitiveTransition
import GromovFilling.OrientedRiemannianChartDensity
import GromovFilling.OrientedRiemannianPrimitiveError

/-!
# Intrinsic primitive-error densities in oriented Riemannian charts

This module identifies the planar cutoff-primitive error produced by localized
weak Stokes with its intrinsic oriented Riemannian density.  The chart
derivative contributes the same signed Jacobian as it does for the symplectic
density itself.
-/

open Bundle Manifold
open scoped Bundle InnerProductSpace Manifold

namespace GromovFilling

noncomputable section

private theorem fromTangentSpace_real_toContinuousLinearMap (a : ℝ) :
    (NormedSpace.fromTangentSpace a).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ ℝ := by
  rfl

/-- The alternating pairing of two real covectors on an oriented Euclidean
plane is its value in a positive orthonormal frame times the area form. -/
theorem alternatingContinuousLinearPair_eq_areaForm_mul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (a b : V →L[ℝ] ℝ) (o : Orientation ℝ V (Fin 2))
    (e : OrthonormalBasis (Fin 2) ℝ V)
    (he : e.toBasis.orientation = o) (u v : V) :
    a v * b u - a u * b v =
      o.areaForm u v * (a (e 1) * b (e 0) - a (e 0) * b (e 1)) := by
  let L₀ : V →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp b +
      Complex.I • Complex.ofRealCLM.comp a
  let L : V →L[ℝ] (Fin 1 → ℂ) :=
    ContinuousLinearMap.pi fun _ : Fin 1 ↦ L₀
  have h := standardComplexSymplectic_eq_areaForm_mul_density
    L o e he u v
  have hpair (p q : V) :
      standardComplexSymplectic (L p) (L q) =
        a q * b p - a p * b q := by
    simp only [standardComplexSymplectic, L, L₀,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply]
    simp [Complex.mul_im]
    ring
  rw [hpair u v] at h
  unfold finiteComplexSymplecticDensityInFrame at h
  rw [hpair (e 0) (e 1)] at h
  exact h

/-- Real scalar manifold chain rule exposed before any Riemannian bundle
instances are introduced. -/
theorem fderiv_real_comp_parametrization_apply_eq_mfderiv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (ρ : M → ℝ) (F : ℂ → M) (z v : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (F z)) :
    fderiv ℝ (ρ ∘ F) z v =
      mfderiv I 𝓘(ℝ, ℝ) ρ (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z v) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp_apply z hρ hF v

/-- The cutoff-primitive error evaluated on the two oriented chart vectors. -/
def finiteComplexRiemannianChartPrimitiveErrorDensity
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (ρ : M → ℝ) (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ) : ℝ :=
  riemannianRealMFDeriv I ρ (F z)
      (orientedRiemannianChartVector I F z 1) *
    finiteComplexRiemannianPrimitive I G (F z)
      (orientedRiemannianChartVector I F z 0) -
  riemannianRealMFDeriv I ρ (F z)
      (orientedRiemannianChartVector I F z 0) *
    finiteComplexRiemannianPrimitive I G (F z)
      (orientedRiemannianChartVector I F z 1)

/-- At a common differentiability point, the planar Fréchet primitive-error
density is its intrinsic expression on the two chart vectors. -/
theorem finiteSymplecticFDerivPrimitiveError_comp_parametrization
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (ρ : M → ℝ) (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (F z))
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    finiteSymplecticFDerivPrimitiveError (ρ ∘ F) (G ∘ F) z =
      finiteComplexRiemannianChartPrimitiveErrorDensity I ρ G F z := by
  have hρ0 : fderiv ℝ (ρ ∘ F) z 1 =
      mfderiv I 𝓘(ℝ, ℝ) ρ (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z (1 : ℂ)) :=
    fderiv_real_comp_parametrization_apply_eq_mfderiv
      I ρ F z 1 hF hρ
  have hρ1 : fderiv ℝ (ρ ∘ F) z Complex.I =
      mfderiv I 𝓘(ℝ, ℝ) ρ (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z Complex.I) :=
    fderiv_real_comp_parametrization_apply_eq_mfderiv
      I ρ F z Complex.I hF hρ
  have hG0 : (fderiv ℝ (G ∘ F) z) 1 =
      finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z (1 : ℂ)) := by
    funext i
    rw [finiteComplexRiemannianDerivative,
      ContinuousLinearMap.pi_apply,
      riemannianComplexMFDeriv_apply_eq_mfderiv]
    exact fderiv_finite_comp_parametrization_apply_eq_mfderiv
      I G F z (1 : ℂ) i hF hG
  have hG1 : (fderiv ℝ (G ∘ F) z) Complex.I =
      finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z Complex.I) := by
    funext i
    rw [finiteComplexRiemannianDerivative,
      ContinuousLinearMap.pi_apply,
      riemannianComplexMFDeriv_apply_eq_mfderiv]
    exact fderiv_finite_comp_parametrization_apply_eq_mfderiv
      I G F z Complex.I i hF hG
  have he0 : orientedComplexTangentOrthonormalBasis z 0 = (1 : ℂ) := by
    rw [orientedComplexTangentOrthonormalBasis_apply]
    simpa using congrFun Complex.coe_orthonormalBasisOneI (0 : Fin 2)
  have he1 :
      orientedComplexTangentOrthonormalBasis z 1 = Complex.I := by
    rw [orientedComplexTangentOrthonormalBasis_apply]
    simpa using congrFun Complex.coe_orthonormalBasisOneI (1 : Fin 2)
  unfold finiteSymplecticFDerivPrimitiveError
    finiteComplexRiemannianChartPrimitiveErrorDensity
    finiteComplexRiemannianPrimitive
    orientedRiemannianChartVector riemannianRealMFDeriv
  rw [fromTangentSpace_real_toContinuousLinearMap,
    ContinuousLinearMap.id_comp]
  rw [he0, he1, hρ0, hρ1, hG0, hG1]
  rfl

/-- The intrinsic chart primitive-error density is the signed chart Jacobian
times the intrinsic oriented primitive-error density. -/
theorem finiteComplexRiemannianChartPrimitiveErrorDensity_eq_jacobian_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : M → ℝ) (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ) :
    finiteComplexRiemannianChartPrimitiveErrorDensity I ρ G F z =
      orientedRiemannianChartJacobian I o F z *
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          I o ρ G (F z) := by
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (F z)⟩
  let e := o.positiveOrthonormalBasis I (F z)
  simpa only [finiteComplexRiemannianChartPrimitiveErrorDensity,
    orientedRiemannianChartJacobian,
    orientedFiniteComplexRiemannianPrimitiveErrorDensity, e] using
    (alternatingContinuousLinearPair_eq_areaForm_mul
      (riemannianRealMFDeriv I ρ (F z))
      (finiteComplexRiemannianPrimitive I G (F z))
      (o.orientation (F z)) e
      (o.positiveOrthonormalBasis_orientation I (F z))
      (orientedRiemannianChartVector I F z 0)
      (orientedRiemannianChartVector I F z 1))

/-- The complete pointwise chart formula for the localized primitive error. -/
theorem finiteSymplecticFDerivPrimitiveError_comp_parametrization_eq_jacobian_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (ρ : M → ℝ) (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (F z))
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    finiteSymplecticFDerivPrimitiveError (ρ ∘ F) (G ∘ F) z =
      orientedRiemannianChartJacobian I o F z *
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          I o ρ G (F z) := by
  rw [finiteSymplecticFDerivPrimitiveError_comp_parametrization
      I ρ G F z hF hρ hG,
    finiteComplexRiemannianChartPrimitiveErrorDensity_eq_jacobian_mul]

#print axioms alternatingContinuousLinearPair_eq_areaForm_mul
#print axioms fderiv_real_comp_parametrization_apply_eq_mfderiv
#print axioms finiteSymplecticFDerivPrimitiveError_comp_parametrization
#print axioms
  finiteComplexRiemannianChartPrimitiveErrorDensity_eq_jacobian_mul
#print axioms
  finiteSymplecticFDerivPrimitiveError_comp_parametrization_eq_jacobian_mul

end

end GromovFilling
