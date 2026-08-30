import GromovFilling.FiniteSymplecticChartTransition
import GromovFilling.OrientedRiemannianDensity
import GromovFilling.RiemannianChartDensity

/-!
# Oriented symplectic density in Riemannian charts

This module identifies the signed planar density of a finite complex-valued
map in a Riemannian chart.  The chart derivative contributes its signed
Riemannian Jacobian, while the map contributes the intrinsic symplectic
density computed in the positive tangent orientation.  Taking absolute
values recovers the orientation-free chart-area density.

This is a pointwise differential identity.  Chartwise weak Stokes and the
partition-of-unity globalization remain separate obligations.
-/

open Bundle Manifold
open scoped Bundle InnerProductSpace Manifold

namespace GromovFilling

noncomputable section

attribute [local instance] Complex.finrank_real_complex_fact

private theorem fromTangentSpace_complex_toContinuousLinearMap (a : ℂ) :
    (NormedSpace.fromTangentSpace a).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ ℂ := by
  rfl

/-- A top-degree finite symplectic pullback is its value in a positive
orthonormal frame times the oriented volume form. -/
theorem finiteComplexSymplecticPullback_eq_density_smul_volumeForm
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] [Fintype ι] [Finite ι]
    (L : V →L[ℝ] (ι → ℂ)) (o : Orientation ℝ V (Fin 2))
    (e : OrthonormalBasis (Fin 2) ℝ V)
    (he : e.toBasis.orientation = o) :
    finiteComplexSymplecticPullback L =
      finiteComplexSymplecticDensityInFrame L e • o.volumeForm := by
  let β : V [⋀^Fin 2]→ₗ[ℝ] ℝ := finiteComplexSymplecticPullback L
  calc
    finiteComplexSymplecticPullback L =
        β e.toBasis • e.toBasis.det := by
      simpa only [β] using β.eq_smul_basis_det e.toBasis
    _ = finiteComplexSymplecticDensityInFrame L e • e.toBasis.det := by
      congr 1
      unfold finiteComplexSymplecticDensityInFrame
      rw [← finiteComplexSymplecticPullback_apply]
      apply congrArg β
      funext i
      fin_cases i <;> rfl
    _ = finiteComplexSymplecticDensityInFrame L e • o.volumeForm := by
      rw [o.volumeForm_robust e he]

/-- Evaluation of the top-degree identity on two arbitrary tangent vectors. -/
theorem standardComplexSymplectic_eq_areaForm_mul_density
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] [Fintype ι] [Finite ι]
    (L : V →L[ℝ] (ι → ℂ)) (o : Orientation ℝ V (Fin 2))
    (e : OrthonormalBasis (Fin 2) ℝ V)
    (he : e.toBasis.orientation = o) (u v : V) :
    standardComplexSymplectic (L u) (L v) =
      o.areaForm u v * finiteComplexSymplecticDensityInFrame L e := by
  have h := congrArg
    (fun η : V [⋀^Fin 2]→ₗ[ℝ] ℝ ↦ η ![u, v])
    (finiteComplexSymplecticPullback_eq_density_smul_volumeForm L o e he)
  change finiteComplexSymplecticPullback L ![u, v] =
    (finiteComplexSymplecticDensityInFrame L e • o.volumeForm) ![u, v] at h
  rw [finiteComplexSymplecticPullback_apply,
    AlternatingMap.smul_apply, smul_eq_mul,
    ← o.areaForm_to_volumeForm] at h
  simpa only [mul_comm] using h

set_option backward.isDefEq.respectTransparency false in
/-- The canonical norm-preserving identification of the complex plane with
its Riemannian tangent space at a point. -/
def orientedComplexTangentLinearIsometry (z : ℂ) :
    ℂ ≃ₗᵢ[ℝ] TangentSpace 𝓘(ℝ, ℂ) z :=
  LinearIsometryEquiv.mk
    (NormedSpace.fromTangentSpace z).symm.toLinearEquiv
    (fun v ↦ by
      simpa only [NormedSpace.fromTangentSpace] using
        (norm_tangentSpace_vectorSpace (x := z)
          (v := (NormedSpace.fromTangentSpace z).symm v)))

/-- The standard complex orthonormal basis transported to the source
tangent space of a complex chart. -/
def orientedComplexTangentOrthonormalBasis (z : ℂ) :
    OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z) :=
  Complex.orthonormalBasisOneI.map (orientedComplexTangentLinearIsometry z)

@[simp] theorem orientedComplexTangentOrthonormalBasis_apply
    (z : ℂ) (i : Fin 2) :
    orientedComplexTangentOrthonormalBasis z i =
      Complex.orthonormalBasisOneI i := by
  rfl

/-- One column of a complex parametrization derivative, named separately so
the Riemannian source and target norm transports are checked once rather than
re-expanded inside every signed density. -/
def orientedRiemannianChartVector
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (F : ℂ → M) (z : ℂ) (i : Fin 2) : TangentSpace I (F z) :=
  mfderiv 𝓘(ℝ, ℂ) I F z
    (orientedComplexTangentOrthonormalBasis z i)

set_option maxHeartbeats 800000 in
private theorem riemannianComplexMFDeriv_apply_eq_mfderiv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (G : M → ℂ) (x : M) (v : TangentSpace I x) :
    riemannianComplexMFDeriv I G x v =
      mfderiv I 𝓘(ℝ, ℂ) G x v := by
  rw [riemannianComplexMFDeriv,
    fromTangentSpace_complex_toContinuousLinearMap,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

set_option maxHeartbeats 800000 in
/-- The Riemannian differential of a complex-valued manifold map, applied
after a differentiable complex parametrization, is the ordinary derivative
of the coordinate pullback. -/
theorem fderiv_comp_parametrization_eq_riemannianComplexMFDeriv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (G : M → ℂ) (F : ℂ → M) (z v : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : MDifferentiableAt I 𝓘(ℝ, ℂ) G (F z)) :
    fderiv ℝ (G ∘ F) z v =
      riemannianComplexMFDeriv I G (F z)
        (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z v) := by
  rw [riemannianComplexMFDeriv_apply_eq_mfderiv,
    riemannianMFDerivBetween_apply]
  simpa only [ContinuousLinearMap.id_apply, mfderiv_eq_fderiv] using
    (mfderiv_comp_apply z hG hF v)

set_option maxHeartbeats 800000 in
private theorem fderiv_finiteComplex_comp_parametrization_apply
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (G : M → ι → ℂ) (F : ℂ → M) (z v : ℂ) (i : ι)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : ∀ j : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x j) (F z)) :
    (fderiv ℝ (G ∘ F) z v) i =
      (finiteComplexRiemannianDerivative I G (F z)
        (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z v)) i := by
  have hcoord : ∀ j : ι,
      DifferentiableAt ℝ ((fun x ↦ G x j) ∘ F) z :=
    fun j ↦ ((hG j).comp z hF).differentiableAt
  calc
    (fderiv ℝ (G ∘ F) z v) i =
        fderiv ℝ ((fun x ↦ G x i) ∘ F) z v := by
      exact congrArg (fun L : ℂ →L[ℝ] (ι → ℂ) ↦ (L v) i)
        (fderiv_pi hcoord)
    _ = riemannianComplexMFDeriv I (fun x ↦ G x i) (F z)
        (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z v) :=
      fderiv_comp_parametrization_eq_riemannianComplexMFDeriv
        I (fun x ↦ G x i) F z v hF (hG i)
    _ = (finiteComplexRiemannianDerivative I G (F z)
        (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z v)) i := by
      rw [finiteComplexRiemannianDerivative,
        ContinuousLinearMap.pi_apply]

set_option maxHeartbeats 800000 in
/-- Coordinatewise manifold chain rule for a finite complex-valued map. -/
theorem fderiv_finiteComplex_comp_parametrization
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    fderiv ℝ (G ∘ F) z =
      (finiteComplexRiemannianDerivative I G (F z)).comp
        (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z) := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  simpa only [ContinuousLinearMap.comp_apply] using
    (fderiv_finiteComplex_comp_parametrization_apply
      I G F z v i hF hG)

/-- The signed Riemannian Jacobian of a complex parametrization relative to
the selected target orientation. -/
def orientedRiemannianChartJacobian
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : ℂ → M) (z : ℂ) : ℝ := by
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (F z)⟩
  exact (o.orientation (F z)).areaForm
    (orientedRiemannianChartVector I F z 0)
    (orientedRiemannianChartVector I F z 1)

/-- The absolute signed chart Jacobian is the intrinsic metric
two-Jacobian. -/
theorem abs_orientedRiemannianChartJacobian_eq_twoJacobian
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : ℂ → M) (z : ℂ) :
    |orientedRiemannianChartJacobian I o F z| =
      riemannianTwoJacobianBetween 𝓘(ℝ, ℂ) I F z := by
  letI : Fact (Module.finrank ℝ
      (TangentSpace 𝓘(ℝ, ℂ) z) = 2) :=
    ⟨tangentSpace_finrank_eq_two 𝓘(ℝ, ℂ) z⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (F z)⟩
  rw [riemannianTwoJacobianBetween_eq_abs_areaForm
    𝓘(ℝ, ℂ) I F z (orientedComplexTangentOrthonormalBasis z)
      (o.orientation (F z))]
  rfl

/-- The `ENNReal` area density forgets exactly the sign of the oriented
chart Jacobian. -/
theorem ofReal_abs_orientedRiemannianChartJacobian_eq_chartDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : ℂ → M) (z : ℂ) :
    ENNReal.ofReal |orientedRiemannianChartJacobian I o F z| =
      riemannianChartDensity I F z := by
  rw [abs_orientedRiemannianChartJacobian_eq_twoJacobian]
  rfl

/-- The signed planar pullback density of a finite complex-valued manifold
map along a complex parametrization. -/
def finiteComplexRiemannianChartPullbackDensity
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ) : ℝ :=
  standardComplexSymplectic
    (finiteComplexRiemannianDerivative I G (F z)
      (orientedRiemannianChartVector I F z 0))
    (finiteComplexRiemannianDerivative I G (F z)
      (orientedRiemannianChartVector I F z 1))

set_option maxHeartbeats 800000 in
/-- At a differentiability point, the ordinary planar `fderiv` density of
the coordinate pullback is exactly the Riemannian chart pullback density. -/
theorem finiteSymplecticFDerivDensity_comp_parametrization
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    finiteSymplecticFDerivDensity (G ∘ F) z =
      finiteComplexRiemannianChartPullbackDensity I G F z := by
  have h0 : orientedComplexTangentOrthonormalBasis z 0 = (1 : ℂ) := by
    rw [orientedComplexTangentOrthonormalBasis_apply]
    simpa using congrFun Complex.coe_orthonormalBasisOneI (0 : Fin 2)
  have h1 : orientedComplexTangentOrthonormalBasis z 1 = Complex.I := by
    rw [orientedComplexTangentOrthonormalBasis_apply]
    simpa using congrFun Complex.coe_orthonormalBasisOneI (1 : Fin 2)
  have hv0 : (fderiv ℝ (G ∘ F) z) 1 =
      finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z 1) := by
    funext i
    simpa only [riemannianMFDerivBetween_apply] using
      (fderiv_finiteComplex_comp_parametrization_apply
        I G F z 1 i hF hG)
  have hv1 : (fderiv ℝ (G ∘ F) z) Complex.I =
      finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z Complex.I) := by
    funext i
    simpa only [riemannianMFDerivBetween_apply] using
      (fderiv_finiteComplex_comp_parametrization_apply
        I G F z Complex.I i hF hG)
  change standardComplexSymplectic ((fderiv ℝ (G ∘ F) z) 1)
      ((fderiv ℝ (G ∘ F) z) Complex.I) =
    standardComplexSymplectic
      (finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z
          (orientedComplexTangentOrthonormalBasis z 0)))
      (finiteComplexRiemannianDerivative I G (F z)
        (mfderiv 𝓘(ℝ, ℂ) I F z
          (orientedComplexTangentOrthonormalBasis z 1)))
  rw [h0, h1]
  exact congrArg₂ standardComplexSymplectic hv0 hv1

/-- In an oriented Riemannian chart, the signed planar pullback density is
the signed chart Jacobian times the intrinsic oriented density. -/
theorem finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ) :
    finiteComplexRiemannianChartPullbackDensity I G F z =
      orientedRiemannianChartJacobian I o F z *
        orientedFiniteComplexRiemannianSymplecticDensity I o G (F z) := by
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (F z)⟩
  let e := o.positiveOrthonormalBasis I (F z)
  simpa only [finiteComplexRiemannianChartPullbackDensity,
    orientedRiemannianChartJacobian,
    orientedFiniteComplexRiemannianSymplecticDensity,
    finiteComplexRiemannianSymplecticDensityInFrame, e] using
    (standardComplexSymplectic_eq_areaForm_mul_density
      (finiteComplexRiemannianDerivative I G (F z))
      (o.orientation (F z)) e
      (o.positiveOrthonormalBasis_orientation I (F z))
      (orientedRiemannianChartVector I F z 0)
      (orientedRiemannianChartVector I F z 1))

/-- The planar Fréchet-derivative density of a differentiable coordinate
pullback factors into signed chart Jacobian and intrinsic oriented density. -/
theorem finiteSymplecticFDerivDensity_comp_parametrization_eq_jacobian_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    finiteSymplecticFDerivDensity (G ∘ F) z =
      orientedRiemannianChartJacobian I o F z *
        orientedFiniteComplexRiemannianSymplecticDensity I o G (F z) := by
  rw [finiteSymplecticFDerivDensity_comp_parametrization I G F z hF hG,
    finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul]

/-- Absolute planar pullback density factors into the metric chart
Jacobian and the absolute intrinsic symplectic density. -/
theorem abs_finiteComplexRiemannianChartPullbackDensity_eq_twoJacobian_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ) :
    |finiteComplexRiemannianChartPullbackDensity I G F z| =
      riemannianTwoJacobianBetween 𝓘(ℝ, ℂ) I F z *
        |orientedFiniteComplexRiemannianSymplecticDensity I o G (F z)| := by
  rw [finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul,
    abs_mul, abs_orientedRiemannianChartJacobian_eq_twoJacobian]

/-- In multiplicative `ℝ≥0∞` form, the absolute planar pullback density is
the chart-area density times the canonical absolute intrinsic symplectic
density.  This is the weighted-measurability identity used by the global
surface-area integral. -/
theorem ofReal_abs_finiteSymplecticFDerivDensity_comp_parametrization_eq_chartDensity_mul
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (G : M → ι → ℂ) (F : ℂ → M) (z : ℂ)
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F z)
    (hG : ∀ i : ι,
      MDifferentiableAt I 𝓘(ℝ, ℂ) (fun x ↦ G x i) (F z)) :
    ENNReal.ofReal |finiteSymplecticFDerivDensity (G ∘ F) z| =
      riemannianChartDensity I F z *
        ENNReal.ofReal
          |orientedFiniteComplexRiemannianSymplecticDensity I o G (F z)| := by
  rw [finiteSymplecticFDerivDensity_comp_parametrization
      I G F z hF hG,
    abs_finiteComplexRiemannianChartPullbackDensity_eq_twoJacobian_mul,
    ENNReal.ofReal_mul
      (riemannianTwoJacobianBetween_nonneg 𝓘(ℝ, ℂ) I F z)]
  rfl

#print axioms finiteComplexSymplecticPullback_eq_density_smul_volumeForm
#print axioms standardComplexSymplectic_eq_areaForm_mul_density
#print axioms orientedRiemannianChartVector
#print axioms abs_orientedRiemannianChartJacobian_eq_twoJacobian
#print axioms ofReal_abs_orientedRiemannianChartJacobian_eq_chartDensity
#print axioms finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul
#print axioms fderiv_comp_parametrization_eq_riemannianComplexMFDeriv
#print axioms fderiv_finiteComplex_comp_parametrization
#print axioms finiteSymplecticFDerivDensity_comp_parametrization
#print axioms finiteSymplecticFDerivDensity_comp_parametrization_eq_jacobian_mul
#print axioms abs_finiteComplexRiemannianChartPullbackDensity_eq_twoJacobian_mul
#print axioms
  ofReal_abs_finiteSymplecticFDerivDensity_comp_parametrization_eq_chartDensity_mul

end

end GromovFilling
