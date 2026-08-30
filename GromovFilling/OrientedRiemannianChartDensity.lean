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
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (F : ℂ → M) (z : ℂ) (i : Fin 2) : TangentSpace I (F z) :=
  riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z
    (orientedComplexTangentOrthonormalBasis z i)

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
  have hcomp := mfderiv_comp_apply z hG hF v
  simpa only [riemannianComplexMFDeriv,
    riemannianMFDerivBetween_apply, ContinuousLinearMap.comp_apply,
    mfderiv_eq_fderiv] using hcomp

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
  have hcoord : ∀ i : ι,
      DifferentiableAt ℝ ((fun x ↦ G x i) ∘ F) z :=
    fun i ↦ ((hG i).comp z hF).differentiableAt
  rw [show G ∘ F =
      (fun w i ↦ ((fun x ↦ G x i) ∘ F) w) from rfl,
    fderiv_pi hcoord]
  ext v i
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    finiteComplexRiemannianDerivative]
  exact fderiv_comp_parametrization_eq_riemannianComplexMFDeriv
    I (fun x ↦ G x i) F z v hF (hG i)

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
  unfold orientedRiemannianChartJacobian riemannianTwoJacobianBetween
  simpa only [orientedRiemannianChartVector,
    riemannianMFDerivBetween_apply] using
    (twoJacobian_eq_abs_areaForm
      (orientedComplexTangentOrthonormalBasis z)
      (o.orientation (F z))
      (riemannianMFDerivBetween 𝓘(ℝ, ℂ) I F z)).symm

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
  unfold finiteSymplecticFDerivDensity
    finiteComplexRiemannianChartPullbackDensity
  rw [fderiv_finiteComplex_comp_parametrization I G F z hF hG]
  simp only [ContinuousLinearMap.comp_apply, h0, h1]

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

end

end GromovFilling
