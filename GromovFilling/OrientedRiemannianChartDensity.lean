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

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace
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
  rw [finiteComplexSymplecticPullback_apply,
    AlternatingMap.smul_apply, smul_eq_mul,
    ← o.areaForm_to_volumeForm] at h
  simpa only [mul_comm] using h

set_option backward.isDefEq.respectTransparency false in
/-- The canonical norm-preserving identification of the complex plane with
its Riemannian tangent space at a point. -/
def orientedComplexTangentLinearIsometry (z : ℂ) :
    ℂ ≃ₗᵢ[ℝ] TangentSpace 𝒘(ℝ, ℂ) z :=
  LinearIsometryEquiv.mk
    (NormedSpace.fromTangentSpace z).symm.toLinearEquiv
    (fun v ↦ by
      simpa only [NormedSpace.fromTangentSpace] using
        (norm_tangentSpace_vectorSpace (x := z)
          (v := (NormedSpace.fromTangentSpace z).symm v)))

/-- The standard complex orthonormal basis transported to the source
tangent space of a complex chart. -/
def orientedComplexTangentOrthonormalBasis (z : ℂ) :
    OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝒘(ℝ, ℂ) z) :=
  Complex.orthonormalBasisOneI.map (orientedComplexTangentLinearIsometry z)

@[simp] theorem orientedComplexTangentOrthonormalBasis_apply
    (z : ℂ) (i : Fin 2) :
    orientedComplexTangentOrthonormalBasis z i =
      Complex.orthonormalBasisOneI i := by
  rfl

/-- The signed Riemannian Jacobian of a complex parametrization relative to
the selected target orientation. -/
def orientedRiemannianChartJacobian
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : ℂ → M) (z : ℂ) : ℝ :=
  (o.orientation (F z)).areaForm
    (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
      (orientedComplexTangentOrthonormalBasis z 0))
    (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
      (orientedComplexTangentOrthonormalBasis z 1))

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
      riemannianTwoJacobianBetween 𝒘(ℝ, ℂ) I F z := by
  letI : Fact (Module.finrank ℝ
      (TangentSpace 𝒘(ℝ, ℂ) z) = 2) :=
    ⟨tangentSpace_finrank_eq_two 𝒘(ℝ, ℂ) z⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I (F z)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I (F z)⟩
  unfold orientedRiemannianChartJacobian riemannianTwoJacobianBetween
  simpa only [riemannianMFDerivBetween_apply] using
    (twoJacobian_eq_abs_areaForm
      (orientedComplexTangentOrthonormalBasis z)
      (o.orientation (F z))
      (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z)).symm

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
      (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
        (orientedComplexTangentOrthonormalBasis z 0)))
    (finiteComplexRiemannianDerivative I G (F z)
      (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
        (orientedComplexTangentOrthonormalBasis z 1)))

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
  let e := o.positiveOrthonormalBasis I (F z)
  simpa only [finiteComplexRiemannianChartPullbackDensity,
    orientedRiemannianChartJacobian,
    orientedFiniteComplexRiemannianSymplecticDensity,
    finiteComplexRiemannianSymplecticDensityInFrame, e] using
    (standardComplexSymplectic_eq_areaForm_mul_density
      (finiteComplexRiemannianDerivative I G (F z))
      (o.orientation (F z)) e
      (o.positiveOrthonormalBasis_orientation I (F z))
      (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
        (orientedComplexTangentOrthonormalBasis z 0))
      (riemannianMFDerivBetween 𝒘(ℝ, ℂ) I F z
        (orientedComplexTangentOrthonormalBasis z 1)))

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
      riemannianTwoJacobianBetween 𝒘(ℝ, ℂ) I F z *
        |orientedFiniteComplexRiemannianSymplecticDensity I o G (F z)| := by
  rw [finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul,
    abs_mul, abs_orientedRiemannianChartJacobian_eq_twoJacobian]

#print axioms finiteComplexSymplecticPullback_eq_density_smul_volumeForm
#print axioms standardComplexSymplectic_eq_areaForm_mul_density
#print axioms abs_orientedRiemannianChartJacobian_eq_twoJacobian
#print axioms ofReal_abs_orientedRiemannianChartJacobian_eq_chartDensity
#print axioms finiteComplexRiemannianChartPullbackDensity_eq_jacobian_mul
#print axioms abs_finiteComplexRiemannianChartPullbackDensity_eq_twoJacobian_mul

end

end GromovFilling
