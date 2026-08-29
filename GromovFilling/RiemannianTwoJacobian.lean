import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The intrinsic two-dimensional metric Jacobian

This file supplies the pointwise definition layer needed to state the
Riemannian part of Lemma 5.4.  The absolute determinant of a linear map
between two-dimensional real inner-product spaces is computed in
orthonormal bases and proved independent of those bases.  Consequently the
definition does not require either vector space to be oriented.
-/

open scoped Bundle Manifold
open Bundle

namespace GromovFilling

noncomputable section

/-- The absolute determinant of a linear map, computed in orthonormal bases.
The common finite index is exposed so that basis independence can be proved
once, before specializing to dimension two. -/
def metricJacobianWithBases
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ E)
    (f : OrthonormalBasis (Fin n) ℝ F) (L : E →L[ℝ] F) : ℝ :=
  |(LinearMap.toMatrix e.toBasis f.toBasis L.toLinearMap).det|

/-- Absolute determinant is unchanged when the source and target
orthonormal bases are changed. -/
theorem metricJacobianWithBases_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (e e' : OrthonormalBasis (Fin n) ℝ E)
    (f f' : OrthonormalBasis (Fin n) ℝ F) (L : E →L[ℝ] F) :
    metricJacobianWithBases e f L = metricJacobianWithBases e' f' L := by
  classical
  have hmatrix :
      f.toBasis.toMatrix f'.toBasis *
          LinearMap.toMatrix e'.toBasis f'.toBasis L.toLinearMap *
          e'.toBasis.toMatrix e.toBasis =
        LinearMap.toMatrix e.toBasis f.toBasis L.toLinearMap :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      e.toBasis e'.toBasis f.toBasis f'.toBasis L.toLinearMap
  have hdet := congrArg Matrix.det hmatrix
  simp only [Matrix.det_mul] at hdet
  unfold metricJacobianWithBases
  rw [← hdet, abs_mul, abs_mul]
  have hf := f.det_to_matrix_orthonormalBasis f'
  have he := e'.det_to_matrix_orthonormalBasis e
  rw [Real.norm_eq_abs, Module.Basis.det_apply] at hf he
  change |(f.toBasis.toMatrix ⇑f'.toBasis).det| = 1 at hf
  change |(e'.toBasis.toMatrix ⇑e.toBasis).det| = 1 at he
  rw [hf, he, one_mul, mul_one]

/-- A fixed orthonormal basis of a real two-dimensional inner-product
space.  Its arbitrary choice is invisible in `twoJacobian` by
`metricJacobianWithBases_eq`. -/
def canonicalOrthonormalBasisTwo
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [hE : Fact (Module.finrank ℝ E = 2)] :
    OrthonormalBasis (Fin 2) ℝ E := by
  letI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_fact_finrank_eq_two
  exact (stdOrthonormalBasis ℝ E).reindex (finCongr hE.out)

/-- The intrinsic two-dimensional metric Jacobian of a continuous real
linear map.  It is the absolute determinant in any pair of orthonormal
bases, hence is defined without choosing orientations. -/
def twoJacobian
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)] (L : E →L[ℝ] F) : ℝ :=
  metricJacobianWithBases
    (canonicalOrthonormalBasisTwo E)
    (canonicalOrthonormalBasisTwo F) L

/-- The intrinsic Jacobian can be evaluated in any orthonormal bases. -/
theorem twoJacobian_eq_metricJacobianWithBases
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (e : OrthonormalBasis (Fin 2) ℝ E)
    (f : OrthonormalBasis (Fin 2) ℝ F) (L : E →L[ℝ] F) :
    twoJacobian L = metricJacobianWithBases e f L :=
  metricJacobianWithBases_eq
    (canonicalOrthonormalBasisTwo E) e
    (canonicalOrthonormalBasisTwo F) f L

theorem twoJacobian_nonneg
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)] (L : E →L[ℝ] F) :
    0 ≤ twoJacobian L := by
  unfold twoJacobian metricJacobianWithBases
  positivity

/-- Precomposing with a linear isometric equivalence does not change the
intrinsic metric Jacobian. -/
theorem twoJacobian_comp_linearIsometryEquiv
    {E E' F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ E' = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (L : E →L[ℝ] F) (φ : E' ≃ₗᵢ[ℝ] E) :
    twoJacobian (E := E') (F := F)
        (L.comp φ.toLinearIsometry.toContinuousLinearMap) =
      twoJacobian (E := E) (F := F) L := by
  let e' := canonicalOrthonormalBasisTwo E'
  let e := e'.map φ
  let f := canonicalOrthonormalBasisTwo F
  rw [twoJacobian_eq_metricJacobianWithBases e' f,
    twoJacobian_eq_metricJacobianWithBases e f]
  unfold metricJacobianWithBases
  change |(LinearMap.toMatrix e'.toBasis f.toBasis
      (L.toLinearMap.comp φ.toLinearEquiv.toLinearMap)).det| = _
  rw [LinearMap.toMatrix_comp e'.toBasis e.toBasis f.toBasis]
  have hφ : LinearMap.toMatrix e'.toBasis e.toBasis
      φ.toLinearEquiv.toLinearMap = 1 := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, e, e']
  rw [hφ, Matrix.mul_one]

/-- On an endomorphism, the intrinsic metric Jacobian is exactly the
absolute value of mathlib's basis-independent determinant. -/
theorem twoJacobian_eq_abs_det
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (L : E →L[ℝ] E) :
    twoJacobian L = |L.det| := by
  unfold twoJacobian metricJacobianWithBases
  rw [LinearMap.det_toMatrix]

/-- In complex coordinates the intrinsic metric Jacobian agrees with the
absolute real determinant already used by the planar area formula. -/
theorem twoJacobian_complex_eq_abs_det (L : ℂ →L[ℝ] ℂ) :
    letI : Fact (Module.finrank ℝ ℂ = 2) :=
      Complex.finrank_real_complex_fact
    twoJacobian L = |L.det| := by
  letI : Fact (Module.finrank ℝ ℂ = 2) :=
    Complex.finrank_real_complex_fact
  exact twoJacobian_eq_abs_det L

private theorem tangentSpace_finrank_eq_two
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [hE : Fact (Module.finrank ℝ E = 2)] (x : M) :
    Module.finrank ℝ (TangentSpace I x) = 2 := by
  simpa only [TangentSpace] using hE.out

/-- The pointwise intrinsic `J₂` of a map from a two-dimensional
Riemannian manifold to the Euclidean complex plane.  The differential is
the manifold differential and both determinant norms come from the
Riemannian metrics on the tangent spaces. -/
def riemannianTwoJacobian
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [hR : RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (G : M → ℂ) (x : M) : ℝ := by
  letI sourceNormed : NormedAddCommGroup (TangentSpace I x) :=
    (hR.g.toCore x).toNormedAddCommGroupOfTopology
      (hR.g.continuousAt x) (hR.g.isVonNBounded x)
  letI sourceInner : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology (hR.g.toCore x)
      (hR.g.continuousAt x) (hR.g.isVonNBounded x)
  let hC : RiemannianBundle
      (fun z : ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) z) := inferInstance
  letI targetNormed : NormedAddCommGroup
      (TangentSpace (𝓘(ℝ, ℂ)) (G x)) :=
    (hC.g.toCore (G x)).toNormedAddCommGroupOfTopology
      (hC.g.continuousAt (G x)) (hC.g.isVonNBounded (G x))
  letI targetInner : InnerProductSpace ℝ
      (TangentSpace (𝓘(ℝ, ℂ)) (G x)) :=
    InnerProductSpace.ofCoreOfTopology (hC.g.toCore (G x))
      (hC.g.continuousAt (G x)) (hC.g.isVonNBounded (G x))
  letI : Fact (Module.finrank ℝ (TangentSpace I x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I x⟩
  letI : Fact (Module.finrank ℝ ℂ = 2) :=
    Complex.finrank_real_complex_fact
  exact twoJacobian (E := TangentSpace I x) (F := ℂ)
    ((NormedSpace.fromTangentSpace (G x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, ℂ) G x))

theorem riemannianTwoJacobian_nonneg
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (G : M → ℂ) (x : M) :
    0 ≤ riemannianTwoJacobian I G x := by
  simp only [riemannianTwoJacobian, twoJacobian,
    metricJacobianWithBases]
  positivity

local instance complexFinrankTwoFact :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- For a map between Euclidean complex planes, the intrinsic Riemannian
`J₂` is the absolute determinant density used by the existing planar area
formula. -/
theorem riemannianTwoJacobian_complex_eq_abs_det_fderiv
    (G : ℂ → ℂ) (x : ℂ) :
    riemannianTwoJacobian 𝓘(ℝ, ℂ) G x =
      |(fderiv ℝ G x).det| := by
  simp only [riemannianTwoJacobian]
  letI : Fact
      (Module.finrank ℝ (TangentSpace (𝓘(ℝ, ℂ)) x) = 2) :=
    ⟨by simpa only [TangentSpace] using Complex.finrank_real_complex⟩
  let ψ : TangentSpace (𝓘(ℝ, ℂ)) x ≃ₗᵢ[ℝ] ℂ := {
    toLinearEquiv := (NormedSpace.fromTangentSpace x).toLinearEquiv
    norm_map' v := by exact norm_tangentSpace_vectorSpace.symm
  }
  have h := twoJacobian_comp_linearIsometryEquiv
    ((NormedSpace.fromTangentSpace (G x)).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G x)) ψ.symm
  have hmap :
      (((NormedSpace.fromTangentSpace (G x)).toContinuousLinearMap.comp
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G x)).comp
          ψ.symm.toLinearIsometry.toContinuousLinearMap) =
        fderiv ℝ G x := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  rw [← h, hmap, twoJacobian_eq_abs_det]

end

end GromovFilling
