import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.TwoDim
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

/-- In any orthonormal source basis, the intrinsic two-Jacobian is the
absolute target area of the two image vectors.  The target orientation is
arbitrary because of the absolute value. -/
theorem twoJacobian_eq_abs_areaForm
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (e : OrthonormalBasis (Fin 2) ℝ E)
    (o : Orientation ℝ F (Fin 2)) (L : E →L[ℝ] F) :
    twoJacobian L =
      |o.areaForm (L (e 0)) (L (e 1))| := by
  let f := canonicalOrthonormalBasisTwo F
  calc
    twoJacobian L =
        |(LinearMap.toMatrix e.toBasis f.toBasis L.toLinearMap).det| := by
      rw [twoJacobian_eq_metricJacobianWithBases e f]
      rfl
    _ = |f.toBasis.det (fun i ↦ L (e i))| := by
      apply congrArg abs
      rw [Basis.det_apply]
      apply congrArg Matrix.det
      ext i j
      rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
      rfl
    _ = |o.volumeForm (fun i ↦ L (e i))| :=
      (o.volumeForm_robust' f (fun i ↦ L (e i))).symm
    _ = |o.areaForm (L (e 0)) (L (e 1))| := by
      rw [o.areaForm_to_volumeForm]
      apply congrArg abs
      apply congrArg o.volumeForm
      funext i
      fin_cases i <;> rfl

/-- Orientation-free Gram-determinant formula for the square of the
intrinsic two-Jacobian.  This presentation contains no chosen target basis
and is the key to measurability in a varying Riemannian tangent bundle. -/
theorem twoJacobian_sq_eq_gram
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (e : OrthonormalBasis (Fin 2) ℝ E)
    (o : Orientation ℝ F (Fin 2)) (L : E →L[ℝ] F) :
    twoJacobian L ^ 2 =
      ‖L (e 0)‖ ^ 2 * ‖L (e 1)‖ ^ 2 -
        ⟦L (e 0), L (e 1)⟧_ℝ ^ 2 := by
  rw [twoJacobian_eq_abs_areaForm e o, sq_abs]
  nlinarith [o.inner_sq_add_areaForm_sq (L (e 0)) (L (e 1))]

/-- Square-root form of the orientation-free Gram formula. -/
theorem twoJacobian_eq_sqrt_gram
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (e : OrthonormalBasis (Fin 2) ℝ E)
    (o : Orientation ℝ F (Fin 2)) (L : E →L[ℝ] F) :
    twoJacobian L =
      √(‖L (e 0)‖ ^ 2 * ‖L (e 1)‖ ^ 2 -
        ⟦L (e 0), L (e 1)⟧_ℝ ^ 2) := by
  calc
    twoJacobian L = |o.areaForm (L (e 0)) (L (e 1))| :=
      twoJacobian_eq_abs_areaForm e o L
    _ = √(o.areaForm (L (e 0)) (L (e 1)) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = √(‖L (e 0)‖ ^ 2 * ‖L (e 1)‖ ^ 2 -
        ⟦L (e 0), L (e 1)⟧_ℝ ^ 2) := by
      congr 1
      nlinarith [o.inner_sq_add_areaForm_sq (L (e 0)) (L (e 1))]

/-- The intrinsic two-dimensional metric Jacobian is multiplicative under
composition. -/
theorem twoJacobian_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    [Fact (Module.finrank ℝ G = 2)]
    (L : F →L[ℝ] G) (K : E →L[ℝ] F) :
    twoJacobian (L.comp K) = twoJacobian L * twoJacobian K := by
  classical
  unfold twoJacobian metricJacobianWithBases
  change |(LinearMap.toMatrix
      (canonicalOrthonormalBasisTwo E).toBasis
      (canonicalOrthonormalBasisTwo G).toBasis
      (L.toLinearMap.comp K.toLinearMap)).det| = _
  rw [LinearMap.toMatrix_comp
      (canonicalOrthonormalBasisTwo E).toBasis
      (canonicalOrthonormalBasisTwo F).toBasis
      (canonicalOrthonormalBasisTwo G).toBasis,
    Matrix.det_mul, abs_mul]

/-- The identity has intrinsic two-dimensional metric Jacobian one. -/
@[simp]
theorem twoJacobian_id
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] :
    twoJacobian (ContinuousLinearMap.id ℝ E) = 1 := by
  unfold twoJacobian metricJacobianWithBases
  change |(LinearMap.toMatrix
      (canonicalOrthonormalBasisTwo E).toBasis
      (canonicalOrthonormalBasisTwo E).toBasis LinearMap.id).det| = 1
  rw [LinearMap.toMatrix_id, Matrix.det_one, abs_one]

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

/-- A linear isometric equivalence has intrinsic metric Jacobian one. -/
@[simp]
theorem twoJacobian_linearIsometryEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    (φ : E ≃ₗᵢ[ℝ] F) :
    twoJacobian φ.toLinearIsometry.toContinuousLinearMap = 1 := by
  have h := twoJacobian_comp_linearIsometryEquiv
    (ContinuousLinearMap.id ℝ F) φ
  simpa only [ContinuousLinearMap.id_comp, twoJacobian_id] using h

/-- Postcomposing with a linear isometric equivalence does not change the
intrinsic metric Jacobian. -/
theorem twoJacobian_linearIsometryEquiv_comp
    {E F F' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)]
    [Fact (Module.finrank ℝ F' = 2)]
    (φ : F ≃ₗᵢ[ℝ] F') (L : E →L[ℝ] F) :
    twoJacobian
        (φ.toLinearIsometry.toContinuousLinearMap.comp L) =
      twoJacobian L := by
  rw [twoJacobian_comp, twoJacobian_linearIsometryEquiv, one_mul]

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

/-- The pointwise intrinsic `J₂` of a map between two two-dimensional
Riemannian manifolds.  Both norms are the Riemannian norms on the respective
tangent spaces. -/
def riemannianTwoJacobianBetween
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [hR₁ : RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    [Fact (Module.finrank ℝ E₁ = 2)]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [hR₂ : RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    [Fact (Module.finrank ℝ E₂ = 2)]
    (G : M₁ → M₂) (x : M₁) : ℝ := by
  letI : Fact (Module.finrank ℝ (TangentSpace I₁ x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₁ x⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I₂ (G x)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₂ (G x)⟩
  exact twoJacobian (mfderiv I₁ I₂ G x)

theorem riemannianTwoJacobianBetween_nonneg
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    [Fact (Module.finrank ℝ E₁ = 2)]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    [Fact (Module.finrank ℝ E₂ = 2)]
    (G : M₁ → M₂) (x : M₁) :
    0 ≤ riemannianTwoJacobianBetween I₁ I₂ G x := by
  simp only [riemannianTwoJacobianBetween, twoJacobian,
    metricJacobianWithBases]
  positivity

/-- The identity map on a two-dimensional Riemannian manifold has intrinsic
two-Jacobian one. -/
@[simp]
theorem riemannianTwoJacobianBetween_id
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] (x : M) :
    riemannianTwoJacobianBetween I I (id : M → M) x = 1 := by
  simp only [riemannianTwoJacobianBetween]
  letI : Fact (Module.finrank ℝ (TangentSpace I x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I x⟩
  rw [mfderiv_id]
  exact twoJacobian_id

/-- The intrinsic Riemannian two-Jacobian obeys the pointwise chain rule at
points where both manifold derivatives exist. -/
theorem riemannianTwoJacobianBetween_comp
    {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    [Fact (Module.finrank ℝ E₁ = 2)]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    [Fact (Module.finrank ℝ E₂ = 2)]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [TopologicalSpace H₃] (I₃ : ModelWithCorners ℝ E₃ H₃)
    [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
    [RiemannianBundle (fun x : M₃ ↦ TangentSpace I₃ x)]
    [Fact (Module.finrank ℝ E₃ = 2)]
    (F : M₁ → M₂) (G : M₂ → M₃) (x : M₁)
    (hF : MDifferentiableAt I₁ I₂ F x)
    (hG : MDifferentiableAt I₂ I₃ G (F x)) :
    riemannianTwoJacobianBetween I₁ I₃ (G ∘ F) x =
      riemannianTwoJacobianBetween I₂ I₃ G (F x) *
        riemannianTwoJacobianBetween I₁ I₂ F x := by
  letI : Fact (Module.finrank ℝ (TangentSpace I₁ x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₁ x⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I₂ (F x)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₂ (F x)⟩
  letI : Fact (Module.finrank ℝ (TangentSpace I₃ (G (F x))) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₃ (G (F x))⟩
  letI : Fact
      (Module.finrank ℝ (TangentSpace I₃ ((G ∘ F) x)) = 2) :=
    ⟨tangentSpace_finrank_eq_two I₃ ((G ∘ F) x)⟩
  simp only [riemannianTwoJacobianBetween]
  rw [mfderiv_comp x hG hF]
  exact twoJacobian_comp _ _

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

local instance complexFinrankTwoFact :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

/-- The specialized complex-valued Riemannian Jacobian is exactly the
general tangent-to-tangent Jacobian.  The canonical identification of the
Euclidean target tangent space with `ℂ` is a linear isometry. -/
theorem riemannianTwoJacobian_eq_between_complex
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (G : M → ℂ) (x : M) :
    riemannianTwoJacobian I G x =
      riemannianTwoJacobianBetween I 𝓘(ℝ, ℂ) G x := by
  simp only [riemannianTwoJacobian,
    riemannianTwoJacobianBetween]
  letI : Fact (Module.finrank ℝ (TangentSpace I x) = 2) :=
    ⟨tangentSpace_finrank_eq_two I x⟩
  letI : Fact
      (Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) (G x)) = 2) :=
    ⟨by simpa only [TangentSpace] using Complex.finrank_real_complex⟩
  letI : Fact (Module.finrank ℝ ℂ = 2) :=
    Complex.finrank_real_complex_fact
  let φ : TangentSpace 𝓘(ℝ, ℂ) (G x) ≃ₗᵢ[ℝ] ℂ := {
    toLinearEquiv := (NormedSpace.fromTangentSpace (G x)).toLinearEquiv
    norm_map' v := by exact norm_tangentSpace_vectorSpace.symm
  }
  exact twoJacobian_linearIsometryEquiv_comp φ
    (mfderiv I 𝓘(ℝ, ℂ) G x)

/-- Chain rule for the complex-valued specialization.  This is the form
needed when a surface map is pulled back along a Riemannian coordinate map. -/
theorem riemannianTwoJacobian_comp
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    [Fact (Module.finrank ℝ E₁ = 2)]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    [Fact (Module.finrank ℝ E₂ = 2)]
    (F : M₁ → M₂) (G : M₂ → ℂ) (x : M₁)
    (hF : MDifferentiableAt I₁ I₂ F x)
    (hG : MDifferentiableAt I₂ 𝓘(ℝ, ℂ) G (F x)) :
    riemannianTwoJacobian I₁ (G ∘ F) x =
      riemannianTwoJacobian I₂ G (F x) *
        riemannianTwoJacobianBetween I₁ I₂ F x := by
  simp only [riemannianTwoJacobian_eq_between_complex]
  exact riemannianTwoJacobianBetween_comp
    I₁ I₂ 𝓘(ℝ, ℂ) F G x hF hG

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

/-- On the Euclidean complex plane, the fully intrinsic tangent-to-tangent
Jacobian is the ordinary absolute real determinant density. -/
theorem riemannianTwoJacobianBetween_complex_eq_abs_det_fderiv
    (G : ℂ → ℂ) (x : ℂ) :
    riemannianTwoJacobianBetween 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) G x =
      |(fderiv ℝ G x).det| := by
  rw [← riemannianTwoJacobian_eq_between_complex]
  exact riemannianTwoJacobian_complex_eq_abs_det_fderiv G x

end

end GromovFilling
