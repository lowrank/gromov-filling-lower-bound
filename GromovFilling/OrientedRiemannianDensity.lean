import GromovFilling.FiniteResonantRiemannianProfileBounds

/-!
# Intrinsic oriented finite symplectic densities

This module removes the auxiliary choice of an oriented orthonormal tangent
frame from the finite resonant symplectic density.  It first bundles the
pullback of the standard finite complex symplectic form as a top-degree
alternating form.  Top-degree uniqueness then proves that evaluating in two
positive orthonormal frames gives the same scalar.

The orientation data here is deliberately only fiberwise.  Compatibility of
these tangent-plane orientations with an oriented boundary atlas is a
separate globalization obligation.
-/

open Bundle Manifold
open scoped BigOperators Bundle InnerProductSpace Manifold

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace
attribute [local instance] Complex.finrank_real_complex_fact

/-- The pullback of the standard symplectic form on a finite complex
coordinate space, bundled as an alternating real `2`-form. -/
def finiteComplexSymplecticPullback
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Finite ι] (L : V →L[ℝ] (ι → ℂ)) :
    V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  ∑ i : ι, Complex.orientation.volumeForm.compLinearMap
    (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).comp L).toLinearMap)

/-- Evaluating the bundled pullback on two vectors recovers the standard
finite complex symplectic pairing. -/
@[simp] theorem finiteComplexSymplecticPullback_apply
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Finite ι] (L : V →L[ℝ] (ι → ℂ)) (u v : V) :
    finiteComplexSymplecticPullback L ![u, v] =
      standardComplexSymplectic (L u) (L v) := by
  unfold finiteComplexSymplecticPullback standardComplexSymplectic
  let ev : (V [⋀^Fin 2]→ₗ[ℝ] ℝ) →+ ℝ :=
    { toFun := fun A ↦ A ![u, v]
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ i : ι, Complex.orientation.volumeForm.compLinearMap
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).comp L).toLinearMap)) =
    ∑ i : ι, (star (L u i) * L v i).im
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show ev (Complex.orientation.volumeForm.compLinearMap
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).comp L).toLinearMap)) =
      (Complex.orientation.volumeForm.compLinearMap
        (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).comp L).toLinearMap))
          ![u, v] by rfl]
  rw [AlternatingMap.compLinearMap_apply]
  rw [show (fun j : Fin 2 ↦
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).comp L).toLinearMap)
        (![u, v] j)) = ![L u i, L v i] by
    funext j
    fin_cases j <;> rfl]
  rw [← Complex.orientation.areaForm_to_volumeForm, Complex.areaForm]
  rfl

/-- The finite symplectic density of a linear map, evaluated in an
orthonormal source frame. -/
def finiteComplexSymplecticDensityInFrame
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] [Finite ι]
    (L : V →L[ℝ] (ι → ℂ)) (e : OrthonormalBasis (Fin 2) ℝ V) : ℝ :=
  standardComplexSymplectic (L (e 0)) (L (e 1))

/-- The finite symplectic density is unchanged when the orthonormal source
frame is replaced by another frame with the same orientation. -/
theorem finiteComplexSymplecticDensityInFrame_eq_of_same_orientation
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] [Finite ι]
    (L : V →L[ℝ] (ι → ℂ))
    (e f : OrthonormalBasis (Fin 2) ℝ V)
    (hef : e.toBasis.orientation = f.toBasis.orientation) :
    finiteComplexSymplecticDensityInFrame L e =
      finiteComplexSymplecticDensityInFrame L f := by
  let β : V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    finiteComplexSymplecticPullback (V := V) (ι := ι) L
  have hβ := β.eq_smul_basis_det e.toBasis
  have hdet : e.toBasis.det f = 1 :=
    e.det_to_matrix_orthonormalBasis_of_same_orientation f hef
  have happ := congrArg (fun A : V [⋀^Fin 2]→ₗ[ℝ] ℝ ↦ A f) hβ
  simp only [AlternatingMap.smul_apply, smul_eq_mul, hdet, mul_one] at happ
  unfold finiteComplexSymplecticDensityInFrame
  rw [← finiteComplexSymplecticPullback_apply,
    ← finiteComplexSymplecticPullback_apply]
  simp only [β] at happ
  convert happ.symm using 1 <;>
    congr 1 <;>
    funext i <;>
    fin_cases i <;>
    rfl

/-- Reversing the orientation of an orthonormal source frame reverses the
finite symplectic density. -/
theorem finiteComplexSymplecticDensityInFrame_eq_neg_of_opposite_orientation
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] [Finite ι]
    (L : V →L[ℝ] (ι → ℂ))
    (e f : OrthonormalBasis (Fin 2) ℝ V)
    (hef : e.toBasis.orientation ≠ f.toBasis.orientation) :
    finiteComplexSymplecticDensityInFrame L e =
      -finiteComplexSymplecticDensityInFrame L f := by
  let β : V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    finiteComplexSymplecticPullback (V := V) (ι := ι) L
  have hβ := β.eq_smul_basis_det e.toBasis
  have hdet : e.toBasis.det f = -1 :=
    e.det_to_matrix_orthonormalBasis_of_opposite_orientation f hef
  have happ := congrArg (fun A : V [⋀^Fin 2]→ₗ[ℝ] ℝ ↦ A f) hβ
  simp only [AlternatingMap.smul_apply, smul_eq_mul, hdet, mul_neg,
    mul_one] at happ
  unfold finiteComplexSymplecticDensityInFrame
  rw [← finiteComplexSymplecticPullback_apply,
    ← finiteComplexSymplecticPullback_apply]
  simp only [β] at happ
  have hfapp :
      finiteComplexSymplecticPullback L (f : Fin 2 → V) =
        finiteComplexSymplecticPullback L ![f 0, f 1] := by
    apply congrArg (finiteComplexSymplecticPullback L)
    funext i
    fin_cases i <;> rfl
  have heapp :
      finiteComplexSymplecticPullback L (e.toBasis : Fin 2 → V) =
        finiteComplexSymplecticPullback L ![e 0, e 1] := by
    apply congrArg (finiteComplexSymplecticPullback L)
    funext i
    fin_cases i <;> rfl
  have happ' :
      finiteComplexSymplecticPullback L ![f 0, f 1] =
        -finiteComplexSymplecticPullback L ![e 0, e 1] := by
    rw [← hfapp, ← heapp]
    exact happ
  linarith

/-- A fiberwise choice of positive orientation for the Riemannian tangent
planes.  Continuity and chart compatibility are intentionally not asserted
at this point. -/
structure RiemannianTangentPlaneOrientation
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] where
  orientation : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin 2)

/-- The canonical positive orthonormal tangent frame selected from a
fiberwise orientation.  Its choice is invisible in the intrinsic density. -/
def RiemannianTangentPlaneOrientation.positiveOrthonormalBasis
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M) (x : M) :
    OrthonormalBasis (Fin 2) ℝ (TangentSpace I x) :=
  (o.orientation x).finOrthonormalBasis (by norm_num)
    (tangentSpace_finrank_eq_two I x)

@[simp] theorem RiemannianTangentPlaneOrientation.positiveOrthonormalBasis_orientation
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M) (x : M) :
    (o.positiveOrthonormalBasis I x).toBasis.orientation = o.orientation x := by
  exact Orientation.finOrthonormalBasis_orientation (by norm_num)
    (tangentSpace_finrank_eq_two I x) (o.orientation x)

/-- The coordinatewise Riemannian differential of a finite complex-valued
manifold map. -/
def finiteComplexRiemannianDerivative
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (F : M → ι → ℂ) (x : M) : TangentSpace I x →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i : ι ↦
    riemannianComplexMFDeriv I (fun y ↦ F y i) x

/-- The signed finite symplectic density of a manifold map in a chosen
orthonormal tangent frame. -/
def finiteComplexRiemannianSymplecticDensityInFrame
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fintype ι] [Finite ι]
    (F : M → ι → ℂ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x)) : ℝ :=
  finiteComplexSymplecticDensityInFrame
    (finiteComplexRiemannianDerivative I F x) e

/-- The intrinsic signed finite symplectic density of a manifold map,
computed in the positive frame selected by the fiberwise orientation. -/
def orientedFiniteComplexRiemannianSymplecticDensity
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : M → ι → ℂ) (x : M) : ℝ :=
  finiteComplexRiemannianSymplecticDensityInFrame I F x
    (o.positiveOrthonormalBasis I x)

/-- Every positive orthonormal tangent frame evaluates the intrinsic signed
finite symplectic density. -/
theorem orientedFiniteComplexRiemannianSymplecticDensity_eq_frame
    {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)] [Fintype ι] [Finite ι]
    (o : RiemannianTangentPlaneOrientation I M)
    (F : M → ι → ℂ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (he : e.toBasis.orientation = o.orientation x) :
    orientedFiniteComplexRiemannianSymplecticDensity I o F x =
      finiteComplexRiemannianSymplecticDensityInFrame I F x e := by
  unfold orientedFiniteComplexRiemannianSymplecticDensity
    finiteComplexRiemannianSymplecticDensityInFrame
  exact finiteComplexSymplecticDensityInFrame_eq_of_same_orientation
    (finiteComplexRiemannianDerivative I F x)
    (o.positiveOrthonormalBasis I x) e
    ((o.positiveOrthonormalBasis_orientation I x).trans he.symm)

/-- The intrinsic signed finite resonant density determined by a fiberwise
tangent-plane orientation. -/
def orientedFiniteResonantRiemannianSymplecticDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (boundary : UnitAddCircle → M) (N : ℕ) (lam : ℝ) (x : M) : ℝ :=
  orientedFiniteComplexRiemannianSymplecticDensity I o
    (fun u n ↦ finiteResonantProfileMap boundary N lam u n) x

/-- Any positive orthonormal tangent frame computes the intrinsic signed
finite resonant density. -/
theorem orientedFiniteResonantRiemannianSymplecticDensity_eq_frame
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I M)
    (boundary : UnitAddCircle → M) (N : ℕ) (lam : ℝ) (x : M)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (he : e.toBasis.orientation = o.orientation x) :
    orientedFiniteResonantRiemannianSymplecticDensity
        I o boundary N lam x =
      finiteResonantRiemannianSymplecticDensity I boundary N lam x e := by
  rw [orientedFiniteResonantRiemannianSymplecticDensity,
    orientedFiniteComplexRiemannianSymplecticDensity_eq_frame I o
      (fun u n ↦ finiteResonantProfileMap boundary N lam u n) x e he]
  rfl

#print axioms finiteComplexSymplecticPullback_apply
#print axioms finiteComplexSymplecticDensityInFrame_eq_of_same_orientation
#print axioms finiteComplexSymplecticDensityInFrame_eq_neg_of_opposite_orientation
#print axioms orientedFiniteComplexRiemannianSymplecticDensity_eq_frame
#print axioms orientedFiniteResonantRiemannianSymplecticDensity_eq_frame

end

end GromovFilling
