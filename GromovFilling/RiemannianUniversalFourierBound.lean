import GromovFilling.RiemannianProfileFourierAE
import GromovFilling.Lemma54Area
import GromovFilling.GivensDiskArea
import GromovFilling.Certificates

/-!
# The universal Fourier bound for Riemannian fillings

This module assembles the exact orientation-free headline theorem.  It
identifies the canonical Schönflies interior of every mixed Givens boundary
curve with its explicit polynomial disk, applies Lemma 5.4 row by row, uses
the canonical surface-area Jacobian budget, and passes the finite Fourier
certificates to `14 ζ(3) / π`.
-/

open Bundle MeasureTheory Set
open scoped BigOperators ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance euclideanPlaneFinrankTwoFactUniversalFourier :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

private theorem givensBoundaryCurveAddCircle_injective
    {N : ℕ} (j : Fin N) :
    Function.Injective (givensBoundaryCurveAddCircle j) := by
  intro x y hxy
  unfold givensBoundaryCurveAddCircle at hxy
  exact unitAddCircleEquivComplexUnitCircle.injective
    (givensBoundaryCurve_injective j hxy)

private theorem zero_mem_schoenfliesJordanInterior_givensBoundaryCurveAddCircle
    {N : ℕ} (j : Fin N) :
    0 ∈ schoenfliesJordanInterior (givensBoundaryCurveAddCircle j) := by
  let curve : UnitAddCircle → ℂ := givensBoundaryCurveAddCircle j
  let curveP : UnitAddCircle → Schoenflies.Plane :=
    complexPlaneHomeomorph ∘ curve
  have hzeroCompl : 0 ∈ (Set.range curve)ᶜ := by
    intro hzero
    obtain ⟨t, ht⟩ := hzero
    exact givensBoundaryCurveAddCircle_ne_zero j t ht
  have hnotRange : complexPlaneHomeomorph 0 ∉ Set.range curveP := by
    rintro ⟨t, ht⟩
    have hzero : curve t = 0 := by
      apply complexPlaneHomeomorph.injective
      simpa only [curveP, Function.comp_apply] using ht
    exact givensBoundaryCurveAddCircle_ne_zero j t hzero
  have hrange : complexPlaneHomeomorph '' Set.range curve =
      Set.range curveP := by
    ext y
    constructor
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨curve t, ⟨t, rfl⟩, rfl⟩
  have hcomponent :=
    complexPlaneHomeomorph.image_connectedComponentIn hzeroCompl
  rw [complexPlaneHomeomorph.image_compl, hrange,
    complexPlaneHomeomorph_apply_zero] at hcomponent
  have hboundedImage : Bornology.IsBounded
      (complexPlaneHomeomorph ''
        connectedComponentIn (Set.range curve)ᶜ 0) := by
    simpa only [complexPlaneHomeomorph] using
      Complex.orthonormalBasisOneI.repr.lipschitz.isBounded_image
        (givensBoundaryCurve_origin_component_bounded j)
  have hboundedComponent : Bornology.IsBounded
      (connectedComponentIn (Set.range curveP)ᶜ
        (complexPlaneHomeomorph 0)) := by
    rw [hcomponent] at hboundedImage
    simpa only [complexPlaneHomeomorph_apply_zero] using hboundedImage
  unfold schoenfliesJordanInterior
  refine ⟨complexPlaneHomeomorph 0, ?_, by simp⟩
  exact ⟨hnotRange, hboundedComponent⟩

theorem schoenfliesJordanInterior_givensBoundaryCurveAddCircle
    {N : ℕ} (j : Fin N) :
    schoenfliesJordanInterior (givensBoundaryCurveAddCircle j) =
      connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 := by
  exact ((schoenfliesJordanInterior_is_bounded_component
    (givensBoundaryCurveAddCircle j)
    (continuous_givensBoundaryCurveAddCircle j)
    (givensBoundaryCurveAddCircle_injective j)).2.2.2 0
      (zero_mem_schoenfliesJordanInterior_givensBoundaryCurveAddCircle j)).symm

theorem volume_schoenfliesJordanInterior_givensBoundaryCurveAddCircle
    {N : ℕ} (j : Fin N) :
    volume (schoenfliesJordanInterior (givensBoundaryCurveAddCircle j)) =
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) := by
  rw [schoenfliesJordanInterior_givensBoundaryCurveAddCircle j,
    ← givensBoundaryPolynomial_image_ball_eq_origin_component j]
  exact volume_givensBoundaryPolynomial_image_ball j

/-- One row of the mixed Fourier family covers its exact Jordan interior,
so Lemma 5.4 bounds its enclosed boundary area by intrinsic Jacobian mass. -/
theorem mixedBoundaryArea_le_lintegral_riemannianTwoJacobian_givensMetricFourierMap
    (S : Type*) [PseudoMetricSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S]
    [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S]
    [RiemannianBundle (fun x : S ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : S ↦
        TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) S]
    (boundary : UnitAddCircle → S)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S)
    {N : ℕ} (j : Fin N) :
    letI : Nonempty S := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) S) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
          (riemannianTwoJacobian
            (modelWithCornersEuclideanHalfSpace 2)
            (givensMetricFourierMap boundary N j) x)
        ∂riemannianSurfaceAreaMeasure
          (modelWithCornersEuclideanHalfSpace 2) := by
  let G : S → ℂ := givensMetricFourierMap boundary N j
  have htrace : G ∘ boundary = givensBoundaryCurveAddCircle j := by
    funext t
    exact givensMetricFourierMap_on_boundary hboundary j t
  have htraceInjective : Function.Injective (G ∘ boundary) := by
    rw [htrace]
    exact givensBoundaryCurveAddCircle_injective j
  letI : Nonempty S := ⟨boundary 0⟩
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) S) :=
    nonempty_controlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  have harea := lemma54_riemannian_area S boundary
    hboundary.lipschitzWith.continuous hboundary.injective hboundaryRange
    G (givensMetricFourierMap_lipschitzWith hboundary N j)
    htraceInjective
  rw [htrace,
    volume_schoenfliesJordanInterior_givensBoundaryCurveAddCircle j] at harea
  exact harea

/-- **Theorem 1.1 (Universal Fourier bound).**  Every compact connected
Riemannian filling of an isometric circle of circumference `2π` has canonical
surface area at least `14 ζ(3) / π`. -/
theorem riemannian_universal_fourier_bound
    (S : Type*) [PseudoMetricSpace S] [T2Space S]
    [MeasurableSpace S] [BorelSpace S]
    [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 S]
    [RiemannianBundle (fun x : S ↦
      TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : S ↦
        TangentSpace (modelWithCornersEuclideanHalfSpace 2) x)]
    [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) S]
    (boundary : UnitAddCircle → S)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S) :
    letI : Nonempty S := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) S) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    ENNReal.ofReal universalConstant ≤
      riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set S) := by
  letI : Nonempty S := ⟨boundary 0⟩
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) S) :=
    nonempty_controlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  apply universal_ennreal_of_givens_coverage_budget
    (riemannianSurfaceAreaMeasure
      (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set S))
  intro N
  let jacobianMass : Fin N → ℝ≥0∞ := fun j ↦
    ∫⁻ x, ENNReal.ofReal
        (riemannianTwoJacobian
          (modelWithCornersEuclideanHalfSpace 2)
          (givensMetricFourierMap boundary N j) x)
      ∂riemannianSurfaceAreaMeasure
        (modelWithCornersEuclideanHalfSpace 2)
  refine ⟨jacobianMass, ?_, ?_⟩
  · intro j
    exact
      mixedBoundaryArea_le_lintegral_riemannianTwoJacobian_givensMetricFourierMap
        S boundary hboundary hboundaryRange j
  · exact
      sum_lintegral_riemannianTwoJacobian_givensMetricFourierMap_le_surfaceArea
        (modelWithCornersEuclideanHalfSpace 2) hboundary N

end

end GromovFilling

#print axioms GromovFilling.volume_schoenfliesJordanInterior_givensBoundaryCurveAddCircle
#print axioms GromovFilling.mixedBoundaryArea_le_lintegral_riemannianTwoJacobian_givensMetricFourierMap
#print axioms GromovFilling.riemannian_universal_fourier_bound
