import GromovFilling.JordanSchoenfliesCoverage
import GromovFilling.RiemannianInteriorAtlasArea
import GromovFilling.RiemannianInteriorCoverage

/-!
# Lemma 5.4: coverage and Riemannian area

This file gives the manuscript-facing conclusion of Lemma 5.4.  The
topological half covers the canonical bounded component of the embedded
boundary trace using interior preimages.  The analytic half applies the
canonical Riemannian surface-area formula to those preimages.
-/

open Bundle MeasureTheory Set
open scoped ENNReal Manifold NNReal

namespace GromovFilling

noncomputable section

local instance euclideanPlaneFinrankTwoFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- **Lemma 5.4, interior coverage.**  The bounded Jordan component has
preimages in the manifold interior; no boundary preimage is needed. -/
theorem lemma54_schoenfliesJordanInterior_subset_image_interior
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (boundary : UnitAddCircle → S)
    (hboundaryContinuous : Continuous boundary)
    (hboundaryInjective : Function.Injective boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S)
    (G : S → ℂ) (hG : Continuous G)
    (htraceInjective : Function.Injective (G ∘ boundary)) :
    schoenfliesJordanInterior (G ∘ boundary) ⊆
      G '' (modelWithCornersEuclideanHalfSpace 2).interior S := by
  apply subset_image_interior_of_subset_range_of_boundary_mapsTo
    (modelWithCornersEuclideanHalfSpace 2) G
    (schoenfliesJordanInterior (G ∘ boundary))
    (Set.range (G ∘ boundary))
  · exact schoenfliesJordanInterior_disjoint_range (G ∘ boundary)
  · intro x hx
    rw [← hboundaryRange] at hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t, rfl⟩
  · exact lemma54_schoenfliesJordanInterior_subset_range S boundary
      hboundaryContinuous hboundaryInjective hboundaryRange G hG
      htraceInjective

/-- **Lemma 5.4, full Riemannian conclusion.**  For a compact connected
Riemannian surface with exactly one parametrized boundary component, every
Lipschitz map whose boundary restriction is a topological embedding has
intrinsic two-Jacobian integral at least the Euclidean area of the bounded
Jordan component enclosed by its boundary trace. -/
theorem lemma54_riemannian_area
    (S : Type*) [PseudoEMetricSpace S] [T2Space S]
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
    (hboundaryContinuous : Continuous boundary)
    (hboundaryInjective : Function.Injective boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S)
    (G : S → ℂ) {KG : ℝ≥0} (hG : LipschitzWith KG G)
    (htraceInjective : Function.Injective (G ∘ boundary)) :
    letI : Nonempty S := ⟨boundary 0⟩
    letI : Nonempty (ControlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2) S) :=
      nonempty_controlledInteriorAtlas
        (modelWithCornersEuclideanHalfSpace 2)
        Complex.orthonormalBasisOneI.repr
    volume (schoenfliesJordanInterior (G ∘ boundary)) ≤
      ∫⁻ x, ENNReal.ofReal
          (riemannianTwoJacobian
            (modelWithCornersEuclideanHalfSpace 2) G x)
        ∂riemannianSurfaceAreaMeasure
          (modelWithCornersEuclideanHalfSpace 2) := by
  letI : Nonempty S := ⟨boundary 0⟩
  letI : Nonempty (ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) S) :=
    nonempty_controlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  exact complex_volume_le_lintegral_riemannianTwoJacobian
    (modelWithCornersEuclideanHalfSpace 2) G
      (schoenfliesJordanInterior (G ∘ boundary)) hG
      (lemma54_schoenfliesJordanInterior_subset_image_interior S boundary
        hboundaryContinuous hboundaryInjective hboundaryRange G
        hG.continuous htraceInjective)

end

end GromovFilling

#print axioms GromovFilling.lemma54_schoenfliesJordanInterior_subset_image_interior
#print axioms GromovFilling.lemma54_riemannian_area
