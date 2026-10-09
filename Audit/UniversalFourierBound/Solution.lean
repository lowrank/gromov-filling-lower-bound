import Audit.UniversalFourierBound.Defs
import GromovFilling.RiemannianUniversalFourierBound

/-!
# Comparator solution: the universal Fourier bound (Theorem 1.1)

The definitions are those of `Defs.lean`, shared with the challenge.
`Bridge` identifies them with the project's (each is a copy, so the identifications
are `rfl`), and the theorem follows from
`GromovFilling.riemannian_universal_fourier_bound`,
`GromovFilling.nonempty_controlledInteriorAtlas` and
`GromovFilling.ControlledInteriorAtlas.areaMeasure_eq_riemannianSurfaceAreaMeasure`.
-/

open Bundle MeasureTheory Set
open scoped BigOperators Bundle ENNReal Manifold NNReal

namespace GromovFillingAudit.UniversalFourierBound

noncomputable section

namespace Bridge

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The project's atlas with the same fields. -/
def toProject (A : ControlledInteriorAtlas I M) : GromovFilling.ControlledInteriorAtlas I M where
  parametrization := A.parametrization
  coordinate := A.coordinate
  domain := A.domain
  lipschitzConstant := A.lipschitzConstant
  isOpen_domain := A.isOpen_domain
  continuousOn_parametrization := A.continuousOn_parametrization
  contMDiffOn_parametrization := A.contMDiffOn_parametrization
  injOn_parametrization := A.injOn_parametrization
  coordinate_parametrization := A.coordinate_parametrization
  mdifferentiableAt_coordinate := A.mdifferentiableAt_coordinate
  mdifferentiableAt_of_differentiableAt_comp := A.mdifferentiableAt_of_differentiableAt_comp
  isOpen_image := A.isOpen_image
  image_subset_interior := A.image_subset_interior
  lipschitzOnWith_parametrization := A.lipschitzOnWith_parametrization
  interior_subset_iUnion_image := A.interior_subset_iUnion_image
  eventually_domain_eq_empty := A.eventually_domain_eq_empty

/-- This file's atlas with the same fields as a project atlas. -/
def ofProject (A : GromovFilling.ControlledInteriorAtlas I M) : ControlledInteriorAtlas I M where
  parametrization := A.parametrization
  coordinate := A.coordinate
  domain := A.domain
  lipschitzConstant := A.lipschitzConstant
  isOpen_domain := A.isOpen_domain
  continuousOn_parametrization := A.continuousOn_parametrization
  contMDiffOn_parametrization := A.contMDiffOn_parametrization
  injOn_parametrization := A.injOn_parametrization
  coordinate_parametrization := A.coordinate_parametrization
  mdifferentiableAt_coordinate := A.mdifferentiableAt_coordinate
  mdifferentiableAt_of_differentiableAt_comp := A.mdifferentiableAt_of_differentiableAt_comp
  isOpen_image := A.isOpen_image
  image_subset_interior := A.image_subset_interior
  lipschitzOnWith_parametrization := A.lipschitzOnWith_parametrization
  interior_subset_iUnion_image := A.interior_subset_iUnion_image
  eventually_domain_eq_empty := A.eventually_domain_eq_empty

/-- The copied area measure is the project's, atlas by atlas. -/
theorem areaMeasure_toProject [MeasurableSpace M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) :
    A.areaMeasure I = (toProject A).areaMeasure I :=
  rfl

theorem universalConstant_eq : universalConstant = GromovFilling.universalConstant :=
  rfl

end Bridge

/-- **Theorem 1.1 (Universal Fourier bound).** A compact connected Riemannian
filling of an isometric circle of circumference `2π` has a controlled interior
atlas, and every such atlas gives it area at least `14 ζ(3) / π`. -/
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
    Nonempty (ControlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2) S) ∧
      ∀ A : ControlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2) S,
        ENNReal.ofReal universalConstant ≤
          A.areaMeasure (modelWithCornersEuclideanHalfSpace 2) (Set.univ : Set S) := by
  haveI : Nonempty S := ⟨boundary 0⟩
  have hmain := GromovFilling.riemannian_universal_fourier_bound S boundary hboundary hboundaryRange
  have hne : Nonempty (GromovFilling.ControlledInteriorAtlas
      (modelWithCornersEuclideanHalfSpace 2) S) :=
    GromovFilling.nonempty_controlledInteriorAtlas (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
  refine ⟨⟨Bridge.ofProject (Classical.choice hne)⟩, fun A => ?_⟩
  rw [Bridge.areaMeasure_toProject, Bridge.universalConstant_eq,
    GromovFilling.ControlledInteriorAtlas.areaMeasure_eq_riemannianSurfaceAreaMeasure]
  exact hmain

end

end GromovFillingAudit.UniversalFourierBound
