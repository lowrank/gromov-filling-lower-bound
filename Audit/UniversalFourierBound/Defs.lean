import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Disjointed

/-!
# Definitions for the comparator challenge of Theorem 1.1

Imported by both `Challenge.lean` and `Solution.lean`, so that the two refer to the
same constants. Mathlib imports only; every definition is copied verbatim from
`GromovFilling` (Constants, DistanceProfile, RiemannianTwoJacobian,
RiemannianChartArea, RiemannianAtlasArea, RiemannianChartDisjointification and
RiemannianInteriorAtlasArea). The two `Fact` instances are scoped to this
namespace so that both files see the same instances.
-/

open Bundle MeasureTheory Set
open scoped BigOperators Bundle ENNReal Manifold NNReal

namespace GromovFillingAudit.UniversalFourierBound

noncomputable section

scoped instance complexFinrankTwoFact :
    Fact (Module.finrank ℝ ℂ = 2) :=
  Complex.finrank_real_complex_fact

scoped instance euclideanPlaneFinrankTwoFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

/-- `ζ(3)`, as the cubic `p`-series (the `n = 0` term is `1 / 0 = 0`). -/
def zetaThree : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ 3

/-- The constant in the orientation-free Fourier theorem. -/
def universalConstant : ℝ :=
  14 * zetaThree / Real.pi

/-- A parametrized boundary circle of circumference `2π` is isometric when
the ambient distance is `2π` times the standard distance on `ℝ / ℤ`. -/
def IsometricCircleBoundary {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ s t, dist (boundary s) (boundary t) =
    2 * Real.pi * dist s t

/-- The absolute determinant of a linear map, computed in orthonormal bases. -/
def metricJacobianWithBases
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ E)
    (f : OrthonormalBasis (Fin n) ℝ F) (L : E →L[ℝ] F) : ℝ :=
  |(LinearMap.toMatrix e.toBasis f.toBasis L.toLinearMap).det|

/-- A fixed orthonormal basis of a real two-dimensional inner-product space. -/
def canonicalOrthonormalBasisTwo
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [hE : Fact (Module.finrank ℝ E = 2)] :
    OrthonormalBasis (Fin 2) ℝ E := by
  letI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_fact_finrank_eq_two
  exact (stdOrthonormalBasis ℝ E).reindex (finCongr hE.out)

/-- The intrinsic two-dimensional metric Jacobian of a continuous real
linear map. -/
def twoJacobian
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ E = 2)]
    [Fact (Module.finrank ℝ F = 2)] (L : E →L[ℝ] F) : ℝ :=
  metricJacobianWithBases
    (canonicalOrthonormalBasisTwo E)
    (canonicalOrthonormalBasisTwo F) L

theorem tangentSpace_finrank_eq_two
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [hE : Fact (Module.finrank ℝ E = 2)] (x : M) :
    Module.finrank ℝ (TangentSpace I x) = 2 := by
  simpa only [TangentSpace] using hE.out

/-- The manifold differential, bundled with the Riemannian norms on its
source and target tangent fibers. -/
def riemannianMFDerivBetween
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [RiemannianBundle (fun x : M₁ ↦ TangentSpace I₁ x)]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [RiemannianBundle (fun x : M₂ ↦ TangentSpace I₂ x)]
    (G : M₁ → M₂) (x : M₁) :
    TangentSpace I₁ x →L[ℝ] TangentSpace I₂ (G x) :=
  mfderiv I₁ I₂ G x

/-- The pointwise intrinsic `J₂` of a map between two two-dimensional
Riemannian manifolds. -/
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
  exact twoJacobian (riemannianMFDerivBetween I₁ I₂ G x)

/-- The `ℝ≥0∞`-valued area density of a parametrization from the Euclidean
complex plane into a two-dimensional Riemannian manifold. -/
def riemannianChartDensity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (riemannianTwoJacobianBetween 𝓘(ℝ, ℂ) I F z)

/-- The area measure contributed by one parametrized chart domain. -/
def riemannianChartAreaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ℂ → M) (s : Set ℂ) : Measure M :=
  Measure.map F
    ((volume.restrict s).withDensity (riemannianChartDensity I F))

/-- The sum of the Jacobian-weighted area measures contributed by a family of
parametrized complex-plane chart pieces. -/
def riemannianAtlasAreaMeasure
    {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [MeasurableSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (F : ι → ℂ → M) (pieces : ι → Set ℂ) : Measure M :=
  Measure.sum (fun i ↦ riemannianChartAreaMeasure I (F i) (pieces i))

/-- The part of the `n`th coordinate domain whose image has not already
appeared in an earlier chart image. -/
def disjointChartPiece
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) (n : ℕ) : Set X :=
  domains n ∩ F n ⁻¹'
    disjointed (fun i ↦ F i '' domains i) n

/-- A countable family of controlled complex parametrizations whose images
cover the manifold interior, with finite support. -/
structure ControlledInteriorAtlas
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] where
  parametrization : ℕ → ℂ → M
  coordinate : ℕ → M → ℂ
  domain : ℕ → Set ℂ
  lipschitzConstant : ℕ → ℝ≥0
  isOpen_domain : ∀ i, IsOpen (domain i)
  continuousOn_parametrization :
    ∀ i, ContinuousOn (parametrization i) (domain i)
  contMDiffOn_parametrization :
    ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) I 1 (parametrization i) (domain i)
  injOn_parametrization :
    ∀ i, Set.InjOn (parametrization i) (domain i)
  coordinate_parametrization :
    ∀ i z, z ∈ domain i → coordinate i (parametrization i z) = z
  mdifferentiableAt_coordinate :
    ∀ i y, y ∈ parametrization i '' domain i →
      MDifferentiableAt I 𝓘(ℝ, ℂ) (coordinate i) y
  mdifferentiableAt_of_differentiableAt_comp :
    ∀ i (G : M → ℂ) z, z ∈ domain i →
      DifferentiableAt ℝ (G ∘ parametrization i) z →
        MDifferentiableAt I 𝓘(ℝ, ℂ) G (parametrization i z)
  isOpen_image : ∀ i, IsOpen (parametrization i '' domain i)
  image_subset_interior :
    ∀ i, parametrization i '' domain i ⊆ I.interior M
  lipschitzOnWith_parametrization :
    ∀ i, LipschitzOnWith (lipschitzConstant i)
      (parametrization i) (domain i)
  interior_subset_iUnion_image :
    I.interior M ⊆ ⋃ i, parametrization i '' domain i
  eventually_domain_eq_empty :
    ∃ N, ∀ i, N ≤ i → domain i = ∅

namespace ControlledInteriorAtlas

/-- Pull the first-occurrence assignment on chart images back to each
coordinate domain. -/
def piece
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (A : ControlledInteriorAtlas I M) (i : ℕ) : Set ℂ :=
  disjointChartPiece A.parametrization A.domain i

/-- The Riemannian area measure contributed by a disjoint controlled
interior atlas. -/
def areaMeasure
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [MeasurableSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) : Measure M :=
  riemannianAtlasAreaMeasure I A.parametrization (A.piece I)

end ControlledInteriorAtlas

end

end GromovFillingAudit.UniversalFourierBound
