import GromovFilling.OrientedRiemannianPrimitiveChart
import GromovFilling.RiemannianControlledBoundaryTrace

/-!
# Genuine primitive-error densities for controlled boundary charts

The controlled weak-Stokes package initially leaves its cutoff-primitive
error in terms of globally Lipschitz Euclidean extensions.  This module
removes those extensions.  On the support of the cutoff, both extensions
agree locally with the genuine manifold data.  At a zero of the nonnegative
cutoff, Fermat's theorem makes the cutoff derivative—and hence the entire
primitive error—vanish.

The resulting chart density factors through the signed Riemannian chart
Jacobian and the intrinsic oriented primitive-error density.  Global chart
orientation signs and boundary gluing remain separate obligations.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped ContDiff Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

local instance controlledBoundaryEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- A globally nonnegative real function has zero Fréchet derivative at
every point where it vanishes.  This includes the nondifferentiable case,
where `fderiv` is zero by definition. -/
theorem fderiv_eq_zero_of_nonneg_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → ℝ) (x : E) (hρ : ∀ y, 0 ≤ ρ y) (hx : ρ x = 0) :
    fderiv ℝ ρ x = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  show ∀ᶠ y in nhds x, ρ x ≤ ρ y
  filter_upwards with y
  rw [hx]
  exact hρ y

/-- The actual planar primitive-error expression vanishes at a zero of a
nonnegative cutoff. -/
theorem finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
    {ι : Type*} [Fintype ι] (ρ : ℂ → ℝ) (F : ℂ → ι → ℂ) (z : ℂ)
    (hρ : ∀ w, 0 ≤ ρ w) (hz : ρ z = 0) :
    finiteSymplecticFDerivPrimitiveError ρ F z = 0 := by
  unfold finiteSymplecticFDerivPrimitiveError
  rw [fderiv_eq_zero_of_nonneg_of_eq_zero ρ z hρ hz]
  simp

/-- The Fréchet primitive error only depends on the germs of the cutoff and
finite complex map at its base point. -/
theorem finiteSymplecticFDerivPrimitiveError_eq_of_eventuallyEq
    {ι : Type*} [Fintype ι]
    {ρ σ : ℂ → ℝ} {F H : ℂ → ι → ℂ} {z : ℂ}
    (hρ : ρ =ᶠ[nhds z] σ) (hF : F =ᶠ[nhds z] H) :
    finiteSymplecticFDerivPrimitiveError ρ F z =
      finiteSymplecticFDerivPrimitiveError σ H z := by
  unfold finiteSymplecticFDerivPrimitiveError
  rw [hF.self_of_nhds,
    Filter.EventuallyEq.fderiv_eq hρ,
    Filter.EventuallyEq.fderiv_eq hF]

/-- On the interior part of a controlled boundary chart, the extension-based
primitive error is exactly the primitive error of the genuine partition
function and surface-map pullback. -/
theorem ControlledBoundaryChartWeakStokesData.primitiveError_eq_comp
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G) {z : ℂ}
    (hz : z ∈ halfSpaceComplexExtChartDomain (P.center i) ∩
      complexRightOpenHalfPlane) :
    finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z =
      finiteSymplecticFDerivPrimitiveError
        (P.partition i ∘ halfSpaceComplexExtChart (P.center i))
        (G ∘ halfSpaceComplexExtChart (P.center i)) z := by
  by_cases hzCutoff : controlledBoundaryChartCutoff P i z = 0
  · have hzRightClosed : z ∈ complexRightClosedHalfPlane := by
      change 0 ≤ z.re
      exact hz.2.le
    have hDzero : D.cutoff z = 0 :=
      (D.cutoff_eq hzRightClosed).trans hzCutoff
    have hPzero :
        (P.partition i ∘ halfSpaceComplexExtChart (P.center i)) z = 0 := by
      change P.partition i
        (halfSpaceComplexExtChart (P.center i) z) = 0
      rw [← controlledBoundaryChartCutoff_eq_of_mem P i hz.1]
      exact hzCutoff
    calc
      finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z = 0 :=
        finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
          D.cutoff D.chartMap z D.cutoff_nonneg hDzero
      _ = finiteSymplecticFDerivPrimitiveError
          (P.partition i ∘ halfSpaceComplexExtChart (P.center i))
          (G ∘ halfSpaceComplexExtChart (P.center i)) z :=
        (finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
          (P.partition i ∘ halfSpaceComplexExtChart (P.center i))
          (G ∘ halfSpaceComplexExtChart (P.center i)) z
          (fun w ↦ P.partition_nonneg i
            (halfSpaceComplexExtChart (P.center i) w)) hPzero).symm
  · exact finiteSymplecticFDerivPrimitiveError_eq_of_eventuallyEq
      (D.cutoff_eventuallyEq_partition hz)
      (D.chartMap_eventuallyEq_of_cutoff_ne_zero hz.2 hzCutoff)

/-- The genuine controlled-chart primitive-error density, written as signed
chart Jacobian times intrinsic oriented density and extended by zero outside
the inverse-chart domain. -/
def controlledBoundaryChartPrimitiveErrorDensity
    (P : FiniteControlledBoundaryChartPartition M)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (i : P.ι) {ι : Type uι} [Fintype ι]
    (G : M → ι → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ halfSpaceComplexExtChartDomain (P.center i) then
      orientedRiemannianChartJacobian
          (modelWithCornersEuclideanHalfSpace 2) o
          (halfSpaceComplexExtChart (P.center i)) z *
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          (modelWithCornersEuclideanHalfSpace 2) o (P.partition i) G
          (halfSpaceComplexExtChart (P.center i) z)
    else 0

/-- On the open half-plane, the extension-based primitive error is the
genuine intrinsic chart density. -/
theorem ControlledBoundaryChartWeakStokesData.primitiveError_eq_chartDensity
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane) :
    finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z =
      controlledBoundaryChartPrimitiveErrorDensity P o i G z := by
  by_cases hzDomain : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · rw [controlledBoundaryChartPrimitiveErrorDensity, if_pos hzDomain,
      D.primitiveError_eq_comp ⟨hzDomain, hzRight⟩]
    exact finiteSymplecticFDerivPrimitiveError_comp_parametrization_eq_jacobian_mul
      (modelWithCornersEuclideanHalfSpace 2) o (P.partition i) G
      (halfSpaceComplexExtChart (P.center i)) z
      (mdifferentiableAt_halfSpaceComplexExtChart
        (P.center i) ⟨hzDomain, hzRight⟩)
      ((P.contMDiff_partition i).mdifferentiableAt (by simp))
      (fun j ↦ (hG j) _)
  · have hzRightClosed : z ∈ complexRightClosedHalfPlane := by
      change 0 ≤ z.re
      change 0 < z.re at hzRight
      exact hzRight.le
    have hDzero : D.cutoff z = 0 := by
      rw [D.cutoff_eq hzRightClosed,
        controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hzDomain]
    rw [controlledBoundaryChartPrimitiveErrorDensity, if_neg hzDomain]
    exact finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
      D.cutoff D.chartMap z D.cutoff_nonneg hDzero

/-- The primitive-error integral in controlled weak Stokes can therefore be
written entirely with the genuine manifold partition, map, orientation, and
chart Jacobian. -/
theorem ControlledBoundaryChartWeakStokesData.integral_primitiveError_eq_chartDensity
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) :
    (∫ z in complexRightOpenHalfPlane,
        finiteSymplecticFDerivPrimitiveError D.cutoff D.chartMap z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartPrimitiveErrorDensity P o i G z := by
  apply integral_congr_ae
  filter_upwards
      [ae_restrict_mem isOpen_complexRightOpenHalfPlane.measurableSet] with z hz
  exact D.primitiveError_eq_chartDensity o hG hz

/-- Fully genuine chart-local weak Stokes: volume, primitive error, and
boundary action now all use the original surface data. -/
theorem ControlledBoundaryChartWeakStokesData.integral_controlledBoundaryChartSymplecticDensity_eq_chartPrimitiveError
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (o : RiemannianTangentPlaneOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) :
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartSymplecticDensity P i G z) =
      (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartPrimitiveErrorDensity P o i G z) -
        ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  rw [← D.integral_primitiveError_eq_chartDensity o hG]
  exact D.integral_controlledBoundaryChartSymplecticDensity_eq

#print axioms fderiv_eq_zero_of_nonneg_of_eq_zero
#print axioms
  finiteSymplecticFDerivPrimitiveError_eq_zero_of_cutoff_eq_zero
#print axioms finiteSymplecticFDerivPrimitiveError_eq_of_eventuallyEq
#print axioms ControlledBoundaryChartWeakStokesData.primitiveError_eq_comp
#print axioms controlledBoundaryChartPrimitiveErrorDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.primitiveError_eq_chartDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_primitiveError_eq_chartDensity
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_controlledBoundaryChartSymplecticDensity_eq_chartPrimitiveError

end

end GromovFilling
