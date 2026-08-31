import GromovFilling.RiemannianControlledBoundaryPhaseSubstitution

/-!
# Boundary parameters on controlled chart axes

The imaginary axis of a half-space chart parametrizes genuine manifold
boundary points wherever it belongs to the extended-chart domain.  For a
boundary parametrization whose range is the whole manifold boundary, this
identifies every nonzero controlled boundary trace with a canonical circle
parameter, chosen by `Function.invFun`.

This is the topological part of the induced-boundary reparametrization
bridge.  Constructing differentiable real lifts of these circle parameters,
with the sign imposed by the surface orientation, remains separate.
-/

open Bundle Filter Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]

/-- Every imaginary-axis coordinate in a half-space extended-chart domain
maps to the manifold boundary. -/
theorem halfSpaceComplexExtChart_real_mul_I_mem_boundary
    (x : M) (y : ℝ)
    (hyDomain : (y * Complex.I : ℂ) ∈
      halfSpaceComplexExtChartDomain x) :
    halfSpaceComplexExtChart x (y * Complex.I) ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  let z : ℂ := y * Complex.I
  have htarget : Complex.orthonormalBasisOneI.repr z ∈
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target :=
    hyDomain
  have hsourceExt :
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm
          (Complex.orthonormalBasisOneI.repr z) ∈
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).source :=
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).map_target htarget
  have hsource :
      (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm
          (Complex.orthonormalBasisOneI.repr z) ∈
        (chartAt (EuclideanHalfSpace 2) x).source := by
    simpa only [extChartAt_source] using hsourceExt
  change (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint
    ((extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm
      (Complex.orthonormalBasisOneI.repr z))
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint
    (I := modelWithCornersEuclideanHalfSpace 2) _]
  intro hinterior
  have hcoord :
      extChartAt (modelWithCornersEuclideanHalfSpace 2) x
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) x).symm
            (Complex.orthonormalBasisOneI.repr z)) ∈
        interior
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) x).target :=
    ((modelWithCornersEuclideanHalfSpace 2).isInteriorPoint_iff_of_mem_atlas
        one_ne_zero
        (chart_mem_atlas (EuclideanHalfSpace 2) x) hsource).mp hinterior
  rw [(extChartAt (modelWithCornersEuclideanHalfSpace 2) x).right_inv
    htarget] at hcoord
  have hrange : Complex.orthonormalBasisOneI.repr z ∈
      interior (Set.range (modelWithCornersEuclideanHalfSpace 2)) :=
    interior_mono (extChartAt_target_subset_range x) hcoord
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hrange
  have hzRealPos : 0 < z.re := by
    simpa only [Complex.orthonormalBasisOneI_repr_apply] using hrange
  have : (0 : ℝ) < 0 := by
    simpa only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self] using hzRealPos
  exact (lt_irrefl 0) this

/-- A nonzero controlled cutoff on the imaginary axis lies at a genuine
manifold-boundary point. -/
theorem halfSpaceComplexExtChart_real_mul_I_mem_boundary_of_cutoff_ne_zero
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    halfSpaceComplexExtChart (P.center i) (y * Complex.I) ∈
      (modelWithCornersEuclideanHalfSpace 2).boundary M := by
  apply halfSpaceComplexExtChart_real_mul_I_mem_boundary
  by_contra hyDomain
  exact hyCutoff
    (controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hyDomain)

/-- The circle parameter obtained by applying the set-theoretic inverse of a
boundary parametrization to a controlled chart-axis point. -/
def controlledBoundaryChartParameter
    (boundary : UnitAddCircle → M)
    (P : FiniteControlledBoundaryChartPartition M)
    (i : P.ι) (y : ℝ) : UnitAddCircle :=
  Function.invFun boundary
    (halfSpaceComplexExtChart (P.center i) (y * Complex.I))

/-- On the nonzero trace of a controlled cutoff, the canonical circle
parameter maps back to the original chart-axis point. -/
theorem boundary_controlledBoundaryChartParameter_of_cutoff_ne_zero
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    boundary (controlledBoundaryChartParameter boundary P i y) =
      halfSpaceComplexExtChart (P.center i) (y * Complex.I) := by
  unfold controlledBoundaryChartParameter
  apply Function.invFun_eq
  rw [← Set.mem_range, hboundaryRange]
  exact
    halfSpaceComplexExtChart_real_mul_I_mem_boundary_of_cutoff_ne_zero
      P i y hyCutoff

/-- The controlled cutoff restricted to the boundary axis is a continuous
real function.  A global Lipschitz cutoff extension supplies the proof while
agreeing exactly on the closed half-plane. -/
theorem continuous_controlledBoundaryChartCutoff_real_mul_I
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    Continuous (fun y : ℝ ↦
      controlledBoundaryChartCutoff P i (y * Complex.I)) := by
  obtain ⟨C, ρ, hρLipschitz, _hρCompact, hρEq, _hρNonneg, _hρLe⟩ :=
    exists_controlledBoundaryChartCutoffExtension P i
  have hfun :
      (fun y : ℝ ↦ controlledBoundaryChartCutoff P i (y * Complex.I)) =
        fun y : ℝ ↦ ρ (y * Complex.I) := by
    funext y
    exact (hρEq (real_mul_I_mem_complexRightClosedHalfPlane y)).symm
  rw [hfun]
  exact hρLipschitz.continuous.comp (by fun_prop)

/-- Near every nonzero controlled boundary trace, the chart axis agrees with
the supplied boundary parametrization evaluated at its canonical circle
parameter. -/
theorem chartAxis_eventuallyEq_boundary_controlledBoundaryChartParameter
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    (fun t : ℝ ↦
        halfSpaceComplexExtChart (P.center i) (t * Complex.I)) =ᶠ[nhds y]
      fun t : ℝ ↦
        boundary (controlledBoundaryChartParameter boundary P i t) := by
  have hne : ∀ᶠ t : ℝ in nhds y,
      controlledBoundaryChartCutoff P i (t * Complex.I) ≠ 0 :=
    (continuous_controlledBoundaryChartCutoff_real_mul_I P i).continuousAt.eventually_ne
      hyCutoff
  filter_upwards [hne] with t ht
  exact (boundary_controlledBoundaryChartParameter_of_cutoff_ne_zero
    boundary hboundaryRange P i t ht).symm

/-- The canonical circle parameter is continuous at every nonzero controlled
boundary trace.  The inverse of the boundary parametrization is continuous on
its image because an isometric circle boundary is a closed embedding; the
chart-axis representative is continuous while it remains in the extended
chart domain. -/
theorem continuousAt_controlledBoundaryChartParameter_of_cutoff_ne_zero
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyCutoff : controlledBoundaryChartCutoff P i
      (y * Complex.I) ≠ 0) :
    ContinuousAt (controlledBoundaryChartParameter boundary P i) y := by
  have hboundaryEmbedding : Topology.IsClosedEmbedding boundary :=
    hboundary.lipschitzWith.continuous.isClosedEmbedding hboundary.injective
  apply hboundaryEmbedding.isInducing.continuousAt_iff.mpr
  have hyDomain : (y * Complex.I : ℂ) ∈
      halfSpaceComplexExtChartDomain (P.center i) := by
    by_contra hyDomain
    exact hyCutoff
      (controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hyDomain)
  have hne : ∀ᶠ t : ℝ in nhds y,
      controlledBoundaryChartCutoff P i (t * Complex.I) ≠ 0 :=
    (continuous_controlledBoundaryChartCutoff_real_mul_I P i).continuousAt.eventually_ne
      hyCutoff
  have haxisDomain : ∀ᶠ t : ℝ in nhds y,
      (t * Complex.I : ℂ) ∈
        halfSpaceComplexExtChartDomain (P.center i) := by
    filter_upwards [hne] with t ht
    by_contra htDomain
    exact ht
      (controlledBoundaryChartCutoff_eq_zero_of_not_mem P i htDomain)
  have hcoordWithin :
      Tendsto (fun t : ℝ ↦ (t * Complex.I : ℂ)) (nhds y)
        (nhdsWithin (y * Complex.I)
          (halfSpaceComplexExtChartDomain (P.center i))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (show ContinuousAt (fun t : ℝ ↦ (t * Complex.I : ℂ)) y by
        fun_prop)
      haxisDomain
  have haxis : ContinuousAt
      (fun t : ℝ ↦
        halfSpaceComplexExtChart (P.center i) (t * Complex.I)) y :=
    (continuousOn_halfSpaceComplexExtChart (P.center i) _ hyDomain).tendsto.comp
      hcoordWithin
  have hboundaryParameter : ContinuousAt
      (fun t : ℝ ↦
        boundary (controlledBoundaryChartParameter boundary P i t)) y :=
    haxis.congr_of_eventuallyEq
      (chartAxis_eventuallyEq_boundary_controlledBoundaryChartParameter
        boundary hboundaryRange P i y hyCutoff).symm
  simpa only [Function.comp_apply] using hboundaryParameter

#print axioms halfSpaceComplexExtChart_real_mul_I_mem_boundary
#print axioms
  halfSpaceComplexExtChart_real_mul_I_mem_boundary_of_cutoff_ne_zero
#print axioms controlledBoundaryChartParameter
#print axioms boundary_controlledBoundaryChartParameter_of_cutoff_ne_zero
#print axioms continuous_controlledBoundaryChartCutoff_real_mul_I
#print axioms
  chartAxis_eventuallyEq_boundary_controlledBoundaryChartParameter
#print axioms
  continuousAt_controlledBoundaryChartParameter_of_cutoff_ne_zero

end

end GromovFilling
