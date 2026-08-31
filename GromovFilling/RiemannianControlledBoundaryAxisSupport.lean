import GromovFilling.RiemannianControlledBoundaryAxisDomain
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Controlled intervals containing boundary-chart axis supports

The boundary trace of a controlled cutoff is supported in the inner closed
chart ball.  If this trace is nonzero, compactness of the intersection of
that ball with the imaginary axis and the strict inner-to-outer radius margin
produce a larger closed real interval.  The whole larger interval stays in
the controlled chart domain, while every nonzero cutoff point lies in its
open interior.  If the trace is empty, we retain that case explicitly rather
than manufacturing an arbitrary chart interval.
-/

open Bundle Function Manifold Metric Set
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
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- A controlled boundary-chart cutoff either vanishes on the whole
imaginary axis or has all of its nonzero axis trace strictly inside a compact
real interval whose entire closed span remains in the controlled chart
domain. -/
theorem all_zero_or_exists_controlledBoundaryChartAxisInterval
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    (∀ y : ℝ,
      controlledBoundaryChartCutoff P i (y * Complex.I) = 0) ∨
      ∃ a b : ℝ,
        a < b ∧
        (∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
          chosenControlledHalfSpaceComplexChartDomain (P.center i)) ∧
        (∀ y ∉ Set.Ioo a b,
          controlledBoundaryChartCutoff P i (y * Complex.I) = 0) := by
  classical
  by_cases hzero : ∀ y : ℝ,
      controlledBoundaryChartCutoff P i (y * Complex.I) = 0
  · exact Or.inl hzero
  · right
    push_neg at hzero
    obtain ⟨y₀, hy₀Cutoff⟩ := hzero
    let axis : ℝ → ℂ := fun y ↦ y * Complex.I
    let innerAxis : Set ℝ := axis ⁻¹'
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i))
    let outerAxis : Set ℝ := axis ⁻¹'
      ball (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceOuterRadius (P.center i))
    have haxisClosedEmbedding : Topology.IsClosedEmbedding axis := by
      simpa only [axis, Complex.real_smul] using
        (isClosedEmbedding_smul_left (𝕜 := ℝ) (E := ℂ)
          Complex.I_ne_zero)
    have hinnerCompact : IsCompact innerAxis := by
      exact haxisClosedEmbedding.isCompact_preimage
        (isCompact_closedBall
          (controlledHalfSpaceComplexChartCenter (P.center i))
          (controlledHalfSpaceInnerRadius (P.center i)))
    have hy₀Inner : y₀ ∈ innerAxis := by
      exact support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
        P i ⟨hy₀Cutoff,
          real_mul_I_mem_complexRightClosedHalfPlane y₀⟩
    have hinnerNonempty : innerAxis.Nonempty := ⟨y₀, hy₀Inner⟩
    have hinnerOuter : innerAxis ⊆ outerAxis := by
      intro y hy
      exact closedBall_subset_ball
        (controlledHalfSpaceInnerRadius_lt_outer (P.center i)) hy
    have hinfInner : sInf innerAxis ∈ innerAxis :=
      hinnerCompact.sInf_mem hinnerNonempty
    have hsupInner : sSup innerAxis ∈ innerAxis :=
      hinnerCompact.sSup_mem hinnerNonempty
    have hinfOuter : sInf innerAxis ∈ outerAxis :=
      hinnerOuter hinfInner
    have hsupOuter : sSup innerAxis ∈ outerAxis :=
      hinnerOuter hsupInner
    have houterOpen : IsOpen outerAxis := by
      exact isOpen_ball.preimage haxisClosedEmbedding.continuous
    obtain ⟨l, u, hinfIoo, hIooInfOuter⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp
        (houterOpen.mem_nhds hinfOuter)
    obtain ⟨a, hla, haInf⟩ := exists_between hinfIoo.1
    have haOuter : a ∈ outerAxis :=
      hIooInfOuter ⟨hla, haInf.trans hinfIoo.2⟩
    obtain ⟨l', u', hsupIoo, hIooSupOuter⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp
        (houterOpen.mem_nhds hsupOuter)
    obtain ⟨b, hSupB, hbu'⟩ := exists_between hsupIoo.2
    have hbOuter : b ∈ outerAxis :=
      hIooSupOuter ⟨hsupIoo.1.trans hSupB, hbu'⟩
    have hInfSup : sInf innerAxis ≤ sSup innerAxis :=
      (hinnerCompact.isLeast_sInf hinnerNonempty).2 hsupInner
    have hab : a < b :=
      (haInf.trans_le hInfSup).trans hSupB
    have houterConvex : Convex ℝ outerAxis := by
      simpa only [outerAxis, axis, LinearMap.toSpanSingleton_apply,
        Complex.real_smul] using
        (convex_ball
          (controlledHalfSpaceComplexChartCenter (P.center i))
          (controlledHalfSpaceOuterRadius (P.center i))).linear_preimage
            (LinearMap.toSpanSingleton ℝ ℂ Complex.I)
    have hIccOuter : Set.Icc a b ⊆ outerAxis :=
      houterConvex.ordConnected.out haOuter hbOuter
    refine ⟨a, b, hab, ?_, ?_⟩
    · intro y hy
      exact controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain
        (P.center i)
        ⟨ball_subset_closedBall (hIccOuter hy),
          real_mul_I_mem_complexRightClosedHalfPlane y⟩
    · intro y hyOutside
      by_contra hyCutoff
      apply hyOutside
      have hyInner : y ∈ innerAxis :=
        support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
          P i ⟨hyCutoff,
            real_mul_I_mem_complexRightClosedHalfPlane y⟩
      exact ⟨haInf.trans_le
          ((hinnerCompact.isLeast_sInf hinnerNonempty).2 hyInner),
        ((hinnerCompact.isGreatest_sSup hinnerNonempty).2 hyInner).trans_lt
          hSupB⟩

#print axioms all_zero_or_exists_controlledBoundaryChartAxisInterval

end

end GromovFilling
