import GromovFilling.RiemannianHalfSpaceChartTransitionAxisMonotone
import GromovFilling.RiemannianHalfSpaceChartTransitionDeterminant
import GromovFilling.RiemannianSurfaceOrientationTransitionParity

/-!
# Direction of oriented controlled-boundary chart transitions

At a boundary-axis overlap, the sign of a conventional surface orientation
determines the direction of the tangential coordinate transition. Equal
controlled chart signs give a locally increasing transition; opposite signs
give a locally decreasing one.

This is the local geometric input used to compare normalized directions of
real boundary-parameter lifts on overlapping controlled charts.
-/

open Bundle Manifold Set
open scoped Bundle Manifold

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianControlledBoundaryTransitionDirectionEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Equal conventional controlled-chart signs make the tangential transition
strictly increasing on some axis interval around the overlap point. -/
theorem exists_axis_interval_strictMonoOn_of_controlledChartSign_eq
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (hAImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart a ''
        chosenControlledHalfSpaceComplexChartDomain a)
    (hBImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart b ''
        chosenControlledHalfSpaceComplexChartDomain b)
    (hsign : O.controlledChartSign a = O.controlledChartSign b) :
    ∃ r : ℝ, 0 < r ∧ StrictMonoOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  have hdet := O.controlledChartSign_eq_transition_det_pos
    a b hz hAImage hBImage hsign
  have htangent :
      0 < (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1 :=
    (fderivWithin_extChartAt_axis_transition_det_pos_iff_tangent_pos
      a b hz hzAxis).mp hdet
  exact exists_axis_interval_strictMonoOn_of_tangent_pos
    a b hz hzAxis htangent

/-- Opposite conventional controlled-chart signs make the tangential
transition strictly decreasing on some axis interval around the overlap
point. -/
theorem exists_axis_interval_strictAntiOn_of_controlledChartSign_eq_neg
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (hAImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart a ''
        chosenControlledHalfSpaceComplexChartDomain a)
    (hBImage : (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm z ∈
      halfSpaceComplexExtChart b ''
        chosenControlledHalfSpaceComplexChartDomain b)
    (hsign : O.controlledChartSign a = -O.controlledChartSign b) :
    ∃ r : ℝ, 0 < r ∧ StrictAntiOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  have hdet := O.controlledChartSign_eq_neg_transition_det_neg
    a b hz hAImage hBImage hsign
  have htangent :
      (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1 < 0 :=
    (fderivWithin_extChartAt_axis_transition_det_neg_iff_tangent_neg
      a b hz hzAxis).mp hdet
  exact exists_axis_interval_strictAntiOn_of_tangent_neg
    a b hz hzAxis htangent

#print axioms exists_axis_interval_strictMonoOn_of_controlledChartSign_eq
#print axioms exists_axis_interval_strictAntiOn_of_controlledChartSign_eq_neg

end

end GromovFilling
