import GromovFilling.CompactLipschitzExtension
import GromovFilling.RiemannianControlledBoundaryPartition
import Mathlib.Analysis.Complex.Convex

/-!
# Compact cutoff extensions for controlled boundary charts

A controlled boundary partition is subordinate to half-radius chart
neighborhoods.  In complex half-space coordinates this leaves an annulus
before the full controlled radius.  We use that annulus to extend every
coordinate cutoff to a globally Lipschitz, compactly supported function on
the complex plane while preserving its values on the entire closed right
half-plane.  In particular, the boundary trace on the imaginary axis is
never created by zero-extension across that axis.
-/

open Bundle Function Manifold Metric Set
open scoped Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]

/-- The complex coordinate of a controlled boundary-chart center. -/
def controlledHalfSpaceComplexChartCenter (x : M) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm
    (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x)

/-- The half-radius containing the support of a controlled cutoff. -/
def controlledHalfSpaceInnerRadius (x : M) : ℝ :=
  (chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) x).r / 2

/-- A three-quarter radius used as the outer support of the coordinate bump. -/
def controlledHalfSpaceOuterRadius (x : M) : ℝ :=
  3 * (chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) x).r / 4

theorem controlledHalfSpaceInnerRadius_pos (x : M) :
    0 < controlledHalfSpaceInnerRadius x := by
  unfold controlledHalfSpaceInnerRadius
  exact half_pos
    (chosenInteriorChartControl
      (modelWithCornersEuclideanHalfSpace 2) x).r_pos

theorem controlledHalfSpaceInnerRadius_lt_outer (x : M) :
    controlledHalfSpaceInnerRadius x <
      controlledHalfSpaceOuterRadius x := by
  unfold controlledHalfSpaceInnerRadius controlledHalfSpaceOuterRadius
  nlinarith [(chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) x).r_pos]

theorem controlledHalfSpaceOuterRadius_lt_controlRadius (x : M) :
    controlledHalfSpaceOuterRadius x <
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x).r := by
  unfold controlledHalfSpaceOuterRadius
  nlinarith [(chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) x).r_pos]

/-- The compact convex outer half-ball on which coordinate data are extended. -/
def controlledHalfSpaceOuterClosedHalfBall (x : M) : Set ℂ :=
  closedBall (controlledHalfSpaceComplexChartCenter x)
      (controlledHalfSpaceOuterRadius x) ∩
    complexRightClosedHalfPlane

theorem convex_complexRightClosedHalfPlane :
    Convex ℝ complexRightClosedHalfPlane := by
  simpa only [complexRightClosedHalfPlane] using
    (convex_halfSpace_re_ge (0 : ℝ))

theorem isClosed_complexRightClosedHalfPlane :
    IsClosed complexRightClosedHalfPlane := by
  simpa only [complexRightClosedHalfPlane] using
    isClosed_le
      (continuous_const : Continuous (fun _ : ℂ ↦ (0 : ℝ)))
      Complex.continuous_re

theorem convex_controlledHalfSpaceOuterClosedHalfBall (x : M) :
    Convex ℝ (controlledHalfSpaceOuterClosedHalfBall x) :=
  (convex_closedBall _ _).inter convex_complexRightClosedHalfPlane

theorem isCompact_controlledHalfSpaceOuterClosedHalfBall (x : M) :
    IsCompact (controlledHalfSpaceOuterClosedHalfBall x) :=
  (isCompact_closedBall
    (controlledHalfSpaceComplexChartCenter x)
    (controlledHalfSpaceOuterRadius x)).inter_right
      isClosed_complexRightClosedHalfPlane

/-- The outer closed half-ball still lies strictly inside the full controlled
half-space chart domain. -/
theorem controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain
    (x : M) :
    controlledHalfSpaceOuterClosedHalfBall x ⊆
      chosenControlledHalfSpaceComplexChartDomain x := by
  intro z hz
  rw [chosenControlledHalfSpaceComplexChartDomain,
    controlledHalfSpaceComplexChartDomain,
    controlledHalfSpaceChartSet]
  refine ⟨?_, ?_⟩
  · rw [mem_ball]
    have hdist :
        dist (Complex.orthonormalBasisOneI.repr z)
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) x x) =
          dist z (controlledHalfSpaceComplexChartCenter x) := by
      simpa only [controlledHalfSpaceComplexChartCenter,
        LinearIsometryEquiv.apply_symm_apply] using
        Complex.orthonormalBasisOneI.repr.dist_map z
          (controlledHalfSpaceComplexChartCenter x)
    rw [hdist]
    exact lt_of_le_of_lt hz.1
      (controlledHalfSpaceOuterRadius_lt_controlRadius x)
  · rw [range_modelWithCornersEuclideanHalfSpace]
    simpa only [complexRightClosedHalfPlane,
      Complex.orthonormalBasisOneI_repr_apply] using hz.2

theorem controlledHalfSpaceOuterClosedHalfBall_subset_domain (x : M) :
    controlledHalfSpaceOuterClosedHalfBall x ⊆
      halfSpaceComplexExtChartDomain x :=
  (controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain x).trans
    (controlledHalfSpaceComplexChartDomain_subset_domain
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) x))

/-- A controlled partition cutoff in its half-space coordinates, set to zero
outside the actual extended-chart domain.  The zero branch is used only away
from the coordinate domain; no zero-extension is made across the boundary
axis. -/
def controlledBoundaryChartCutoff
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) : ℂ → ℝ :=
  fun z ↦ if z ∈ halfSpaceComplexExtChartDomain (P.center i) then
    P.partition i (halfSpaceComplexExtChart (P.center i) z) else 0

@[simp] theorem controlledBoundaryChartCutoff_eq_of_mem
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) {z : ℂ}
    (hz : z ∈ halfSpaceComplexExtChartDomain (P.center i)) :
    controlledBoundaryChartCutoff P i z =
      P.partition i (halfSpaceComplexExtChart (P.center i) z) := by
  simp only [controlledBoundaryChartCutoff, hz, if_true]

@[simp] theorem controlledBoundaryChartCutoff_eq_zero_of_not_mem
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) {z : ℂ}
    (hz : z ∉ halfSpaceComplexExtChartDomain (P.center i)) :
    controlledBoundaryChartCutoff P i z = 0 := by
  simp only [controlledBoundaryChartCutoff, hz, if_false]

theorem controlledBoundaryChartCutoff_nonneg
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (z : ℂ) :
    0 ≤ controlledBoundaryChartCutoff P i z := by
  by_cases hz : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · rw [controlledBoundaryChartCutoff_eq_of_mem P i hz]
    exact P.partition_nonneg i _
  · rw [controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hz]

theorem controlledBoundaryChartCutoff_le_one
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (z : ℂ) :
    controlledBoundaryChartCutoff P i z ≤ 1 := by
  by_cases hz : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · rw [controlledBoundaryChartCutoff_eq_of_mem P i hz]
    exact P.partition.le_one i _
  · rw [controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hz]
    exact zero_le_one

/-- In the closed right half-plane, the coordinate cutoff support lies in
the half-radius closed ball. -/
theorem support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    support (controlledBoundaryChartCutoff P i) ∩
        complexRightClosedHalfPlane ⊆
      closedBall (controlledHalfSpaceComplexChartCenter (P.center i))
        (controlledHalfSpaceInnerRadius (P.center i)) := by
  rintro z ⟨hzSupport, _hzRight⟩
  by_cases hzDomain :
      z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · have hpartition :
        P.partition i (halfSpaceComplexExtChart (P.center i) z) ≠ 0 := by
      simpa only [mem_support,
        controlledBoundaryChartCutoff_eq_of_mem P i hzDomain] using hzSupport
    have hshrink := P.tsupport_partition_subset_shrunk i
      (subset_tsupport (P.partition i) hpartition)
    have hcoord :
        extChartAt (modelWithCornersEuclideanHalfSpace 2) (P.center i)
            (halfSpaceComplexExtChart (P.center i) z) =
          Complex.orthonormalBasisOneI.repr z := by
      simpa only [halfSpaceComplexExtChart, Function.comp_apply] using
        (extChartAt (modelWithCornersEuclideanHalfSpace 2)
          (P.center i)).apply_symm_apply hzDomain
    have hdist :
        dist (Complex.orthonormalBasisOneI.repr z)
            (extChartAt (modelWithCornersEuclideanHalfSpace 2)
              (P.center i) (P.center i)) <
          controlledHalfSpaceInnerRadius (P.center i) := by
      have hball := hshrink.2
      change extChartAt (modelWithCornersEuclideanHalfSpace 2) (P.center i)
          (halfSpaceComplexExtChart (P.center i) z) ∈
        ball
          (extChartAt (modelWithCornersEuclideanHalfSpace 2)
            (P.center i) (P.center i))
          (controlledHalfSpaceInnerRadius (P.center i)) at hball
      simpa only [mem_ball, hcoord] using hball
    rw [mem_closedBall]
    have hmap :
        dist (Complex.orthonormalBasisOneI.repr z)
            (extChartAt (modelWithCornersEuclideanHalfSpace 2)
              (P.center i) (P.center i)) =
          dist z (controlledHalfSpaceComplexChartCenter (P.center i)) := by
      simpa only [controlledHalfSpaceComplexChartCenter,
        LinearIsometryEquiv.apply_symm_apply] using
        Complex.orthonormalBasisOneI.repr.dist_map z
          (controlledHalfSpaceComplexChartCenter (P.center i))
    rw [← hmap]
    exact hdist.le
  · exact False.elim (hzSupport
      (controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hzDomain))

/-- The coordinate cutoff is `C¹` on the compact outer half-ball. -/
theorem contDiffOn_controlledBoundaryChartCutoff_outerClosedHalfBall
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    ContDiffOn ℝ 1 (controlledBoundaryChartCutoff P i)
      (controlledHalfSpaceOuterClosedHalfBall (P.center i)) := by
  have hchart : ContMDiffOn 𝓘(ℝ, ℂ)
      (modelWithCornersEuclideanHalfSpace 2) 1
      (halfSpaceComplexExtChart (P.center i))
      (controlledHalfSpaceOuterClosedHalfBall (P.center i)) :=
    (contMDiffOn_halfSpaceComplexExtChart (P.center i)).mono
      (controlledHalfSpaceOuterClosedHalfBall_subset_domain (P.center i))
  have hpartition : ContMDiff
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ) 1 (P.partition i) :=
    (P.contMDiff_partition i).of_le (by simp)
  have hcomp : ContDiffOn ℝ 1
      (P.partition i ∘ halfSpaceComplexExtChart (P.center i))
      (controlledHalfSpaceOuterClosedHalfBall (P.center i)) :=
    (hpartition.comp_contMDiffOn hchart).contDiffOn
  apply hcomp.congr
  intro z hz
  rw [controlledBoundaryChartCutoff_eq_of_mem P i
    (controlledHalfSpaceOuterClosedHalfBall_subset_domain
      (P.center i) hz)]
  rfl

/-- Every controlled boundary cutoff has a global Lipschitz compactly
supported extension which agrees with it on the entire closed right
half-plane and remains `[0, 1]`-valued. -/
theorem exists_controlledBoundaryChartCutoffExtension
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) :
    ∃ C : ℝ≥0, ∃ ρ : ℂ → ℝ,
      LipschitzWith C ρ ∧ HasCompactSupport ρ ∧
        EqOn ρ (controlledBoundaryChartCutoff P i)
          complexRightClosedHalfPlane ∧
        (∀ z, 0 ≤ ρ z) ∧ ∀ z, ρ z ≤ 1 := by
  obtain ⟨K, hK⟩ :=
    (contDiffOn_controlledBoundaryChartCutoff_outerClosedHalfBall P i).
      exists_lipschitzOnWith one_ne_zero
        (convex_controlledHalfSpaceOuterClosedHalfBall (P.center i))
        (isCompact_controlledHalfSpaceOuterClosedHalfBall (P.center i))
  exact exists_lipschitzWith_hasCompactSupport_extension_Icc_of_support_subset
    (controlledHalfSpaceInnerRadius_pos (P.center i))
    (controlledHalfSpaceInnerRadius_lt_outer (P.center i)) hK
    (support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset P i)
    (fun z _hz ↦ controlledBoundaryChartCutoff_nonneg P i z)
    (fun z _hz ↦ controlledBoundaryChartCutoff_le_one P i z)

#print axioms controlledHalfSpaceOuterClosedHalfBall_subset_controlledDomain
#print axioms
  support_controlledBoundaryChartCutoff_inter_rightClosedHalfPlane_subset
#print axioms contDiffOn_controlledBoundaryChartCutoff_outerClosedHalfBall
#print axioms exists_controlledBoundaryChartCutoffExtension

end

end GromovFilling
