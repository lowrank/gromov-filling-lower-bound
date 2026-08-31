import GromovFilling.RiemannianControlledBoundaryAxisLiftInterface
import GromovFilling.RiemannianControlledBoundaryDirectionOverlap

/-!
# Comparing an arbitrary boundary lift with an active reference lift

The active-chart cover supplies the globally glued direction bit.  This file
compares that bit with a lift from any controlled chart, without assuming that
the target chart's cutoff is active in its own finite partition.  It is the
local geometric bridge from the cover construction to the all-chart
induced-boundary-orientation contract.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianControlledBoundaryAxisLiftOverlapEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- An active reference lift has the same outward-first bit as an arbitrary
controlled target lift at a common boundary point. -/
theorem ControlledBoundaryActiveAxisLift.toAxisLift_outwardBit_eq_of_axisLiftOverlap
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P₁ : FiniteControlledBoundaryChartPartition M)
    (i : P₁.activeAxisCharts)
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (P₂ : FiniteControlledBoundaryChartPartition M) (j : P₂.ι)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
    (q : UnitAddCircle)
    (hqi : q ∈ controlledBoundaryChartActiveSet boundary P₁ i.1)
    (v : ℝ) (hv : v ∈ Set.Ioo L2.a L2.b)
    (hvParameter : controlledBoundaryChartParameter boundary P₂ j v = q) :
    L1.toAxisLift.outwardBit (O.controlledChartSign (P₁.center i.1)) =
      L2.outwardBit (O.controlledChartSign (P₂.center j)) := by
  obtain ⟨u, hu, huParameter, huCutoff⟩ :=
    exists_axisCoordinate_of_mem_controlledBoundaryChartActiveSet
      boundary hboundary hboundaryRange P₁ i.1 q hqi
  have hparameter :
      controlledBoundaryCenterParameter boundary (P₁.center i.1) u =
        controlledBoundaryCenterParameter boundary (P₂.center j) v := by
    calc
      controlledBoundaryCenterParameter boundary (P₁.center i.1) u =
          controlledBoundaryChartParameter boundary P₁ i.1 u := rfl
      _ = q := huParameter
      _ = controlledBoundaryChartParameter boundary P₂ j v := hvParameter.symm
      _ = controlledBoundaryCenterParameter boundary (P₂.center j) v := rfl
  have huIoo : u ∈ Set.Ioo L1.a L1.b := by
    by_contra huNot
    exact huCutoff (L1.houtside u huNot)
  have hvIcc : v ∈ Set.Icc L2.a L2.b := ⟨hv.1.le, hv.2.le⟩
  obtain ⟨rDom, hrDom, hDom⟩ :=
    exists_commonControlledAxisInterval_with_centerParameter_eq
      boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
      hu (L2.hdomain v hvIcc) hparameter
  obtain ⟨rSource, hrSource, hSource⟩ :=
    exists_centeredIcc_subset_Icc_of_mem_Ioo huIoo
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let z : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (u * Complex.I)
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I (P₂.center j) ∘ (extChartAt I (P₁.center i.1)).symm
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  let phi : PartialEquiv (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) :=
    (extChartAt I (P₁.center i.1)).symm ≫ extChartAt I (P₂.center j)
  let s : Set (EuclideanSpace ℝ (Fin 2)) := phi.source
  let J : Set ℝ := Set.Icc (-rDom) rDom
  let eta : ℝ → EuclideanSpace ℝ (Fin 2) := fun t ↦ z + t • e1
  let tau : ℝ → ℝ := fun t ↦ (T (eta t)) 1
  have hDom' : ∀ t ∈ J,
      eta t ∈ s ∧
      eta t ∈ controlledHalfSpaceChartSet
        (chosenInteriorChartControl I (P₁.center i.1)) ∧
      T (eta t) ∈ controlledHalfSpaceChartSet
        (chosenInteriorChartControl I (P₂.center j)) ∧
      (T (eta t)) 0 = 0 ∧
      controlledBoundaryCenterParameter boundary (P₁.center i.1)
        ((eta t) 1) =
        controlledBoundaryCenterParameter boundary (P₂.center j)
          ((T (eta t)) 1) := by
    simpa only [I, z, T, e1, phi, s, J, eta, Function.comp_apply] using hDom
  obtain ⟨hzSource, hzApply⟩ :=
    centerParameter_eq_transition_source_and_apply
      boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
      hu (L2.hdomain v hvIcc) hparameter
  have hTauZero : tau 0 = v := by
    have hApply : T z = Complex.orthonormalBasisOneI.repr (v * Complex.I) := by
      simpa only [I, z, T, Function.comp_apply] using hzApply
    change (T (z + 0 • e1)) 1 = v
    rw [zero_smul, add_zero, hApply]
    simp [Complex.orthonormalBasisOneI_repr_apply]
  have hTContinuous : ContinuousOn T s := by
    simpa only [I, T, s, phi, Function.comp_def] using
      (contDiffOn_ext_coord_change (P₂.center j) (P₁.center i.1)).continuousOn
  have hEtaContinuous : Continuous eta := by
    simpa only [eta] using
      continuous_const.add (continuous_id.smul continuous_const)
  have hEtaMaps : Set.MapsTo eta J s := by
    intro t ht
    exact (hDom' t ht).1
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hTauContinuous : ContinuousOn tau J := by
    simpa only [tau, p, Function.comp_def] using
      p.continuous.continuousOn.comp
        (hTContinuous.comp hEtaContinuous.continuousOn hEtaMaps)
        (by
          intro t ht
          simp)
  have hZeroJ : (0 : ℝ) ∈ J := by
    dsimp only [J]
    constructor <;> linarith
  have hTauContinuousAt : ContinuousAt tau 0 :=
    (hTauContinuous 0 hZeroJ).continuousAt
      (by
        dsimp only [J]
        exact Icc_mem_nhds (by linarith) (by linarith))
  have hTauImage : tau 0 ∈ Set.Ioo L2.a L2.b := by
    simpa only [hTauZero] using hv
  obtain ⟨rTarget, hrTarget, hTarget⟩ :=
    hTauContinuousAt.exists_centeredIcc_mapsTo_Icc hTauImage
  have hTarget' : Set.MapsTo tau
      (Set.Icc (-rTarget) rTarget) (Set.Icc L2.a L2.b) := by
    simpa only [zero_add] using hTarget
  have centeredIcc_subset {r s : ℝ} (hrs : r ≤ s) :
      Set.Icc (-r) r ⊆ Set.Icc (-s) s := by
    intro t ht
    constructor <;> linarith
  have shrink (rOrientation : ℝ) (hrOrientation : 0 < rOrientation) :
      ∃ r : ℝ, 0 < r ∧
        Set.Icc (-r) r ⊆ J ∧
        Set.Icc (-r) r ⊆ Set.Icc (-rSource) rSource ∧
        Set.Icc (-r) r ⊆ Set.Icc (-rTarget) rTarget ∧
        Set.Icc (-r) r ⊆ Set.Icc (-rOrientation) rOrientation := by
    let r : ℝ := min rDom (min rSource (min rTarget rOrientation))
    have hTargetOrientation : 0 < min rTarget rOrientation :=
      lt_min hrTarget hrOrientation
    have hSourceTargetOrientation :
        0 < min rSource (min rTarget rOrientation) :=
      lt_min hrSource hTargetOrientation
    have hr : 0 < r := by
      dsimp only [r]
      exact lt_min hrDom hSourceTargetOrientation
    have hrleDom : r ≤ rDom := by
      dsimp only [r]
      exact min_le_left _ _
    have hrleSource : r ≤ rSource := by
      dsimp only [r]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hrleTarget : r ≤ rTarget := by
      dsimp only [r]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hrleOrientation : r ≤ rOrientation := by
      dsimp only [r]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
    · simpa only [J] using centeredIcc_subset hrleDom
    · exact centeredIcc_subset hrleSource
    · exact centeredIcc_subset hrleTarget
    · exact centeredIcc_subset hrleOrientation
  have hProjectOf : ∀ (r : ℝ)
      (hDomSub : Set.Icc (-r) r ⊆ J)
      (hSourceSub : Set.Icc (-r) r ⊆ Set.Icc (-rSource) rSource)
      (hTargetSub : Set.Icc (-r) r ⊆ Set.Icc (-rTarget) rTarget),
      ∀ t ∈ Set.Icc (-r) r,
        ((L1.lift (u + t) : ℝ) : UnitAddCircle) =
          ((L2.lift (tau t) : ℝ) : UnitAddCircle) := by
    intro r hDomSub hSourceSub hTargetSub t ht
    rcases hDom' t (hDomSub ht) with ⟨_, _, _, _, hCenter⟩
    calc
      ((L1.lift (u + t) : ℝ) : UnitAddCircle) =
          controlledBoundaryChartParameter boundary P₁ i.1 (u + t) :=
        L1.project_lift (hSource t (hSourceSub ht))
      _ = controlledBoundaryCenterParameter boundary (P₁.center i.1) (u + t) := rfl
      _ = controlledBoundaryCenterParameter boundary (P₂.center j) (tau t) := by
        simpa [tau, eta, z, T, e1,
          Complex.orthonormalBasisOneI_repr_apply,
          PiLp.add_apply, PiLp.smul_apply, Function.comp_apply] using hCenter
      _ = controlledBoundaryChartParameter boundary P₂ j (tau t) := rfl
      _ = ((L2.lift (tau t) : ℝ) : UnitAddCircle) :=
        (L2.project_lift (hTarget' t (hTargetSub ht))).symm
  rcases O.controlledChartSign_eq_one_or_neg_one (P₁.center i.1) with hi | hi <;>
    rcases O.controlledChartSign_eq_one_or_neg_one (P₂.center j) with hj | hj
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
        hu (L2.hdomain v hvIcc) hparameter (by rw [hi, hj])
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictMonoOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.toAxisLift.monoBit = L2.monoBit :=
      L1.toAxisLift.monoBit_eq_of_local_transition_mono L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' t (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.toAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq L2
      (by rw [hi, hj]) hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
        hu (L2.hdomain v hvIcc) hparameter (by rw [hi, hj]; norm_num)
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictAntiOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.toAxisLift.monoBit = Bool.not L2.monoBit :=
      L1.toAxisLift.monoBit_eq_not_of_local_transition_anti L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' t (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.toAxisLift.outwardBit_eq_of_chartSigns_one_neg_one L2 hi hj hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
        hu (L2.hdomain v hvIcc) hparameter (by rw [hi, hj]; norm_num)
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictAntiOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.toAxisLift.monoBit = Bool.not L2.monoBit :=
      L1.toAxisLift.monoBit_eq_not_of_local_transition_anti L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' t (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.toAxisLift.outwardBit_eq_of_chartSigns_neg_one_one L2 hi hj hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j) u v
        hu (L2.hdomain v hvIcc) hparameter (by rw [hi, hj])
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictMonoOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.toAxisLift.monoBit = L2.monoBit :=
      L1.toAxisLift.monoBit_eq_of_local_transition_mono L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' t (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.toAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq L2
      (by rw [hi, hj]) hBit

#print axioms
  ControlledBoundaryActiveAxisLift.toAxisLift_outwardBit_eq_of_axisLiftOverlap

end

end GromovFilling
