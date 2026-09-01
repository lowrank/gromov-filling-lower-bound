import GromovFilling.RiemannianBoundaryOrientationLocalInterval
import GromovFilling.RiemannianControlledBoundaryDirectionParity
import GromovFilling.RiemannianControlledBoundaryTransitionCenterDirection

/-!
# Compatibility of controlled boundary-direction labels on overlaps

For two active charts, possibly chosen from different finite controlled
boundary partitions, this file compares their chosen real boundary lifts at
an overlap point.  Canonical center parameters provide the concrete
chart-transition overlap, continuity shrinks it to the two selected lift
intervals, and conventional chart-sign parity determines whether the
transition preserves or reverses direction.
-/

open Bundle Function Manifold Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance riemannianControlledBoundaryDirectionOverlapEuclideanFinrankTwo :
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

/-- The outward-first direction labels of two active controlled charts agree
at every overlap point, even when the charts use different finite
partitions. -/
theorem ControlledBoundaryActiveAxisLift.outwardBit_eq_of_activeOverlap
    (O : RiemannianSurfaceOrientation
      (modelWithCornersEuclideanHalfSpace 2) M)
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P₁ P₂ : FiniteControlledBoundaryChartPartition M)
    (i : P₁.activeAxisCharts) (j : P₂.activeAxisCharts)
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    (q : UnitAddCircle)
    (hqi : q ∈ controlledBoundaryChartActiveSet boundary P₁ i.1)
    (hqj : q ∈ controlledBoundaryChartActiveSet boundary P₂ j.1) :
    L1.outwardBit (O.controlledChartSign (P₁.center i.1)) =
      L2.outwardBit (O.controlledChartSign (P₂.center j.1)) := by
  obtain ⟨u, hu, huParameter, huCutoff⟩ :=
    exists_axisCoordinate_of_mem_controlledBoundaryChartActiveSet
      boundary hboundary hboundaryRange P₁ i.1 q hqi
  obtain ⟨v, hv, hvParameter, hvCutoff⟩ :=
    exists_axisCoordinate_of_mem_controlledBoundaryChartActiveSet
      boundary hboundary hboundaryRange P₂ j.1 q hqj
  have hparameter :
      controlledBoundaryCenterParameter boundary (P₁.center i.1) u =
        controlledBoundaryCenterParameter boundary (P₂.center j.1) v := by
    calc
      controlledBoundaryCenterParameter boundary (P₁.center i.1) u =
          controlledBoundaryChartParameter boundary P₁ i.1 u := rfl
      _ = q := huParameter
      _ = controlledBoundaryChartParameter boundary P₂ j.1 v := hvParameter.symm
      _ = controlledBoundaryCenterParameter boundary (P₂.center j.1) v := rfl
  have huIoo : u ∈ Set.Ioo L1.a L1.b := by
    by_contra huNot
    exact huCutoff (L1.houtside u huNot)
  have hvIoo : v ∈ Set.Ioo L2.a L2.b := by
    by_contra hvNot
    exact hvCutoff (L2.houtside v hvNot)
  obtain ⟨rDom, hrDom, hDom⟩ :=
    exists_commonControlledAxisInterval_with_centerParameter_eq
      boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
      hu hv hparameter
  obtain ⟨rSource, hrSource, hSource⟩ :=
    exists_centeredIcc_subset_Icc_of_mem_Ioo huIoo
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let z : EuclideanSpace ℝ (Fin 2) :=
    Complex.orthonormalBasisOneI.repr (u * Complex.I)
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I (P₂.center j.1) ∘ (extChartAt I (P₁.center i.1)).symm
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  let phi : PartialEquiv (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) :=
    (extChartAt I (P₁.center i.1)).symm ≫ extChartAt I (P₂.center j.1)
  let s : Set (EuclideanSpace ℝ (Fin 2)) := phi.source
  let J : Set ℝ := Set.Icc (-rDom) rDom
  let eta : ℝ → EuclideanSpace ℝ (Fin 2) := fun t ↦ z + t • e1
  let tau : ℝ → ℝ := fun t ↦ (T (eta t)) 1
  have hDom' : ∀ t ∈ J,
      eta t ∈ s ∧
      eta t ∈ controlledHalfSpaceChartSet
        (chosenInteriorChartControl I (P₁.center i.1)) ∧
      T (eta t) ∈ controlledHalfSpaceChartSet
        (chosenInteriorChartControl I (P₂.center j.1)) ∧
      (T (eta t)) 0 = 0 ∧
      controlledBoundaryCenterParameter boundary (P₁.center i.1)
        ((eta t) 1) =
        controlledBoundaryCenterParameter boundary (P₂.center j.1)
          ((T (eta t)) 1) := by
    simpa only [I, z, T, e1, phi, s, J, eta, Function.comp_apply] using hDom
  obtain ⟨hzSource, hzApply⟩ :=
    centerParameter_eq_transition_source_and_apply
      boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
      hu hv hparameter
  have hTauZero : tau 0 = v := by
    have hApply : T z = Complex.orthonormalBasisOneI.repr (v * Complex.I) := by
      simpa only [I, z, T, Function.comp_apply] using hzApply
    change (T (z + 0 • e1)) 1 = v
    rw [zero_smul, add_zero, hApply]
    simp [Complex.orthonormalBasisOneI_repr_apply]
  have hTContinuous : ContinuousOn T s := by
    simpa only [I, T, s, phi, Function.comp_def] using
      (contDiffOn_ext_coord_change (n := 1)
        (P₂.center j.1) (P₁.center i.1)).continuousOn
  have hEtaContinuous : Continuous eta := by
    simpa only [eta] using
      continuous_const.add (continuous_id.smul continuous_const)
  have hEtaMaps : Set.MapsTo eta J s := by
    intro t ht
    exact (hDom' t ht).1
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hTauContinuous : ContinuousOn tau J := by
    simpa only [tau, p, Function.comp_def] using
      p.continuous.comp_continuousOn
        (hTContinuous.comp hEtaContinuous.continuousOn hEtaMaps)
  have hZeroJ : (0 : ℝ) ∈ J := by
    dsimp only [J]
    constructor <;> linarith
  have hTauContinuousAt : ContinuousAt tau 0 :=
    (hTauContinuous 0 hZeroJ).continuousAt
      (by
        dsimp only [J]
        exact Icc_mem_nhds (by linarith) (by linarith))
  have hTauImage : tau 0 ∈ Set.Ioo L2.a L2.b := by
    simpa only [hTauZero] using hvIoo
  obtain ⟨rTarget, hrTarget, hTarget⟩ :=
    GromovFilling.ContinuousAt.exists_centeredIcc_mapsTo_Icc
      hTauContinuousAt hTauImage
  have hTarget' : Set.MapsTo tau
      (Set.Icc (-rTarget) rTarget) (Set.Icc L2.a L2.b) := by
    simpa only [zero_add] using hTarget
  have centeredIcc_subset {r s : ℝ} (hrs : r ≤ s) :
      Set.Icc (-r) r ⊆ Set.Icc (-s) s := by
    intro t ht
    exact ⟨(neg_le_neg hrs).trans ht.1, ht.2.trans hrs⟩
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
        L1.project_lift (u + t) (hSource t (hSourceSub ht))
      _ = controlledBoundaryCenterParameter boundary (P₁.center i.1) (u + t) := rfl
      _ = controlledBoundaryCenterParameter boundary (P₂.center j.1) (tau t) := by
        simpa [tau, eta, z, T, e1,
          Complex.orthonormalBasisOneI_repr_apply,
          PiLp.add_apply, PiLp.smul_apply, Function.comp_apply] using hCenter
      _ = controlledBoundaryChartParameter boundary P₂ j.1 (tau t) := rfl
      _ = ((L2.lift (tau t) : ℝ) : UnitAddCircle) :=
        (L2.project_lift (tau t) (hTarget' (hTargetSub ht))).symm
  rcases O.controlledChartSign_eq_one_or_neg_one (P₁.center i.1) with hi | hi <;>
    rcases O.controlledChartSign_eq_one_or_neg_one (P₂.center j.1) with hj | hj
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
        hu hv hparameter (by rw [hi, hj])
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictMonoOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.monoBit = L2.monoBit :=
      L1.monoBit_eq_of_local_transition_mono L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.outwardBit_eq_of_chartSign_eq_of_monoBit_eq L2
      (by rw [hi, hj]) hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
        hu hv hparameter (by rw [hi, hj]; norm_num)
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictAntiOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.monoBit = Bool.not L2.monoBit :=
      L1.monoBit_eq_not_of_local_transition_anti L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.outwardBit_eq_of_chartSigns_one_neg_one L2 hi hj hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictAntiOn_of_centerParameter_eq_of_controlledChartSign_eq_neg
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
        hu hv hparameter (by rw [hi, hj])
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictAntiOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.monoBit = Bool.not L2.monoBit :=
      L1.monoBit_eq_not_of_local_transition_anti L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.outwardBit_eq_of_chartSigns_neg_one_one L2 hi hj hBit
  · obtain ⟨rOrientation, hrOrientation, hOrientation⟩ :=
      exists_axis_interval_strictMonoOn_of_centerParameter_eq_of_controlledChartSign_eq
        O boundary hboundaryRange (P₁.center i.1) (P₂.center j.1) u v
        hu hv hparameter (by rw [hi, hj])
    obtain ⟨r, hr, hDomSub, hSourceSub, hTargetSub, hOrientationSub⟩ :=
      shrink rOrientation hrOrientation
    have hOrientation' : StrictMonoOn tau
        (Set.Icc (-rOrientation) rOrientation) := by
      simpa only [tau, eta, z, T, e1, I, Function.comp_apply] using hOrientation
    have hBit : L1.monoBit = L2.monoBit :=
      L1.monoBit_eq_of_local_transition_mono L2 hr
        (fun t ht ↦ hSource t (hSourceSub ht))
        (hTauContinuous.mono hDomSub)
        (fun t ht ↦ hTarget' (hTargetSub ht))
        (hProjectOf r hDomSub hSourceSub hTargetSub)
        (hOrientation'.mono hOrientationSub)
    exact L1.outwardBit_eq_of_chartSign_eq_of_monoBit_eq L2
      (by rw [hi, hj]) hBit

#print axioms ControlledBoundaryActiveAxisLift.outwardBit_eq_of_activeOverlap

end

end GromovFilling
