import GromovFilling.RiemannianBoundaryOrientationDirectionTransport
import GromovFilling.RiemannianControlledBoundaryDirectionBit

/-!
# Parity of controlled boundary-lift directions

This file is the one-dimensional Boolean layer of the conventional
orientation bridge.  A locally increasing chart transition preserves a
lift's stored direction bit; a locally decreasing transition flips it.  The
outward-first bit combines that direction with the conventional chart sign.
No manifold-chart bookkeeping is performed here.
-/

open Set

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

/-- The Boolean direction required by the outward-first convention: a
positive chart needs a decreasing lift, while a negative chart needs an
increasing lift. -/
def ControlledBoundaryActiveAxisLift.outwardBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i)
    (chartSign : ℝ) : Bool :=
  Bool.xor (if chartSign = 1 then true else false) L.monoBit

/-- A locally strictly increasing transition preserves the stored direction
bit of two projected controlled boundary lifts, including lifts chosen from
different finite partitions. -/
theorem ControlledBoundaryActiveAxisLift.monoBit_eq_of_local_transition_mono
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.activeAxisCharts} {j : P₂.activeAxisCharts}
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    {u r : ℝ} (hr : 0 < r)
    (hsource : ∀ t ∈ Set.Icc (-r) r, u + t ∈ Set.Icc L1.a L1.b)
    {transition : ℝ → ℝ}
    (htransitionContinuous : ContinuousOn transition (Set.Icc (-r) r))
    (htransitionMaps : Set.MapsTo transition (Set.Icc (-r) r)
      (Set.Icc L2.a L2.b))
    (hproject : ∀ t ∈ Set.Icc (-r) r,
      ((L1.lift (u + t) : ℝ) : UnitAddCircle) =
        ((L2.lift (transition t) : ℝ) : UnitAddCircle))
    (htransition : StrictMonoOn transition (Set.Icc (-r) r)) :
    L1.monoBit = L2.monoBit := by
  have htranslate : Continuous (fun t : ℝ ↦ u + t) :=
    continuous_const.add continuous_id
  have hshiftContinuous : Continuous (fun t : ℝ ↦ L1.lift (u + t)) :=
    L1.continuous_lift.comp htranslate
  rcases hdirection : L2.direction with hL2 | hL2
  · have hlocal : StrictMonoOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictMonoOn_of_projected_real_lifts_comp_strictMonoOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition
        hL2
    have hL1bit : L1.monoBit = true :=
      L1.monoBit_eq_true_of_strictMonoOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = true := by
      simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]
    exact hL1bit.trans hL2bit.symm
  · have hlocal : StrictAntiOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictAntiOn_of_projected_real_lifts_comp_strictMonoOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition
        hL2
    have hL1bit : L1.monoBit = false :=
      L1.monoBit_eq_false_of_strictAntiOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = false := by
      simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]
    exact hL1bit.trans hL2bit.symm

/-- A locally strictly decreasing transition flips the stored direction bit
of two projected controlled boundary lifts, including lifts chosen from
different finite partitions. -/
theorem ControlledBoundaryActiveAxisLift.monoBit_eq_not_of_local_transition_anti
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.activeAxisCharts} {j : P₂.activeAxisCharts}
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    {u r : ℝ} (hr : 0 < r)
    (hsource : ∀ t ∈ Set.Icc (-r) r, u + t ∈ Set.Icc L1.a L1.b)
    {transition : ℝ → ℝ}
    (htransitionContinuous : ContinuousOn transition (Set.Icc (-r) r))
    (htransitionMaps : Set.MapsTo transition (Set.Icc (-r) r)
      (Set.Icc L2.a L2.b))
    (hproject : ∀ t ∈ Set.Icc (-r) r,
      ((L1.lift (u + t) : ℝ) : UnitAddCircle) =
        ((L2.lift (transition t) : ℝ) : UnitAddCircle))
    (htransition : StrictAntiOn transition (Set.Icc (-r) r)) :
    L1.monoBit = Bool.not L2.monoBit := by
  have htranslate : Continuous (fun t : ℝ ↦ u + t) :=
    continuous_const.add continuous_id
  have hshiftContinuous : Continuous (fun t : ℝ ↦ L1.lift (u + t)) :=
    L1.continuous_lift.comp htranslate
  rcases hdirection : L2.direction with hL2 | hL2
  · have hlocal : StrictAntiOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictAntiOn_of_projected_real_lifts_comp_strictAntiOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition
        hL2
    have hL1bit : L1.monoBit = false :=
      L1.monoBit_eq_false_of_strictAntiOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = true := by
      simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]
    simp [hL1bit, hL2bit]
  · have hlocal : StrictMonoOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictMonoOn_of_projected_real_lifts_comp_strictAntiOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition
        hL2
    have hL1bit : L1.monoBit = true :=
      L1.monoBit_eq_true_of_strictMonoOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = false := by
      simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]
    simp [hL1bit, hL2bit]

/-- Equal chart signs and equal local direction bits give the same
outward-first Boolean label. -/
theorem ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.activeAxisCharts} {j : P₂.activeAxisCharts}
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign : sign1 = sign2) (hbit : L1.monoBit = L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  simp [ControlledBoundaryActiveAxisLift.outwardBit, hsign, hbit]

/-- Opposite chart signs with signs `+1` and `-1` cancel a flipped local
direction bit in the outward-first label. -/
theorem ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSigns_one_neg_one
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.activeAxisCharts} {j : P₂.activeAxisCharts}
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign1 : sign1 = 1) (hsign2 : sign2 = -1)
    (hbit : L1.monoBit = Bool.not L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  simp [ControlledBoundaryActiveAxisLift.outwardBit, hsign1, hsign2, hbit, hneg]

/-- Opposite chart signs with signs `-1` and `+1` cancel a flipped local
direction bit in the outward-first label. -/
theorem ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSigns_neg_one_one
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.activeAxisCharts} {j : P₂.activeAxisCharts}
    (L1 : ControlledBoundaryActiveAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryActiveAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign1 : sign1 = -1) (hsign2 : sign2 = 1)
    (hbit : L1.monoBit = Bool.not L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  simp [ControlledBoundaryActiveAxisLift.outwardBit, hsign1, hsign2, hbit, hneg]

#print axioms ControlledBoundaryActiveAxisLift.outwardBit
#print axioms ControlledBoundaryActiveAxisLift.monoBit_eq_of_local_transition_mono
#print axioms ControlledBoundaryActiveAxisLift.monoBit_eq_not_of_local_transition_anti
#print axioms
  ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq
#print axioms
  ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSigns_one_neg_one
#print axioms
  ControlledBoundaryActiveAxisLift.outwardBit_eq_of_chartSigns_neg_one_one

end

end GromovFilling
