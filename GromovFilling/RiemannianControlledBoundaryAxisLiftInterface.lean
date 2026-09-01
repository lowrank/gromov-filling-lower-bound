import GromovFilling.RiemannianControlledBoundaryDirectionParity

/-!
# Arbitrary controlled boundary-axis lifts

The active-chart cover used to glue a global boundary direction carries an
extra cutoff-support field.  The induced-boundary-orientation contract,
however, quantifies over every controlled chart and every continuous real
lift, including charts that are inactive in a particular finite partition.
This file packages the common interval-and-lift data without a cutoff and
records the Boolean outward-first convention for such arbitrary lifts.
-/

open Bundle Function Manifold Set
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

/-- A real lift of one controlled boundary-chart parameter on a nontrivial
closed axis interval.  Unlike `ControlledBoundaryActiveAxisLift`, it does
not require the chart cutoff to be active. -/
structure ControlledBoundaryAxisLift
    (boundary : UnitAddCircle → M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) where
  a : ℝ
  b : ℝ
  hab : a < b
  hdomain : ∀ y : ℝ, y ∈ Set.Icc a b → (y * Complex.I : ℂ) ∈
    chosenControlledHalfSpaceComplexChartDomain (P.center i)
  lift : ℝ → ℝ
  continuous_lift : Continuous lift
  project_lift : ∀ y : ℝ, y ∈ Set.Icc a b →
    ((lift y : ℝ) : UnitAddCircle) =
      controlledBoundaryChartParameter boundary P i y
  direction : ControlledBoundaryLiftDirection lift (Set.Icc a b)

/-- Forget the cutoff-support field of an active axis lift. -/
def ControlledBoundaryActiveAxisLift.toAxisLift
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i) :
    ControlledBoundaryAxisLift boundary P i.1 where
  a := L.a
  b := L.b
  hab := L.hab
  hdomain := L.hdomain
  lift := L.lift
  continuous_lift := L.continuous_lift
  project_lift := L.project_lift
  direction := L.direction

/-- Every continuous real lift of a controlled boundary-chart parameter on a
nontrivial domain interval has one strict direction. -/
theorem strictMonoOn_or_strictAntiOn_ofContinuousProjectedLift
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (a b : ℝ) (hab : a < b)
    (hdomain : ∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i))
    (lift : ℝ → ℝ) (hliftContinuous : Continuous lift)
    (hliftProject : ∀ y ∈ Set.Icc a b,
      ((lift y : ℝ) : UnitAddCircle) =
        controlledBoundaryChartParameter boundary P i y) :
    StrictMonoOn lift (Set.Icc a b) ∨ StrictAntiOn lift (Set.Icc a b) := by
  have hparameterInjective : Set.InjOn
      (controlledBoundaryChartParameter boundary P i) (Set.Icc a b) :=
    injOn_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i (Set.Icc a b) hdomain
  have hliftInjective : Set.InjOn lift (Set.Icc a b) := by
    intro y hy z hz hyz
    apply hparameterInjective hy hz
    calc
      controlledBoundaryChartParameter boundary P i y =
          ((lift y : ℝ) : UnitAddCircle) := (hliftProject y hy).symm
      _ = ((lift z : ℝ) : UnitAddCircle) :=
        congrArg (fun r : ℝ ↦ (r : UnitAddCircle)) hyz
      _ = controlledBoundaryChartParameter boundary P i z :=
        hliftProject z hz
  exact hliftContinuous.continuousOn.strictMonoOn_of_injOn_Icc'
    hab.le hliftInjective

/-- Package any continuous real lift of a controlled boundary-chart
parameter on a nontrivial domain interval.  Injectivity of the chart
parameter forces one of the two strict directions, so no cutoff-activity
assumption is needed. -/
noncomputable def ControlledBoundaryAxisLift.ofContinuousProjectedLift
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (a b : ℝ) (hab : a < b)
    (hdomain : ∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i))
    (lift : ℝ → ℝ) (hliftContinuous : Continuous lift)
    (hliftProject : ∀ y ∈ Set.Icc a b,
      ((lift y : ℝ) : UnitAddCircle) =
        controlledBoundaryChartParameter boundary P i y) :
    ControlledBoundaryAxisLift boundary P i := {
  a := a
  b := b
  hab := hab
  hdomain := hdomain
  lift := lift
  continuous_lift := hliftContinuous
  project_lift := hliftProject
  direction := ControlledBoundaryLiftDirection.ofOr
    (strictMonoOn_or_strictAntiOn_ofContinuousProjectedLift
      boundary hboundaryRange P i a b hab hdomain lift hliftContinuous
      hliftProject)
}

/-- Boolean encoding of an arbitrary controlled lift's strict direction. -/
def ControlledBoundaryAxisLift.monoBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) : Bool :=
  L.direction.monoBit

/-- Boolean encoding of the outward-first direction for an arbitrary
controlled axis lift. -/
def ControlledBoundaryAxisLift.outwardBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) (chartSign : ℝ) : Bool :=
  Bool.xor (if chartSign = 1 then true else false) L.monoBit

@[simp] theorem ControlledBoundaryActiveAxisLift.toAxisLift_monoBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i) :
    L.toAxisLift.monoBit = L.monoBit := rfl

@[simp] theorem ControlledBoundaryActiveAxisLift.toAxisLift_outwardBit
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i) (chartSign : ℝ) :
    L.toAxisLift.outwardBit chartSign = L.outwardBit chartSign := rfl

private theorem not_strictAntiOn_of_strictMonoOn
    {a b : ℝ} {lift : ℝ → ℝ} (hab : a < b)
    (hmono : StrictMonoOn lift (Set.Icc a b)) :
    ¬ StrictAntiOn lift (Set.Icc a b) := by
  intro hanti
  have hmonoValue : lift a < lift b :=
    hmono (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab
  have hantiValue : lift b < lift a :=
    hanti (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab
  linarith

private theorem not_strictMonoOn_of_strictAntiOn
    {a b : ℝ} {lift : ℝ → ℝ} (hab : a < b)
    (hanti : StrictAntiOn lift (Set.Icc a b)) :
    ¬ StrictMonoOn lift (Set.Icc a b) := by
  intro hmono
  exact not_strictAntiOn_of_strictMonoOn hab hmono hanti

/-- Reading `true` from an arbitrary lift's direction bit is equivalent to
strict increase on its full interval. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_true_iff
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) :
    L.monoBit = true ↔ StrictMonoOn L.lift (Set.Icc L.a L.b) := by
  rcases hdirection : L.direction with hmono | hanti
  · simp [ControlledBoundaryAxisLift.monoBit, hdirection, hmono]
  · have hnot := not_strictMonoOn_of_strictAntiOn L.hab hanti
    simp [ControlledBoundaryAxisLift.monoBit, hdirection, hnot]

/-- Reading `false` from an arbitrary lift's direction bit is equivalent to
strict decrease on its full interval. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_false_iff
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) :
    L.monoBit = false ↔ StrictAntiOn L.lift (Set.Icc L.a L.b) := by
  rcases hdirection : L.direction with hmono | hanti
  · have hnot := not_strictAntiOn_of_strictMonoOn L.hab hmono
    simp [ControlledBoundaryAxisLift.monoBit, hdirection, hnot]
  · simp [ControlledBoundaryAxisLift.monoBit, hdirection, hanti]

/-- A nontrivial locally increasing translate determines an arbitrary
controlled lift's stored direction bit. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_true_of_strictMonoOn_translate
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i)
    {u r : ℝ} (hr : 0 < r)
    (hsub : ∀ t ∈ Set.Icc (-r) r, u + t ∈ Set.Icc L.a L.b)
    (hmono : StrictMonoOn (fun t : ℝ ↦ L.lift (u + t))
      (Set.Icc (-r) r)) :
    L.monoBit = true := by
  rcases hdirection : L.direction with hL | hL
  · simp [ControlledBoundaryAxisLift.monoBit, hdirection]
  · have hleft : (-r : ℝ) ∈ Set.Icc (-r) r := by
      constructor <;> linarith
    have hright : (r : ℝ) ∈ Set.Icc (-r) r := by
      constructor <;> linarith
    have hlt : (-r : ℝ) < r := by linarith
    have hmonoValue : L.lift (u + (-r)) < L.lift (u + r) :=
      hmono hleft hright hlt
    have hantiValue : L.lift (u + r) < L.lift (u + (-r)) :=
      hL (hsub (-r) hleft) (hsub r hright) (by linarith)
    exfalso
    linarith

/-- A nontrivial locally decreasing translate determines an arbitrary
controlled lift's stored direction bit. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_false_of_strictAntiOn_translate
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i)
    {u r : ℝ} (hr : 0 < r)
    (hsub : ∀ t ∈ Set.Icc (-r) r, u + t ∈ Set.Icc L.a L.b)
    (hanti : StrictAntiOn (fun t : ℝ ↦ L.lift (u + t))
      (Set.Icc (-r) r)) :
    L.monoBit = false := by
  rcases hdirection : L.direction with hL | hL
  · have hleft : (-r : ℝ) ∈ Set.Icc (-r) r := by
      constructor <;> linarith
    have hright : (r : ℝ) ∈ Set.Icc (-r) r := by
      constructor <;> linarith
    have hlt : (-r : ℝ) < r := by linarith
    have hmonoValue : L.lift (u + (-r)) < L.lift (u + r) :=
      hL (hsub (-r) hleft) (hsub r hright) (by linarith)
    have hantiValue : L.lift (u + r) < L.lift (u + (-r)) :=
      hanti hleft hright hlt
    exfalso
    linarith
  · simp [ControlledBoundaryAxisLift.monoBit, hdirection]

/-- `true` is exactly the outward-first direction: decrease in a positive
chart and increase in a negative chart. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_true_iff
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) (chartSign : ℝ)
    (hsign : chartSign = 1 ∨ chartSign = -1) :
    L.outwardBit chartSign = true ↔
      (chartSign = 1 ∧ StrictAntiOn L.lift (Set.Icc L.a L.b)) ∨
        (chartSign = -1 ∧ StrictMonoOn L.lift (Set.Icc L.a L.b)) := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  have hone_neg : (1 : ℝ) ≠ -1 := Ne.symm hneg
  rcases hsign with hsign | hsign
  · rcases hdirection : L.direction with hmono | hanti
    · have hnot := not_strictAntiOn_of_strictMonoOn L.hab hmono
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hmono, hnot, hone_neg]
    · have hnot := not_strictMonoOn_of_strictAntiOn L.hab hanti
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hanti, hnot, hneg]
  · rcases hdirection : L.direction with hmono | hanti
    · have hnot := not_strictAntiOn_of_strictMonoOn L.hab hmono
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hmono, hnot, hneg]
    · have hnot := not_strictMonoOn_of_strictAntiOn L.hab hanti
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hanti, hnot, hneg]

/-- `false` is exactly the reverse of the outward-first direction. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_false_iff
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    (L : ControlledBoundaryAxisLift boundary P i) (chartSign : ℝ)
    (hsign : chartSign = 1 ∨ chartSign = -1) :
    L.outwardBit chartSign = false ↔
      (chartSign = 1 ∧ StrictMonoOn L.lift (Set.Icc L.a L.b)) ∨
        (chartSign = -1 ∧ StrictAntiOn L.lift (Set.Icc L.a L.b)) := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  have hone_neg : (1 : ℝ) ≠ -1 := Ne.symm hneg
  rcases hsign with hsign | hsign
  · rcases hdirection : L.direction with hmono | hanti
    · have hnot := not_strictAntiOn_of_strictMonoOn L.hab hmono
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hmono, hnot, hneg]
    · have hnot := not_strictMonoOn_of_strictAntiOn L.hab hanti
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hanti, hnot, hone_neg]
  · rcases hdirection : L.direction with hmono | hanti
    · have hnot := not_strictAntiOn_of_strictMonoOn L.hab hmono
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hmono, hnot, hneg]
    · have hnot := not_strictMonoOn_of_strictAntiOn L.hab hanti
      simp [ControlledBoundaryAxisLift.outwardBit,
        ControlledBoundaryAxisLift.monoBit, hsign, hdirection, hanti, hnot, hneg]

/-- A locally strictly increasing coordinate transition preserves the
direction bit of two arbitrary projected controlled boundary lifts. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_of_local_transition_mono
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.ι} {j : P₂.ι}
    (L1 : ControlledBoundaryAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
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
        htransitionContinuous htransitionMaps hproject htransition hL2
    have hL1bit : L1.monoBit = true :=
      L1.monoBit_eq_true_of_strictMonoOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = true := by
      simp [ControlledBoundaryAxisLift.monoBit, hdirection]
    exact hL1bit.trans hL2bit.symm
  · have hlocal : StrictAntiOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictAntiOn_of_projected_real_lifts_comp_strictMonoOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition hL2
    have hL1bit : L1.monoBit = false :=
      L1.monoBit_eq_false_of_strictAntiOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = false := by
      simp [ControlledBoundaryAxisLift.monoBit, hdirection]
    exact hL1bit.trans hL2bit.symm

/-- A locally strictly decreasing coordinate transition flips the direction
bit of two arbitrary projected controlled boundary lifts. -/
theorem ControlledBoundaryAxisLift.monoBit_eq_not_of_local_transition_anti
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.ι} {j : P₂.ι}
    (L1 : ControlledBoundaryAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
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
        htransitionContinuous htransitionMaps hproject htransition hL2
    have hL1bit : L1.monoBit = false :=
      L1.monoBit_eq_false_of_strictAntiOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = true := by
      simp [ControlledBoundaryAxisLift.monoBit, hdirection]
    simp [hL1bit, hL2bit]
  · have hlocal : StrictMonoOn (fun t : ℝ ↦ L1.lift (u + t))
        (Set.Icc (-r) r) :=
      strictMonoOn_of_projected_real_lifts_comp_strictAntiOn
        hshiftContinuous.continuousOn L2.continuous_lift.continuousOn
        htransitionContinuous htransitionMaps hproject htransition hL2
    have hL1bit : L1.monoBit = true :=
      L1.monoBit_eq_true_of_strictMonoOn_translate hr hsource hlocal
    have hL2bit : L2.monoBit = false := by
      simp [ControlledBoundaryAxisLift.monoBit, hdirection]
    simp [hL1bit, hL2bit]

/-- Equal chart signs and equal local direction bits give the same generic
outward-first label. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.ι} {j : P₂.ι}
    (L1 : ControlledBoundaryAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign : sign1 = sign2) (hbit : L1.monoBit = L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  simp [ControlledBoundaryAxisLift.outwardBit, hsign, hbit]

/-- Opposite signs cancel the bit flip caused by a decreasing transition. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_of_chartSigns_one_neg_one
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.ι} {j : P₂.ι}
    (L1 : ControlledBoundaryAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign1 : sign1 = 1) (hsign2 : sign2 = -1)
    (hbit : L1.monoBit = Bool.not L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  simp [ControlledBoundaryAxisLift.outwardBit, hsign1, hsign2, hbit, hneg]

/-- Opposite signs cancel the bit flip caused by a decreasing transition. -/
theorem ControlledBoundaryAxisLift.outwardBit_eq_of_chartSigns_neg_one_one
    {boundary : UnitAddCircle → M}
    {P₁ P₂ : FiniteControlledBoundaryChartPartition M}
    {i : P₁.ι} {j : P₂.ι}
    (L1 : ControlledBoundaryAxisLift boundary P₁ i)
    (L2 : ControlledBoundaryAxisLift boundary P₂ j)
    {sign1 sign2 : ℝ}
    (hsign1 : sign1 = -1) (hsign2 : sign2 = 1)
    (hbit : L1.monoBit = Bool.not L2.monoBit) :
    L1.outwardBit sign1 = L2.outwardBit sign2 := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  simp [ControlledBoundaryAxisLift.outwardBit, hsign1, hsign2, hbit, hneg]

#print axioms ControlledBoundaryAxisLift
#print axioms ControlledBoundaryActiveAxisLift.toAxisLift
#print axioms strictMonoOn_or_strictAntiOn_ofContinuousProjectedLift
#print axioms ControlledBoundaryAxisLift.ofContinuousProjectedLift
#print axioms ControlledBoundaryAxisLift.monoBit
#print axioms ControlledBoundaryAxisLift.outwardBit
#print axioms ControlledBoundaryAxisLift.monoBit_eq_true_iff
#print axioms ControlledBoundaryAxisLift.monoBit_eq_false_iff
#print axioms
  ControlledBoundaryAxisLift.monoBit_eq_true_of_strictMonoOn_translate
#print axioms
  ControlledBoundaryAxisLift.monoBit_eq_false_of_strictAntiOn_translate
#print axioms ControlledBoundaryAxisLift.outwardBit_eq_true_iff
#print axioms ControlledBoundaryAxisLift.outwardBit_eq_false_iff
#print axioms ControlledBoundaryAxisLift.monoBit_eq_of_local_transition_mono
#print axioms ControlledBoundaryAxisLift.monoBit_eq_not_of_local_transition_anti
#print axioms
  ControlledBoundaryAxisLift.outwardBit_eq_of_chartSign_eq_of_monoBit_eq
#print axioms
  ControlledBoundaryAxisLift.outwardBit_eq_of_chartSigns_one_neg_one
#print axioms
  ControlledBoundaryAxisLift.outwardBit_eq_of_chartSigns_neg_one_one

end

end GromovFilling
