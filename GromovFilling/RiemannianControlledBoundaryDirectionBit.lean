import GromovFilling.RiemannianControlledBoundaryDirectionCover

/-!
# Reading local directions from controlled boundary lifts

The direction-cover layer stores the two possible strict directions of a
controlled boundary lift as a Boolean.  The overlap argument only establishes
a direction on a possibly smaller interval.  This file supplies the elementary
order-theoretic adapters which recover the stored Boolean from that local
information.
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

/-- A controlled active-axis lift whose translate is strictly increasing on a
nontrivial centered subinterval has increasing stored direction. -/
theorem ControlledBoundaryActiveAxisLift.monoBit_eq_true_of_strictMonoOn_translate
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i)
    {u r : ℝ} (hr : 0 < r)
    (hsub : ∀ t ∈ Set.Icc (-r) r, u + t ∈ Set.Icc L.a L.b)
    (hmono : StrictMonoOn (fun t : ℝ ↦ L.lift (u + t))
      (Set.Icc (-r) r)) :
    L.monoBit = true := by
  rcases hdirection : L.direction with hL | hL
  · simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]
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

/-- A controlled active-axis lift whose translate is strictly decreasing on a
nontrivial centered subinterval has decreasing stored direction. -/
theorem ControlledBoundaryActiveAxisLift.monoBit_eq_false_of_strictAntiOn_translate
    {boundary : UnitAddCircle → M}
    {P : FiniteControlledBoundaryChartPartition M}
    {i : P.activeAxisCharts}
    (L : ControlledBoundaryActiveAxisLift boundary P i)
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
  · simp [ControlledBoundaryActiveAxisLift.monoBit, hdirection]

#print axioms
  ControlledBoundaryActiveAxisLift.monoBit_eq_true_of_strictMonoOn_translate
#print axioms
  ControlledBoundaryActiveAxisLift.monoBit_eq_false_of_strictAntiOn_translate

end

end GromovFilling
