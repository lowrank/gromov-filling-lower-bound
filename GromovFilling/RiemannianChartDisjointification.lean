import GromovFilling.RiemannianAtlasArea
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Disjointed

/-!
# Disjointifying countable Riemannian chart families

An open atlas generally overlaps, while the intrinsic area measure must count
each surface point only once.  This file assigns a point to the first chart
image containing it and pulls that assignment back to the corresponding
coordinate domain.

The construction preserves the union of the chart images, makes the new
images pairwise disjoint, and produces measurable coordinate pieces from
continuous chart parametrizations.  Although compactness will later make the
relevant family finite, indexing by `ℕ` lets the same construction feed the
existing countable-atlas area theorem directly.
-/

open MeasureTheory Set
open scoped Function

namespace GromovFilling

noncomputable section

/-- The part of the `n`th coordinate domain whose image has not already
appeared in an earlier chart image. -/
def disjointChartPiece
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) (n : ℕ) : Set X :=
  domains n ∩ F n ⁻¹'
    disjointed (fun i ↦ F i '' domains i) n

/-- A disjointified coordinate piece stays inside its original domain. -/
theorem disjointChartPiece_subset
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) (n : ℕ) :
    disjointChartPiece F domains n ⊆ domains n :=
  inter_subset_left

/-- The image of a disjointified coordinate piece is exactly the
corresponding disjointified chart image. -/
theorem image_disjointChartPiece
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) (n : ℕ) :
    F n '' disjointChartPiece F domains n =
      disjointed (fun i ↦ F i '' domains i) n := by
  rw [disjointChartPiece, image_inter_preimage]
  exact inter_eq_right.mpr (disjointed_subset _ _)

/-- Distinct disjointified coordinate pieces have disjoint images, even
when the original chart domains overlap. -/
theorem pairwise_disjoint_image_disjointChartPiece
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) :
    Pairwise (Disjoint on fun n ↦ F n '' disjointChartPiece F domains n) := by
  simpa only [image_disjointChartPiece] using
    (disjoint_disjointed (fun n ↦ F n '' domains n))

/-- Disjointification does not change the union covered by the chart
images. -/
theorem iUnion_image_disjointChartPiece
    {X Y : Type*} (F : ℕ → X → Y) (domains : ℕ → Set X) :
    (⋃ n, F n '' disjointChartPiece F domains n) =
      ⋃ n, F n '' domains n := by
  simp_rw [image_disjointChartPiece]
  exact iUnion_disjointed

/-- Continuous chart parametrizations on measurable domains have measurable
disjointified coordinate pieces, provided their chart images are measurable.
Only continuity on the domain is needed: a measurable piecewise extension
handles the arbitrary values of a partial chart inverse outside its target. -/
theorem measurableSet_disjointChartPiece
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    (F : ℕ → X → Y) (domains : ℕ → Set X)
    (hdomains : ∀ n, MeasurableSet (domains n))
    (hcontinuous : ∀ n, ContinuousOn (F n) (domains n))
    (himages : ∀ n, MeasurableSet (F n '' domains n)) (n : ℕ) :
    MeasurableSet (disjointChartPiece F domains n) := by
  classical
  let y0 : Y := Classical.choice inferInstance
  let g : X → Y := (domains n).piecewise (F n) (fun _ ↦ y0)
  have hg : Measurable g := by
    exact (hcontinuous n).measurable_piecewise
      continuous_const.continuousOn (hdomains n)
  have hdisjointed : MeasurableSet
      (disjointed (fun i ↦ F i '' domains i) n) :=
    MeasurableSet.disjointed himages n
  have hpreimage : MeasurableSet
      (g ⁻¹' disjointed (fun i ↦ F i '' domains i) n) :=
    hdisjointed.preimage hg
  have heq : disjointChartPiece F domains n =
      domains n ∩
        g ⁻¹' disjointed (fun i ↦ F i '' domains i) n := by
    ext x
    constructor
    · rintro ⟨hx, hFx⟩
      refine ⟨hx, ?_⟩
      simpa [g, hx] using hFx
    · rintro ⟨hx, hgx⟩
      refine ⟨hx, ?_⟩
      simpa [g, hx] using hgx
  rw [heq]
  exact (hdomains n).inter hpreimage

/-- Open chart domains and open chart images satisfy the measurable-piece
hypotheses automatically. -/
theorem measurableSet_disjointChartPiece_of_isOpen
    {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    (F : ℕ → X → Y) (domains : ℕ → Set X)
    (hdomains : ∀ n, IsOpen (domains n))
    (hcontinuous : ∀ n, ContinuousOn (F n) (domains n))
    (himages : ∀ n, IsOpen (F n '' domains n)) (n : ℕ) :
    MeasurableSet (disjointChartPiece F domains n) :=
  measurableSet_disjointChartPiece F domains
    (fun i ↦ (hdomains i).measurableSet) hcontinuous
    (fun i ↦ (himages i).measurableSet) n

end

end GromovFilling
