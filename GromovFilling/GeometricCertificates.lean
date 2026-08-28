import GromovFilling.PlanarCertificate
import GromovFilling.Certificates

/-!
# Geometric certificate endpoints

This file exposes the currently formalized orientation-free certificate
statements at the geometric interfaces currently available in the development.
-/

open scoped ENNReal NNReal

namespace GromovFilling

noncomputable section

/-- Current exact orientation-free geometric endpoint for the square
homeomorphism plus glued-strip route at the final certificate layer, stated
for the generic source-chart system interface. -/
theorem universal_ennreal_of_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_closedUnitSquare_homeomorph_cylinderStripGlued
    e hboundaryMap

/-- The same geometric endpoint yields the rigorous universal headline
decimal. -/
theorem universal_ennreal_ge_53567723441_of_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal (53567723441 / 10000000000 : ℝ) ≤ area :=
  universal_ennreal_ge_53567723441
    (universal_ennreal_of_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
      S e hboundaryMap)

/-- Exact orientation-free geometric endpoint from bundled compact-open-cover
metric chart data together with the bundled glued-strip polygonal-model
interface on the same boundary. -/
theorem universal_ennreal_of_metric_compactOpenCover_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_cylinderStripGluedArbitrarilyFineData hmodels)

/-- The same bundled metric endpoint yields the rigorous universal headline
decimal. -/
theorem universal_ennreal_ge_53567723441_of_metric_compactOpenCover_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary) :
    ENNReal.ofReal (53567723441 / 10000000000 : ℝ) ≤ area :=
  universal_ennreal_ge_53567723441
    (universal_ennreal_of_metric_compactOpenCover_cylinderStripGluedArbitrarilyFineData
      hboundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece chart
      targetPiece_open localMap K local_lipschitz local_agree budget hmodels)

/-- Exact slack-refined orientation-free geometric endpoint from bundled
compact-open-cover metric chart data together with the bundled glued-strip
polygonal-model interface on the same boundary. -/
theorem universal_ennreal_add_of_metric_compactOpenCover_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_cylinderStripGluedArbitrarilyFineData
      hmodels hbudget)

/-- Exact orientation-free geometric endpoint from bundled compact-open-cover
metric chart data together with the ordinary arbitrarily-fine polygonal-model
interface on the same boundary. This is the direct handoff expected from a
future compact-surface triangulation theorem. -/
theorem universal_ennreal_of_metric_compactOpenCover_arbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_compact_continuous_arbitrarilyFine
      (f := id) continuous_id (by ext t; rfl) hmodels)

/-- The ordinary arbitrarily-fine metric endpoint also yields the rigorous
universal headline decimal. -/
theorem universal_ennreal_ge_53567723441_of_metric_compactOpenCover_arbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal (53567723441 / 10000000000 : ℝ) ≤ area :=
  universal_ennreal_ge_53567723441
    (universal_ennreal_of_metric_compactOpenCover_arbitrarilyFine
      hboundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece chart
      targetPiece_open localMap K local_lipschitz local_agree budget hmodels)

/-- Exact slack-refined orientation-free geometric endpoint from bundled
compact-open-cover metric chart data together with the ordinary arbitrarily-
fine polygonal-model interface on the same boundary. -/
theorem universal_ennreal_add_of_metric_compactOpenCover_arbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_compact_continuous_arbitrarilyFine
      (f := id) continuous_id (by ext t; rfl) hmodels hbudget)

/-- Exact orientation-free geometric endpoint for the square homeomorphism plus
bundled compact-open-cover chart data at the generic source-chart-system
interface, with no need to prepackage the chart family first. -/
theorem universal_ennreal_of_compactOpenCover_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (rowMap : ∀ N : ℕ, Fin N → X → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      rowMap N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_closedUnitSquare_homeomorph_cylinderStripGlued
      e hboundaryMap)

/-- Exact slack-refined orientation-free geometric endpoint for the square
homeomorphism plus bundled compact-open-cover chart data at the generic
source-chart-system interface. -/
theorem universal_ennreal_add_of_compactOpenCover_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (rowMap : ∀ N : ℕ, Fin N → X → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      rowMap N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_closedUnitSquare_homeomorph_cylinderStripGlued
      e hboundaryMap hbudget)

/-- Current exact slack-refined orientation-free geometric endpoint for the
square homeomorphism plus glued-strip route at the generic source-chart-system
interface. -/
theorem universal_ennreal_add_of_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_closedUnitSquare_homeomorph_cylinderStripGlued
    e hboundaryMap hbudget

/-- Current exact orientation-free geometric endpoint for the square
homeomorphism plus glued-strip route at the final certificate layer. -/
theorem universal_ennreal_of_metric_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_closedUnitSquare_homeomorph_cylinderStripGlued
    e hboundaryMap

/-- Exact orientation-free geometric endpoint for the square homeomorphism plus
bundled compact-open-cover chart data, with no need to prepackage the chart
family into a `MetricComplexSourceChartSystem`. -/
theorem universal_ennreal_of_metric_compactOpenCover_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_closedUnitSquare_homeomorph_cylinderStripGlued
      e hboundaryMap)

/-- Exact slack-refined orientation-free geometric endpoint for the square
homeomorphism plus bundled compact-open-cover chart data. -/
theorem universal_ennreal_add_of_metric_compactOpenCover_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_closedUnitSquare_homeomorph_cylinderStripGlued
      e hboundaryMap hbudget)

/-- Exact orientation-free geometric endpoint from a compact source boundary
admitting arbitrarily-fine polygonal models, a continuous map into a target
space, and bundled compact-open-cover metric chart data on that target. -/
theorem universal_ennreal_of_metric_compactOpenCover_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {ι : ℕ → Type*} {area : ℝ≥0∞}
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (sourcePiece : ∀ N : ℕ, ι N → Set Y)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ y : sourcePiece N i,
      givensMetricFourierMap boundary' N j y = localMap N j i (chart N i y))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary' sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_compact_continuous_arbitrarilyFine
      f hf hboundaryMap hmodels)

/-- Exact slack-refined orientation-free geometric endpoint from a compact
source boundary admitting arbitrarily-fine polygonal models, a continuous map
into a target space, and bundled compact-open-cover metric chart data on that
target. -/
theorem universal_ennreal_add_of_metric_compactOpenCover_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (sourcePiece : ∀ N : ℕ, ι N → Set Y)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ y : sourcePiece N i,
      givensMetricFourierMap boundary' N j y = localMap N j i (chart N i y))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) + defect ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary' sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_compact_continuous_arbitrarilyFine
      f hf hboundaryMap hmodels hbudget)

/-- Exact orientation-free geometric endpoint from a compact source boundary
admitting arbitrarily-fine polygonal models, a continuous map into a target
space, and bundled compact-open-cover generic chart data on that target. -/
theorem universal_ennreal_of_compactOpenCover_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {ι : ℕ → Type*} {area : ℝ≥0∞}
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (rowMap : ∀ N : ℕ, Fin N → Y → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set Y)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ y : sourcePiece N i,
      rowMap N j y = localMap N j i (chart N i y))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_compact_continuous_arbitrarilyFine
      f hf hboundaryMap hmodels)

/-- Exact slack-refined orientation-free geometric endpoint from a compact
source boundary admitting arbitrarily-fine polygonal models, a continuous map
into a target space, and bundled compact-open-cover generic chart data on that
target. -/
theorem universal_ennreal_add_of_compactOpenCover_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (rowMap : ∀ N : ℕ, Fin N → Y → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set Y)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ y : sourcePiece N i,
      rowMap N j y = localMap N j i (chart N i y))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i y ↦ local_agree N j i y)).jacobianMass j) + defect ≤ area)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_compact_continuous_arbitrarilyFine
      f hf hboundaryMap hmodels hbudget)


/-- Current exact orientation-free geometric endpoint for the disk-homeomorphic
route at the generic source-chart-system interface. -/
theorem universal_ennreal_of_chartSystem_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_closedUnitDisk_homeomorph e hboundaryMap hdisk

/-- Current exact slack-refined orientation-free geometric endpoint for the
 disk-homeomorphic route at the generic source-chart-system interface. -/
theorem universal_ennreal_add_of_chartSystem_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_closedUnitDisk_homeomorph e hboundaryMap hdisk hbudget

/-- Current exact orientation-free geometric endpoint for the disk-homeomorphic
route at the metric source-chart-system interface. -/
theorem universal_ennreal_of_metric_chartSystem_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_closedUnitDisk_homeomorph e hboundaryMap hdisk

/-- Current exact slack-refined orientation-free geometric endpoint for the
 disk-homeomorphic route at the metric source-chart-system interface. -/
theorem universal_ennreal_add_of_metric_chartSystem_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_closedUnitDisk_homeomorph e hboundaryMap hdisk hbudget

/-- Exact orientation-free geometric endpoint for the disk-homeomorphic route
from bundled compact-open-cover generic chart data. -/
theorem universal_ennreal_of_compactOpenCover_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (rowMap : ∀ N : ℕ, Fin N → X → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      rowMap N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)

/-- Exact slack-refined orientation-free geometric endpoint for the
 disk-homeomorphic route from bundled compact-open-cover generic chart data. -/
theorem universal_ennreal_add_of_compactOpenCover_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (rowMap : ∀ N : ℕ, Fin N → X → ℂ)
    (rowMap_cont : ∀ N : ℕ, ∀ j : Fin N, Continuous (rowMap N j))
    (rowMap_boundary : ∀ N : ℕ, ∀ j : Fin N, ∀ t,
      rowMap N j (boundary t) = givensBoundaryCurveAddCircle j t)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      rowMap N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteComplexSourceChartData.ofCompactOpenCover
          (rowMap N)
          (fun j ↦ rowMap_cont N j)
          (fun j t ↦ rowMap_boundary N j t)
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    ComplexSourceChartSystem.ofCompactOpenCover area rowMap rowMap_cont
      rowMap_boundary sourcePiece sourcePiece_open sourcePiece_cover targetPiece
      chart targetPiece_open localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_closedUnitDisk_homeomorph e hboundaryMap hdisk hbudget)

/-- Exact orientation-free geometric endpoint for the disk-homeomorphic route
from bundled compact-open-cover metric chart data. -/
theorem universal_ennreal_of_metric_compactOpenCover_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)

/-- Exact slack-refined orientation-free geometric endpoint for the
 disk-homeomorphic route from bundled compact-open-cover metric chart data. -/
theorem universal_ennreal_add_of_metric_compactOpenCover_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {ι : ℕ → Type*} {area defect : ℝ≥0∞}
    (hboundary : IsometricCircleBoundary boundary)
    (sourcePiece : ∀ N : ℕ, ι N → Set X)
    (sourcePiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (sourcePiece N i))
    (sourcePiece_cover : ∀ N : ℕ, Set.univ ⊆ ⋃ i, sourcePiece N i)
    (targetPiece : ∀ N : ℕ, ι N → Set ℂ)
    (chart : ∀ N : ℕ, ∀ i : ι N, sourcePiece N i → targetPiece N i)
    (targetPiece_open : ∀ N : ℕ, ∀ i : ι N, IsOpen (targetPiece N i))
    (localMap : ∀ N : ℕ, Fin N → ι N → ℂ → ℂ)
    (K : ∀ N : ℕ, Fin N → ι N → ℝ≥0)
    (local_lipschitz : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N,
      LipschitzOnWith (K N j i) (localMap N j i) (targetPiece N i))
    (local_agree : ∀ N : ℕ, ∀ j : Fin N, ∀ i : ι N, ∀ x : sourcePiece N i,
      givensMetricFourierMap boundary N j x = localMap N j i (chart N i x))
    (budget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) ≤ area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (FiniteMetricComplexSourceChartData.ofCompactOpenCover
          (sourcePiece N)
          (fun i ↦ sourcePiece_open N i)
          (sourcePiece_cover N)
          (targetPiece N)
          (chart N)
          (fun i ↦ targetPiece_open N i)
          (localMap N)
          (K N)
          (fun j i ↦ local_lipschitz N j i)
          (fun j i x ↦ local_agree N j i x)).jacobianMass j) + defect ≤ area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  let S :=
    MetricComplexSourceChartSystem.ofCompactOpenCover area hboundary sourcePiece
      sourcePiece_open sourcePiece_cover targetPiece chart targetPiece_open
      localMap K local_lipschitz local_agree budget
  simpa [S] using
    (S.universal_ennreal_add_of_closedUnitDisk_homeomorph e hboundaryMap hdisk hbudget)

theorem universal_ennreal_add_of_metric_chartSystem_closedUnitSquare_homeomorph_cylinderStripGlued
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_closedUnitSquare_homeomorph_cylinderStripGlued
    e hboundaryMap hbudget

end

end GromovFilling
