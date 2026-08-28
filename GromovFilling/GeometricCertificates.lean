import GromovFilling.PlanarCertificate
import GromovFilling.Certificates

/-!
# Geometric certificate endpoints

This file exposes the currently formalized orientation-free certificate
statements at the exact geometric interfaces coming from the square
homeomorphism plus glued-strip route.
-/

open scoped ENNReal

namespace GromovFilling

noncomputable section

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

/-- Current exact slack-refined orientation-free geometric endpoint for the
square homeomorphism plus glued-strip route at the final certificate
layer. -/
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
