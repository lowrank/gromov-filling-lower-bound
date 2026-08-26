import GromovFilling.BoundaryDegree
import GromovFilling.RadialDegreeStability

/-!
# Componentwise degree of mixed boundary curves

The explicit degree-one calculation at the origin propagates to every
point in the same connected component of the curve complement.
-/

namespace GromovFilling

noncomputable section

/-- A mixed Givens boundary row in additive-circle coordinates. -/
def givensBoundaryCurveAddCircle {N : ℕ} (j : Fin N) :
    UnitAddCircle → ℂ := fun x ↦
  givensBoundaryCurve j (unitAddCircleEquivComplexUnitCircle x)

theorem continuous_givensBoundaryCurveAddCircle
    {N : ℕ} (j : Fin N) :
    Continuous (givensBoundaryCurveAddCircle j) := by
  unfold givensBoundaryCurveAddCircle givensBoundaryCurve
  exact continuous_dominantHarmonicCurve_addCircle
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))

theorem givensBoundaryCurveAddCircle_ne_zero
    {N : ℕ} (j : Fin N) (x : UnitAddCircle) :
    givensBoundaryCurveAddCircle j x ≠ 0 :=
  givensBoundaryCurve_ne_zero j x

/-- Every point in the origin component of the mixed curve complement
sees radial degree `+1`. -/
theorem givensBoundaryCurve_degree_one_on_origin_component
    {N : ℕ} (j : Fin N) :
    ∀ (y : ℂ)
      (hy : y ∈ connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0),
      HasComplexCircleDegree
        (radialMap (givensBoundaryCurveAddCircle j) y
          (curve_ne_of_mem_complement_component
            (givensBoundaryCurveAddCircle j) 0 y hy)) 1 := by
  apply radialMap_degree_constant_on_complement_component
    (givensBoundaryCurveAddCircle j)
    (continuous_givensBoundaryCurveAddCircle j) 0
    (givensBoundaryCurveAddCircle_ne_zero j)
  simpa [givensBoundaryCurveAddCircle] using givensBoundaryCurve_degree_one j

/-- The origin component is a bounded component of the mixed curve
complement, certified by its nonzero degree. -/
theorem givensBoundaryCurve_origin_component_bounded
    {N : ℕ} (j : Fin N) :
    Bornology.IsBounded
      (connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0) := by
  apply complement_component_bounded_of_degree_ne_zero
    (givensBoundaryCurveAddCircle j)
    (continuous_givensBoundaryCurveAddCircle j) 0
    (givensBoundaryCurveAddCircle_ne_zero j)
    (by simpa [givensBoundaryCurveAddCircle] using
      givensBoundaryCurve_degree_one j)
  norm_num

end

end GromovFilling
