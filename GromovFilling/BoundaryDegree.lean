import GromovFilling.BoundaryCertificate
import GromovFilling.DominantHarmonicDegree

/-!
# Degree of the mixed boundary rows

The Givens-row curves used by the universal certificate are not only
Jordan parametrizations: their radial normalization about the origin has
integer degree `+1`.
-/

namespace GromovFilling

noncomputable section

lemma oddMode_higher_pos {N : ℕ} (k : Fin (N - 1)) :
    1 ≤ oddMode (k + 1) := by
  unfold oddMode
  omega

theorem givensBoundaryCurve_ne_zero {N : ℕ} (j : Fin N)
    (x : UnitAddCircle) :
    givensBoundaryCurve j (unitAddCircleEquivComplexUnitCircle x) ≠ 0 := by
  unfold givensBoundaryCurve
  exact dominantHarmonicCurve_ne_zero
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))
    oddMode_higher_pos (givensBoundaryCurve_dominance j) x

/-- Every explicit mixed boundary row winds once around the origin. -/
theorem givensBoundaryCurve_degree_one {N : ℕ} (j : Fin N) :
    HasComplexCircleDegree
      (radialMap
        (fun x : UnitAddCircle ↦
          givensBoundaryCurve j (unitAddCircleEquivComplexUnitCircle x))
        0 (givensBoundaryCurve_ne_zero j))
      1 := by
  unfold givensBoundaryCurve
  exact dominantHarmonicCurve_degree_one
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))
    oddMode_higher_pos (givensBoundaryCurve_dominance j)

end

end GromovFilling
