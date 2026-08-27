import GromovFilling.BoundaryDegreeComponents
import GromovFilling.DominantHarmonicDisk

/-!
# Disk extensions of the mixed Givens curves

Each mixed boundary row is the restriction of an explicit polynomial which
is injective on the closed unit disk.  Its open-disk image is therefore the
origin component of the curve complement.
-/

namespace GromovFilling

noncomputable section

/-- The polynomial disk extension of one mixed Givens boundary row. -/
def givensBoundaryPolynomial {N : ℕ} (j : Fin N) : ℂ → ℂ :=
  dominantHarmonicPolynomial
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))

@[simp]
theorem givensBoundaryPolynomial_coe_unitCircle
    {N : ℕ} (j : Fin N) (z : ComplexUnitCircle) :
    givensBoundaryPolynomial j z = givensBoundaryCurve j z := rfl

/-- The sphere image of the polynomial is exactly the range of the
additive-circle boundary parametrization. -/
theorem givensBoundaryPolynomial_image_sphere
    {N : ℕ} (j : Fin N) :
    givensBoundaryPolynomial j '' Metric.sphere 0 1 =
      Set.range (givensBoundaryCurveAddCircle j) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let u : ComplexUnitCircle := ⟨z, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
    obtain ⟨x, hx⟩ := unitAddCircleEquivComplexUnitCircle.surjective u
    refine ⟨x, ?_⟩
    change givensBoundaryCurve j (unitAddCircleEquivComplexUnitCircle x) =
      givensBoundaryPolynomial j z
    rw [hx]
    simpa only [u] using
      (givensBoundaryPolynomial_coe_unitCircle j u).symm
  · rintro ⟨x, rfl⟩
    refine ⟨(unitAddCircleEquivComplexUnitCircle x : ℂ), ?_, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right] using
        (unitAddCircleEquivComplexUnitCircle x).property
    · rfl

/-- The polynomial image of the open disk is the origin component outside
the mixed boundary curve. -/
theorem givensBoundaryPolynomial_image_ball_eq_origin_component
    {N : ℕ} (j : Fin N) :
    givensBoundaryPolynomial j '' Metric.ball 0 1 =
      connectedComponentIn
        (Set.range (givensBoundaryCurveAddCircle j))ᶜ 0 := by
  have h := dominantHarmonicPolynomial_image_ball_eq_component
    ((boundaryRadius (oddMode 0) *
      givensMatrix N j ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : ℝ) : ℂ)
    (fun k : Fin (N - 1) ↦ oddMode (k + 1))
    (fun k : Fin (N - 1) ↦
      ((boundaryRadius (oddMode (k + 1)) *
        givensMatrix N j (higherFinIndex k) : ℝ) : ℂ))
    oddMode_higher_pos (givensBoundaryCurve_dominance j)
  change givensBoundaryPolynomial j '' Metric.ball 0 1 =
    connectedComponentIn
      (givensBoundaryPolynomial j '' Metric.sphere 0 1)ᶜ 0 at h
  rw [givensBoundaryPolynomial_image_sphere j] at h
  exact h

end

end GromovFilling
