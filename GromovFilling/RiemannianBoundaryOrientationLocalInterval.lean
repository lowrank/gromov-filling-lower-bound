import GromovFilling.RiemannianBoundaryOrientationDirectionTransport

/-!
# Centered intervals for local boundary-direction comparisons

The oriented transition argument compares lifts only on a sufficiently small
interval about an overlap coordinate.  These elementary real-line lemmas turn
membership in an open interval and continuity at its center into the closed
interval containment needed by the direction-transport API.
-/

open Set
open scoped Topology

namespace GromovFilling

noncomputable section

/-- A point of an open real interval has a nontrivial centered closed
subinterval contained in that interval. -/
theorem exists_centeredIcc_subset_Icc_of_mem_Ioo
    {a b u : ℝ} (hu : u ∈ Set.Ioo a b) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Set.Icc (-r) r,
      u + t ∈ Set.Icc a b := by
  let r : ℝ := min (u - a) (b - u)
  have hleft : 0 < u - a := sub_pos.mpr hu.1
  have hright : 0 < b - u := sub_pos.mpr hu.2
  have hmin : 0 < min (u - a) (b - u) := lt_min hleft hright
  have hr : 0 < r := by
    simpa only [r] using hmin
  refine ⟨r, hr, ?_⟩
  intro t ht
  rcases ht with ⟨htlower, htupper⟩
  have hleftBound : a - u ≤ t := by
    have hminLeft : r ≤ u - a := by
      dsimp only [r]
      exact min_le_left _ _
    exact le_trans (by linarith) htlower
  have hrightBound : t ≤ b - u := by
    have hminRight : r ≤ b - u := by
      dsimp only [r]
      exact min_le_right _ _
    exact htupper.trans hminRight
  constructor <;>
    linarith

/-- A real function continuous at a point sends some centered closed interval
around that point into any open interval containing its value. -/
theorem ContinuousAt.exists_centeredIcc_mapsTo_Icc
    {f : ℝ → ℝ} {a b u : ℝ}
    (hcontinuous : ContinuousAt f u)
    (himage : f u ∈ Set.Ioo a b) :
    ∃ r : ℝ, 0 < r ∧ Set.MapsTo (fun t : ℝ ↦ f (u + t))
      (Set.Icc (-r) r) (Set.Icc a b) := by
  have hpreimage : f ⁻¹' Set.Ioo a b ∈ 𝓝 u :=
    hcontinuous.preimage_mem_nhds (Ioo_mem_nhds himage.1 himage.2)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hpreimage
  refine ⟨eps / 2, half_pos heps, ?_⟩
  intro t ht
  rcases ht with ⟨htlower, htupper⟩
  have hhalf : eps / 2 < eps := half_lt_self heps
  have htAbs : |t| < eps := by
    rw [abs_lt]
    exact ⟨(neg_lt_neg hhalf).trans_le htlower, htupper.trans_lt hhalf⟩
  apply Set.Ioo_subset_Icc_self
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  simpa only [add_sub_cancel_left] using htAbs

#print axioms exists_centeredIcc_subset_Icc_of_mem_Ioo
#print axioms ContinuousAt.exists_centeredIcc_mapsTo_Icc

end

end GromovFilling
