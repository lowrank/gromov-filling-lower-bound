import GromovFilling.DominantHarmonic

/-!
# The mod-2 degree obstruction

This file formalizes the orientation-free algebraic-topology step in the
proof of Lemma 5.4.  A finite triangulation is represented by its faces,
their edge sets, and the boundary edges.  The incidence hypothesis says
that interior edges occur an even number of times and boundary edges an odd
number of times.  No orientations or signs are chosen.
-/

open scoped BigOperators

namespace GromovFilling

noncomputable section

/-- Mod-2 evaluation of an edge cochain on the boundary cycle. -/
def modTwoBoundaryDegree {E : Type*} (boundaryEdges : Finset E)
    (ω : E → ZMod 2) : ZMod 2 :=
  ∑ e ∈ boundaryEdges, ω e

/-- Combinatorial Stokes over `ZMod 2`: a cochain which sums to zero around
every face also sums to zero around the boundary of the surface. -/
theorem modTwo_boundary_degree_zero
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    (faceEdges : F → Finset E) (boundaryEdges : Finset E)
    (hincidence : ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0)
    (ω : E → ZMod 2)
    (hclosed : ∀ f : F, ∑ e ∈ faceEdges f, ω e = 0) :
    modTwoBoundaryDegree boundaryEdges ω = 0 := by
  classical
  calc
    modTwoBoundaryDegree boundaryEdges ω =
        ∑ e : E, (if e ∈ boundaryEdges then (1 : ZMod 2) else 0) * ω e := by
          simp [modTwoBoundaryDegree]
    _ = ∑ e : E,
        (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) * ω e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [hincidence e]
    _ = ∑ e : E, ∑ f : F,
        (if e ∈ faceEdges f then (1 : ZMod 2) else 0) * ω e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_mul]
    _ = ∑ f : F, ∑ e : E,
        (if e ∈ faceEdges f then (1 : ZMod 2) else 0) * ω e := by
          rw [Finset.sum_comm]
    _ = ∑ f : F, ∑ e ∈ faceEdges f, ω e := by
          apply Finset.sum_congr rfl
          intro f _
          simp
    _ = 0 := by simp [hclosed]

/-- Therefore an odd boundary degree cannot extend across such a surface.
This is the contradiction used after radial projection away from a point
omitted by the image. -/
theorem no_odd_modTwo_degree_extension
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    (faceEdges : F → Finset E) (boundaryEdges : Finset E)
    (hincidence : ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0)
    (ω : E → ZMod 2)
    (hclosed : ∀ f : F, ∑ e ∈ faceEdges f, ω e = 0)
    (hodd : modTwoBoundaryDegree boundaryEdges ω = 1) : False := by
  have hzero := modTwo_boundary_degree_zero faceEdges boundaryEdges hincidence ω hclosed
  rw [hodd] at hzero
  norm_num at hzero

end

end GromovFilling
