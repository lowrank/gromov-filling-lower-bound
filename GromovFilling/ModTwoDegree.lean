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

/-- If an edge cochain is represented on each face as the coboundary of
local vertex lifts, then it is closed on that face.  The vertex-incidence
hypothesis is the purely combinatorial statement that the boundary of a
face meets every vertex an even number of times. -/
theorem locally_lifted_edge_cochain_closed
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (hfaceEven : ∀ (f : F) (v : V),
      (∑ e ∈ faceEdges f,
        ((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
          if v = (edgeEnds e).2 then (1 : ZMod 2) else 0)) = 0)
    (localLift : F → V → ZMod 2) (ω : E → ZMod 2)
    (hlocal : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ω e = localLift f (edgeEnds e).1 + localLift f (edgeEnds e).2) :
    ∀ f : F, ∑ e ∈ faceEdges f, ω e = 0 := by
  classical
  intro f
  calc
    (∑ e ∈ faceEdges f, ω e) =
        ∑ e ∈ faceEdges f,
          (localLift f (edgeEnds e).1 + localLift f (edgeEnds e).2) := by
            apply Finset.sum_congr rfl
            intro e he
            exact hlocal f e he
    _ = ∑ e ∈ faceEdges f, ∑ v : V,
          (((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
            if v = (edgeEnds e).2 then (1 : ZMod 2) else 0) *
              localLift f v) := by
            apply Finset.sum_congr rfl
            intro e _
            simp only [add_mul, Finset.sum_add_distrib]
            simp
    _ = ∑ v : V, ∑ e ∈ faceEdges f,
          (((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
            if v = (edgeEnds e).2 then (1 : ZMod 2) else 0) *
              localLift f v) := by
            rw [Finset.sum_comm]
    _ = ∑ v : V,
          (∑ e ∈ faceEdges f,
            ((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
              if v = (edgeEnds e).2 then (1 : ZMod 2) else 0)) *
                localLift f v := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_mul]
    _ = 0 := by simp [hfaceEven]

/-- Full combinatorial degree contradiction from local circle lifts.  This
is the form used after triangulating a hypothetical radial projection: local
arguments on faces give `localLift`, while an odd boundary winding gives
`hodd`. -/
theorem no_odd_modTwo_degree_of_local_lifts
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E]
    (edgeEnds : E → V × V) (faceEdges : F → Finset E)
    (boundaryEdges : Finset E)
    (hincidence : ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0)
    (hfaceEven : ∀ (f : F) (v : V),
      (∑ e ∈ faceEdges f,
        ((if v = (edgeEnds e).1 then (1 : ZMod 2) else 0) +
          if v = (edgeEnds e).2 then (1 : ZMod 2) else 0)) = 0)
    (localLift : F → V → ZMod 2) (ω : E → ZMod 2)
    (hlocal : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ω e = localLift f (edgeEnds e).1 + localLift f (edgeEnds e).2)
    (hodd : modTwoBoundaryDegree boundaryEdges ω = 1) : False := by
  exact no_odd_modTwo_degree_extension faceEdges boundaryEdges hincidence ω
    (locally_lifted_edge_cochain_closed edgeEnds faceEdges hfaceEven
      localLift ω hlocal) hodd

end

end GromovFilling
