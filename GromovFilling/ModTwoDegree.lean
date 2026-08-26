import GromovFilling.DominantHarmonic
import Mathlib.Topology.Instances.AddCircle.Real

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

/-- Reduction modulo two of an integral edge-turn cochain.  The integral
turn is the endpoint displacement of a lift of the circle map along the
edge. -/
def integerEdgeParity {E : Type*} (turn : E → ℤ) : E → ZMod 2 :=
  fun e ↦ (turn e : ZMod 2)

/-- An odd integral degree is nonzero, and in fact is exactly one, after
reduction modulo two. -/
lemma intCast_zmod_two_eq_one_of_odd {degree : ℤ} (hdegree : Odd degree) :
    (degree : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := hdegree
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_one]
  change (2 : ZMod 2) * (k : ZMod 2) + 1 = 1
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [htwo]
  simp

/-- The sum of the integral edge turns around the boundary reduces to the
mod-two boundary evaluation of the parity cochain. -/
lemma modTwoBoundaryDegree_integerEdgeParity
    {E : Type*} [Fintype E] [DecidableEq E]
    (boundaryEdges : Finset E) (turn : E → ℤ) (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree) :
    modTwoBoundaryDegree boundaryEdges (integerEdgeParity turn) =
      (degree : ZMod 2) := by
  unfold modTwoBoundaryDegree integerEdgeParity
  rw [← hdegree]
  push_cast
  rfl

/-- Integral version of the degree contradiction.  It records explicitly
the step used in Lemma 5.4: an integer winding cochain which is closed on
the faces cannot have odd total winding on the boundary. -/
theorem no_odd_integer_boundary_degree_extension
    {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E]
    (faceEdges : F → Finset E) (boundaryEdges : Finset E)
    (hincidence : ∀ e : E,
      (∑ f : F, if e ∈ faceEdges f then (1 : ZMod 2) else 0) =
        if e ∈ boundaryEdges then 1 else 0)
    (turn : E → ℤ)
    (hclosed : ∀ f : F,
      ∑ e ∈ faceEdges f, integerEdgeParity turn e = 0)
    (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree)
    (hodd : Odd degree) : False := by
  apply no_odd_modTwo_degree_extension faceEdges boundaryEdges hincidence
    (integerEdgeParity turn) hclosed
  rw [modTwoBoundaryDegree_integerEdgeParity boundaryEdges turn degree hdegree]
  exact intCast_zmod_two_eq_one_of_odd hodd

/-- Fully integral local-lift form of the combinatorial obstruction.  On a
face, changing from fixed vertex lifts to one face lift assigns an integer
transition to every vertex.  The turn on an edge is the difference of its
endpoint transitions.  In characteristic two the sign disappears, so the
resulting edge parity is the coboundary used above. -/
theorem no_odd_integer_degree_of_local_lifts
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
    (transition : F → V → ℤ) (turn : E → ℤ)
    (hlocal : ∀ (f : F) (e : E), e ∈ faceEdges f →
      turn e = transition f (edgeEnds e).1 -
        transition f (edgeEnds e).2)
    (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree)
    (hodd : Odd degree) : False := by
  apply no_odd_modTwo_degree_of_local_lifts edgeEnds faceEdges boundaryEdges
    hincidence hfaceEven
    (fun f v ↦ (transition f v : ZMod 2))
    (integerEdgeParity turn)
  · intro f e he
    change (turn e : ZMod 2) =
      (transition f (edgeEnds e).1 : ZMod 2) +
        (transition f (edgeEnds e).2 : ZMod 2)
    rw [hlocal f e he]
    simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg,
      ZMod.neg_eq_self_mod_two]
  · rw [modTwoBoundaryDegree_integerEdgeParity boundaryEdges turn degree hdegree]
    exact intCast_zmod_two_eq_one_of_odd hodd

/-- Two real lifts of the same point of `ℝ ⧸ ℤ` differ by an integer. -/
lemma exists_integer_difference_of_same_unitAddCircle (a b : ℝ)
    (h : (a : UnitAddCircle) = (b : UnitAddCircle)) :
    ∃ n : ℤ, (n : ℝ) = a - b := by
  have hzero : ((a - b : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  refine ⟨n, ?_⟩
  simpa using hn

/-- Local real phases give the integral transition functions required by
the preceding obstruction.  The hypothesis `hturn` is the endpoint
identity obtained by comparing the lift along an edge with the lift on an
incident face; this statement now performs, rather than assumes, the
integer-valued transition and parity reductions. -/
theorem no_odd_integer_degree_of_real_circle_lifts
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
    (vertexLift : V → ℝ) (faceLift : F → V → ℝ)
    (hsameCircle : ∀ (f : F) (v : V),
      (faceLift f v : UnitAddCircle) = (vertexLift v : UnitAddCircle))
    (turn : E → ℤ)
    (hturn : ∀ (f : F) (e : E), e ∈ faceEdges f →
      (turn e : ℝ) =
        (faceLift f (edgeEnds e).1 - vertexLift (edgeEnds e).1) -
          (faceLift f (edgeEnds e).2 - vertexLift (edgeEnds e).2))
    (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree)
    (hodd : Odd degree) : False := by
  choose transition htransition using fun f v ↦
    exists_integer_difference_of_same_unitAddCircle
      (faceLift f v) (vertexLift v) (hsameCircle f v)
  apply no_odd_integer_degree_of_local_lifts edgeEnds faceEdges boundaryEdges
    hincidence hfaceEven transition turn
  · intro f e he
    have hreal : (turn e : ℝ) =
        (transition f (edgeEnds e).1 : ℝ) -
          (transition f (edgeEnds e).2 : ℝ) := by
      rw [htransition, htransition]
      exact hturn f e he
    exact_mod_cast hreal
  · exact hdegree
  · exact hodd

end

end GromovFilling
