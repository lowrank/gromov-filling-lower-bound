import GromovFilling.ModTwoDegree
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Order.IntermediateValue

/-!
# Radial projection away from an omitted point

This is the continuous first step of Lemma 5.4.  If a planar map omits a
point, normalization about that point gives a continuous circle-valued map
extending the normalized boundary curve.
-/

namespace GromovFilling

noncomputable section

/-- The subtype used for Fourier boundary curves is canonically the same
topological circle as mathlib's multiplicative `Circle`. -/
def circleEquivComplexUnitCircle : Circle ≃ₜ ComplexUnitCircle where
  toFun z := ⟨z.1, mem_sphere_zero_iff_norm.mp z.2⟩
  invFun z := ⟨z.1, mem_sphere_zero_iff_norm.mpr z.2⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Identification of the additive circle `ℝ/ℤ` with the complex unit
circle used by radial projection. -/
def unitAddCircleEquivComplexUnitCircle :
    UnitAddCircle ≃ₜ ComplexUnitCircle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
    circleEquivComplexUnitCircle

/-- A point strictly less than half a turn from `x` cannot be its
antipode. -/
lemma ne_unitAddCircle_antipode_of_dist_lt_half (x y : UnitAddCircle)
    (hxy : dist x y < 1 / 2) :
    y ≠ x + ((1 / 2 : ℝ) : UnitAddCircle) := by
  intro hy
  rw [hy, dist_eq_norm, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg,
    AddCircle.norm_half_period_eq] at hxy
  norm_num at hxy

/-- If a circle-valued family stays in an open half-turn ball, then its
image omits a cut, represented by an actual real number. -/
lemma exists_real_cut_avoided_of_dist_lt_half
    {X : Type*} (H : X → UnitAddCircle) (center : X)
    (hsmall : ∀ x, dist (H center) (H x) < 1 / 2) :
    ∃ cut : ℝ, ∀ x, H x ≠ (cut : UnitAddCircle) := by
  let antipode : UnitAddCircle :=
    H center + ((1 / 2 : ℝ) : UnitAddCircle)
  obtain ⟨cut, _hcutIco, hcut⟩ := AddCircle.eq_coe_Ico antipode
  refine ⟨cut, fun x hx ↦ ?_⟩
  have hxAntipode : H x = antipode := hx.trans hcut
  exact (ne_unitAddCircle_antipode_of_dist_lt_half
    (H center) (H x) (hsmall x)) hxAntipode

/-- Simultaneously choose an avoided real cut for every face when all of
its incident edges have circle image within half a turn of a chosen face
center. -/
lemma exists_face_cuts_of_small_edge_images
    {X E F : Type*} (faceEdges : F → Finset E)
    (EdgePoint : E → Type*) (edgeToX : ∀ e : E, EdgePoint e → X)
    (H : X → UnitAddCircle)
    (faceCenter : F → X)
    (hsmall : ∀ (f : F) (e : E), e ∈ faceEdges f → ∀ x : EdgePoint e,
      dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2) :
    ∃ cut : F → ℝ, ∀ (f : F) (e : E), e ∈ faceEdges f → ∀ x,
      H (edgeToX e x) ≠ (cut f : UnitAddCircle) := by
  let antipode : F → UnitAddCircle := fun f ↦
    H (faceCenter f) + ((1 / 2 : ℝ) : UnitAddCircle)
  choose cut _hcutIco hcut using fun f ↦ AddCircle.eq_coe_Ico (antipode f)
  refine ⟨cut, ?_⟩
  intro f e he x hx
  have hxAntipode : H (edgeToX e x) = antipode f := hx.trans (hcut f)
  exact (ne_unitAddCircle_antipode_of_dist_lt_half
    (H (faceCenter f)) (H (edgeToX e x)) (hsmall f e he x)) hxAntipode

/-- Heine--Cantor supplies a single mesh radius on a compact metric space
for which every circle image has diameter less than half a turn. -/
lemma exists_uniform_half_turn_radius
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (H : X → UnitAddCircle) (hH : Continuous H) :
    ∃ δ > 0, ∀ {x y : X}, dist x y < δ → dist (H x) (H y) < 1 / 2 := by
  exact Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hH) (1 / 2) (by norm_num)

/-- A compact domain has one mesh threshold which works for every face:
if each incident edge lies within that threshold of its chosen face
center, then the circle map on those edges admits a facewise avoided cut.

This isolates the analytic input needed from a sufficiently fine
triangulation.  The remaining triangulation theorem only has to produce
the stated mesh estimate. -/
theorem exists_mesh_radius_for_face_cuts
    {X E F : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (faceEdges : F → Finset E)
    (EdgePoint : E → Type*) (edgeToX : ∀ e : E, EdgePoint e → X)
    (H : X → UnitAddCircle) (hH : Continuous H) :
    ∃ δ > 0, ∀ faceCenter : F → X,
      (∀ (f : F) (e : E), e ∈ faceEdges f → ∀ x : EdgePoint e,
        dist (faceCenter f) (edgeToX e x) < δ) →
      ∃ cut : F → ℝ, ∀ (f : F) (e : E), e ∈ faceEdges f → ∀ x,
        H (edgeToX e x) ≠ (cut f : UnitAddCircle) := by
  obtain ⟨δ, hδ, huniform⟩ := exists_uniform_half_turn_radius H hH
  refine ⟨δ, hδ, ?_⟩
  intro faceCenter hmesh
  apply exists_face_cuts_of_small_edge_images faceEdges EdgePoint edgeToX H
    faceCenter
  intro f e he x
  exact huniform (hmesh f e he x)

/-- A real phase of an additive-circle map, using the cut represented by
`cut`.  It is continuous wherever the map avoids that cut. -/
def circlePhaseAway {X : Type*} (cut : ℝ) (H : X → UnitAddCircle) : X → ℝ :=
  fun x ↦ (AddCircle.equivIco (1 : ℝ) cut (H x)).1

theorem circlePhaseAway_projects {X : Type*} (cut : ℝ)
    (H : X → UnitAddCircle) (x : X) :
    ((circlePhaseAway cut H x : ℝ) : UnitAddCircle) = H x := by
  change (AddCircle.equivIco (1 : ℝ) cut).symm
    (AddCircle.equivIco (1 : ℝ) cut (H x)) = H x
  exact (AddCircle.equivIco (1 : ℝ) cut).symm_apply_apply (H x)

theorem continuous_circlePhaseAway {X : Type*} [TopologicalSpace X]
    (cut : ℝ) (H : X → UnitAddCircle) (hH : Continuous H)
    (havoid : ∀ x, H x ≠ (cut : UnitAddCircle)) :
    Continuous (circlePhaseAway cut H) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hlocal := (AddCircle.continuousAt_equivIco (1 : ℝ) cut (havoid x)).comp
    hH.continuousAt
  simpa [circlePhaseAway] using continuousAt_subtype_val.comp hlocal

/-- Uniqueness of real lifts on a preconnected space, in the exact form
needed on every edge of a triangulation: two lifts of the same additive
circle map differ by one constant integer. -/
theorem real_circle_lifts_difference_eq
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (g₁ g₂ : X → ℝ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hproject : ∀ x, (g₁ x : UnitAddCircle) = (g₂ x : UnitAddCircle))
    (x y : X) : g₁ x - g₂ x = g₁ y - g₂ y := by
  obtain ⟨nx, hnx⟩ :=
    exists_integer_difference_of_same_unitAddCircle (g₁ x) (g₂ x) (hproject x)
  obtain ⟨ny, hny⟩ :=
    exists_integer_difference_of_same_unitAddCircle (g₁ y) (g₂ y) (hproject y)
  have hcontinuous : Continuous (fun z ↦ g₁ z - g₂ z) := hg₁.sub hg₂
  have no_strict_increase (a b : X) (na nb : ℤ)
      (hna : (na : ℝ) = g₁ a - g₂ a)
      (hnb : (nb : ℝ) = g₁ b - g₂ b) (hlt : na < nb) : False := by
    have hsucc : na + 1 ≤ nb := by omega
    have hsuccReal : (na : ℝ) + 1 ≤ (nb : ℝ) := by exact_mod_cast hsucc
    have hmid : (na : ℝ) + 1 / 2 ∈
        Set.Icc (g₁ a - g₂ a) (g₁ b - g₂ b) := by
      rw [← hna, ← hnb]
      constructor <;> linarith
    obtain ⟨z, hz⟩ := intermediate_value_univ a b hcontinuous hmid
    obtain ⟨nz, hnz⟩ := exists_integer_difference_of_same_unitAddCircle
      (g₁ z) (g₂ z) (hproject z)
    have hnzReal : (nz : ℝ) = (na : ℝ) + 1 / 2 := hnz.trans hz
    have hparityReal : (((2 * nz : ℤ) : ℝ)) =
        (((2 * na + 1 : ℤ) : ℝ)) := by
      push_cast
      linarith only [hnzReal]
    have hparity : 2 * nz = 2 * na + 1 := by exact_mod_cast hparityReal
    omega
  by_contra hne
  have hnxy : nx ≠ ny := by
    intro h
    apply hne
    rw [← hnx, ← hny, h]
  rcases lt_or_gt_of_ne hnxy with hlt | hgt
  · exact no_strict_increase x y nx ny hnx hny hlt
  · exact no_strict_increase y x ny nx hny hnx hgt

/-- Comparing an edge lift with a face lift does not change the integral
edge turn computed relative to fixed endpoint lifts.  This is the precise
endpoint identity used to make the edge cochain independent of the
incident face. -/
theorem edge_turn_eq_face_transition
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (edgeLift faceLift : X → ℝ)
    (hedge : Continuous edgeLift) (hface : Continuous faceLift)
    (hproject : ∀ x,
      (edgeLift x : UnitAddCircle) = (faceLift x : UnitAddCircle))
    (x₀ x₁ : X) (vertex₀ vertex₁ : ℝ) (turn : ℤ)
    (hturn : (turn : ℝ) =
      (edgeLift x₀ - vertex₀) - (edgeLift x₁ - vertex₁)) :
    (turn : ℝ) =
      (faceLift x₀ - vertex₀) - (faceLift x₁ - vertex₁) := by
  have hconstant := real_circle_lifts_difference_eq faceLift edgeLift
    hface hedge (fun x ↦ (hproject x).symm) x₀ x₁
  linarith

/-- End-to-end finite-triangulation degree obstruction once continuous
edge and face lifts have been chosen.  Connectedness of every edge proves
that its integral turn agrees with the transition computed from either
incident face; combinatorial Stokes then rules out odd boundary degree. -/
theorem no_odd_degree_of_triangulated_circle_extension
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
    (vertexLift : V → ℝ) (faceVertexLift : F → V → ℝ)
    (hsameCircle : ∀ (f : F) (v : V),
      (faceVertexLift f v : UnitAddCircle) =
        (vertexLift v : UnitAddCircle))
    (EdgePoint : E → Type*)
    [∀ e, TopologicalSpace (EdgePoint e)]
    [∀ e, PreconnectedSpace (EdgePoint e)]
    (edgeStart edgeFinish : ∀ e, EdgePoint e)
    (edgeLift : ∀ e, EdgePoint e → ℝ)
    (faceEdgeLift : ∀ _f e, EdgePoint e → ℝ)
    (hedgeContinuous : ∀ e, Continuous (edgeLift e))
    (hfaceContinuous : ∀ (f : F) (e : E), e ∈ faceEdges f →
      Continuous (faceEdgeLift f e))
    (hsameEdgeCircle : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x, (edgeLift e x : UnitAddCircle) =
        (faceEdgeLift f e x : UnitAddCircle))
    (hfaceStart : ∀ (f : F) (e : E), e ∈ faceEdges f →
      faceEdgeLift f e (edgeStart e) =
        faceVertexLift f (edgeEnds e).1)
    (hfaceFinish : ∀ (f : F) (e : E), e ∈ faceEdges f →
      faceEdgeLift f e (edgeFinish e) =
        faceVertexLift f (edgeEnds e).2)
    (turn : E → ℤ)
    (hturn : ∀ e : E, (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2))
    (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree)
    (hodd : Odd degree) : False := by
  apply no_odd_integer_degree_of_real_circle_lifts edgeEnds faceEdges
    boundaryEdges hincidence hfaceEven vertexLift faceVertexLift hsameCircle
    turn
  · intro f e he
    rw [← hfaceStart f e he, ← hfaceFinish f e he]
    exact edge_turn_eq_face_transition (edgeLift e) (faceEdgeLift f e)
      (hedgeContinuous e) (hfaceContinuous f e he)
      (hsameEdgeCircle f e he) (edgeStart e) (edgeFinish e)
      (vertexLift (edgeEnds e).1) (vertexLift (edgeEnds e).2)
      (turn e) (hturn e)
  · exact hdegree
  · exact hodd

/-- The same triangulated obstruction with all face lifts constructed
canonically from cuts avoided by the circle map on the incident edges.
Thus no covering-space lifting theorem is hidden in the hypotheses: the
only refinement datum still required is an omitted cut for each face. -/
theorem no_odd_degree_of_triangulated_circle_map_with_face_cuts
    {X V E F : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype E] [Fintype F]
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
    (vertexPoint : V → X)
    (EdgePoint : E → Type*)
    [∀ e, TopologicalSpace (EdgePoint e)]
    [∀ e, PreconnectedSpace (EdgePoint e)]
    (edgeStart edgeFinish : ∀ e, EdgePoint e)
    (edgeToX : ∀ e, EdgePoint e → X)
    (hedgeToX : ∀ e, Continuous (edgeToX e))
    (hedgeStart : ∀ e, edgeToX e (edgeStart e) =
      vertexPoint (edgeEnds e).1)
    (hedgeFinish : ∀ e, edgeToX e (edgeFinish e) =
      vertexPoint (edgeEnds e).2)
    (H : X → UnitAddCircle) (hH : Continuous H)
    (cut : F → ℝ)
    (hcut : ∀ (f : F) (e : E), e ∈ faceEdges f →
      ∀ x, H (edgeToX e x) ≠ (cut f : UnitAddCircle))
    (vertexLift : V → ℝ)
    (hvertexLift : ∀ v,
      (vertexLift v : UnitAddCircle) = H (vertexPoint v))
    (edgeLift : ∀ e, EdgePoint e → ℝ)
    (hedgeLift : ∀ e, Continuous (edgeLift e))
    (hedgeLiftProjects : ∀ e x,
      (edgeLift e x : UnitAddCircle) = H (edgeToX e x))
    (turn : E → ℤ)
    (hturn : ∀ e : E, (turn e : ℝ) =
      (edgeLift e (edgeStart e) - vertexLift (edgeEnds e).1) -
        (edgeLift e (edgeFinish e) - vertexLift (edgeEnds e).2))
    (degree : ℤ)
    (hdegree : ∑ e ∈ boundaryEdges, turn e = degree)
    (hodd : Odd degree) : False := by
  let faceVertexLift : F → V → ℝ := fun f v ↦
    circlePhaseAway (cut f) H (vertexPoint v)
  let faceEdgeLift : ∀ _f e, EdgePoint e → ℝ := fun f e ↦
    circlePhaseAway (cut f) (H ∘ edgeToX e)
  refine no_odd_degree_of_triangulated_circle_extension edgeEnds faceEdges
    boundaryEdges hincidence hfaceEven vertexLift faceVertexLift ?_
    EdgePoint edgeStart edgeFinish edgeLift faceEdgeLift hedgeLift ?_ ?_ ?_ ?_
    turn hturn degree hdegree hodd
  · intro f v
    exact (circlePhaseAway_projects (cut f) H (vertexPoint v)).trans
      (hvertexLift v).symm
  · intro f e he
    exact continuous_circlePhaseAway (cut f) (H ∘ edgeToX e)
      (hH.comp (hedgeToX e)) (hcut f e he)
  · intro f e _he x
    exact (hedgeLiftProjects e x).trans
      (circlePhaseAway_projects (cut f) (H ∘ edgeToX e) x).symm
  · intro f e _he
    change circlePhaseAway (cut f) (H ∘ edgeToX e) (edgeStart e) =
      circlePhaseAway (cut f) H (vertexPoint (edgeEnds e).1)
    unfold circlePhaseAway
    rw [show (H ∘ edgeToX e) (edgeStart e) =
      H (vertexPoint (edgeEnds e).1) by rw [Function.comp_apply, hedgeStart]]
  · intro f e _he
    change circlePhaseAway (cut f) (H ∘ edgeToX e) (edgeFinish e) =
      circlePhaseAway (cut f) H (vertexPoint (edgeEnds e).2)
    unfold circlePhaseAway
    rw [show (H ∘ edgeToX e) (edgeFinish e) =
      H (vertexPoint (edgeEnds e).2) by rw [Function.comp_apply, hedgeFinish]]

/-- The plane punctured at `y`. -/
abbrev PuncturedPlane (y : ℂ) := {z : ℂ // z ≠ y}

/-- Normalize a point of the punctured plane onto the unit circle centered
at the puncture. -/
def radialProjection (y : ℂ) (z : PuncturedPlane y) : ComplexUnitCircle := by
  refine ⟨(z.1 - y) / (‖z.1 - y‖ : ℂ), ?_⟩
  have hnorm : ‖z.1 - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr z.2)), div_self hnorm]

theorem continuous_radialProjection (y : ℂ) : Continuous (radialProjection y) := by
  apply Continuous.subtype_mk
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z hz
    have hnorm : ‖z.1 - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)
    apply hnorm
    exact_mod_cast hz

/-- Radial projection of a map which omits `y`. -/
def radialMap {X : Type*} (G : X → ℂ) (y : ℂ)
    (havoid : ∀ x, G x ≠ y) : X → ComplexUnitCircle := fun x ↦
  radialProjection y ⟨G x, havoid x⟩

theorem continuous_radialMap {X : Type*} [TopologicalSpace X]
    (G : X → ℂ) (y : ℂ) (havoid : ∀ x, G x ≠ y)
    (hG : Continuous G) : Continuous (radialMap G y havoid) := by
  apply (continuous_radialProjection y).comp
  exact hG.subtype_mk havoid

/-- Radial projection expressed in additive-circle coordinates.  This is
the form to which the real local-lift and integral parity lemmas apply. -/
def radialMapAddCircle {X : Type*} (G : X → ℂ) (y : ℂ)
    (havoid : ∀ x, G x ≠ y) : X → UnitAddCircle := fun x ↦
  unitAddCircleEquivComplexUnitCircle.symm (radialMap G y havoid x)

theorem continuous_radialMapAddCircle {X : Type*} [TopologicalSpace X]
    (G : X → ℂ) (y : ℂ) (havoid : ∀ x, G x ≠ y)
    (hG : Continuous G) : Continuous (radialMapAddCircle G y havoid) := by
  exact unitAddCircleEquivComplexUnitCircle.symm.continuous.comp
    (continuous_radialMap G y havoid hG)

/-- A point omitted by `G` would produce a circle-valued extension of the
radially projected boundary.  Thus any obstruction to such an extension
forces the point into the image. -/
theorem mem_range_of_no_radial_extension
    {X B : Type*} [TopologicalSpace X]
    (boundary : B → X) (G : X → ℂ) (y : ℂ) (hG : Continuous G)
    (hboundary : ∀ b, G (boundary b) ≠ y)
    (hno : ¬ ∃ (H : X → ComplexUnitCircle), Continuous H ∧
      ∀ b : B, H (boundary b) =
        radialProjection y ⟨G (boundary b), hboundary b⟩) :
    y ∈ Set.range G := by
  by_contra hy
  have havoid : ∀ x, G x ≠ y := by
    exact fun x hx ↦ hy ⟨x, hx⟩
  apply hno
  refine ⟨radialMap G y havoid, continuous_radialMap G y havoid hG, ?_⟩
  intro b
  rfl

end

end GromovFilling
