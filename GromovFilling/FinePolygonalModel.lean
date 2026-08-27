import GromovFilling.PolygonalSurfaceObstruction
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.UniformSpace.Compact

/-!
# Bundled fine polygonal models

This packages the exact finite datum required by the no-odd-degree
argument.  The remaining surface-topology input to Lemma 5.4 is precisely
the construction of one such model for every continuous circle map.
-/

namespace GromovFilling

noncomputable section

/-- The closed unit disk in `ℂ`, used as the canonical model source for the
remaining surface-triangulation input. -/
abbrev ClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

instance : CompactSpace ClosedUnitDisk :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)

/-- Boundary parametrization of the closed unit disk by the standard unit
circle. -/
def closedUnitDiskBoundary (t : UnitAddCircle) : ClosedUnitDisk := by
  refine ⟨(unitAddCircleEquivComplexUnitCircle t : ℂ), ?_⟩
  change dist (unitAddCircleEquivComplexUnitCircle t : ℂ) 0 ≤ 1
  simpa [dist_eq_norm] using (unitAddCircleEquivComplexUnitCircle t).property.le

theorem continuous_closedUnitDiskBoundary :
    Continuous closedUnitDiskBoundary := by
  exact
    (continuous_subtype_val.comp unitAddCircleEquivComplexUnitCircle.continuous).subtype_mk
      (fun t ↦ by
        change dist (unitAddCircleEquivComplexUnitCircle t : ℂ) 0 ≤ 1
        simpa [dist_eq_norm] using (unitAddCircleEquivComplexUnitCircle t).property.le)

theorem closedUnitDiskBoundary_coe (t : UnitAddCircle) :
    ((closedUnitDiskBoundary t : ClosedUnitDisk) : ℂ) =
      (unitAddCircleEquivComplexUnitCircle t : ℂ) := rfl

/-- The sup norm on `ℂ ≃ ℝ²`, used for a square model domain. -/
def complexSupNorm (z : ℂ) : ℝ :=
  max |z.re| |z.im|

theorem complexSupNorm_nonneg (z : ℂ) : 0 ≤ complexSupNorm z := by
  simp [complexSupNorm]

theorem abs_re_le_complexSupNorm (z : ℂ) : |z.re| ≤ complexSupNorm z := by
  simp [complexSupNorm]

theorem abs_im_le_complexSupNorm (z : ℂ) : |z.im| ≤ complexSupNorm z := by
  simp [complexSupNorm]

theorem complexSupNorm_eq_zero_iff (z : ℂ) : complexSupNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Complex.ext <;> apply abs_eq_zero.mp
    · exact le_antisymm
        (by simpa [h] using (abs_re_le_complexSupNorm z))
        (abs_nonneg _)
    · exact le_antisymm
        (by simpa [h] using (abs_im_le_complexSupNorm z))
        (abs_nonneg _)
  · intro h
    simp [complexSupNorm, h]

theorem complexSupNorm_ne_zero_iff (z : ℂ) : complexSupNorm z ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro hz hz'
    exact hz ((complexSupNorm_eq_zero_iff z).2 hz')
  · intro hz hzero
    exact hz ((complexSupNorm_eq_zero_iff z).1 hzero)

theorem continuous_complexSupNorm : Continuous complexSupNorm := by
  simpa [complexSupNorm] using
    (Complex.continuous_re.abs.max Complex.continuous_im.abs)

/-- The closed unit square in `ℂ`, i.e. the unit ball for `complexSupNorm`. -/
abbrev ClosedUnitSquare := {z : ℂ // complexSupNorm z ≤ 1}

instance : CompactSpace ClosedUnitSquare := by
  let s : Set ℂ := {z | complexSupNorm z ≤ 1}
  have hs_closed : IsClosed s := by
    simpa [s] using isClosed_le continuous_complexSupNorm continuous_const
  have hs_subset : s ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt 2) := by
    intro z hz
    change dist z 0 ≤ Real.sqrt 2
    rw [dist_eq_norm, sub_zero]
    calc
      ‖z‖ ≤ Real.sqrt 2 * complexSupNorm z := by
        simpa [complexSupNorm] using Complex.norm_le_sqrt_two_mul_max z
      _ ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 := by ring
  have hs_compact : IsCompact s :=
    IsCompact.of_isClosed_subset
      (isCompact_closedBall (0 : ℂ) (Real.sqrt 2)) hs_closed hs_subset
  simpa [ClosedUnitSquare, s] using isCompact_iff_compactSpace.mp hs_compact

theorem complexSupNorm_inv_smul_le_one {z : ℂ} (hz : complexSupNorm z ≠ 0) :
    complexSupNorm (((complexSupNorm z)⁻¹ : ℝ) • z) ≤ 1 := by
  rw [complexSupNorm]
  refine max_le_iff.mpr ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left
        (abs_re_le_complexSupNorm z)
        (inv_nonneg.mpr (complexSupNorm_nonneg z))
    rw [Complex.smul_re, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (complexSupNorm_nonneg z))]
    simpa [inv_mul_cancel₀ hz] using h
  · have h := mul_le_mul_of_nonneg_left
        (abs_im_le_complexSupNorm z)
        (inv_nonneg.mpr (complexSupNorm_nonneg z))
    rw [Complex.smul_im, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (complexSupNorm_nonneg z))]
    simpa [inv_mul_cancel₀ hz] using h

theorem complexSupNorm_ne_zero_unitAddCircle (t : UnitAddCircle) :
    complexSupNorm (unitAddCircleEquivComplexUnitCircle t : ℂ) ≠ 0 := by
  intro h
  have hz : (unitAddCircleEquivComplexUnitCircle t : ℂ) = 0 :=
    (complexSupNorm_eq_zero_iff _).1 h
  have h01 : (0 : ℝ) = 1 := by
    simpa [hz] using (unitAddCircleEquivComplexUnitCircle t).property
  norm_num at h01

/-- Boundary parametrization of the closed unit square by radial projection of
the standard unit circle. -/
def closedUnitSquareBoundary (t : UnitAddCircle) : ClosedUnitSquare := by
  refine ⟨(Complex.ofReal ((complexSupNorm (unitAddCircleEquivComplexUnitCircle t : ℂ))⁻¹)) *
      (unitAddCircleEquivComplexUnitCircle t : ℂ), ?_⟩
  simpa [smul_eq_mul] using
    complexSupNorm_inv_smul_le_one (complexSupNorm_ne_zero_unitAddCircle t)

theorem continuous_closedUnitSquareBoundary :
    Continuous closedUnitSquareBoundary := by
  let z : UnitAddCircle → ℂ := fun t => (unitAddCircleEquivComplexUnitCircle t : ℂ)
  have hz : Continuous z :=
    continuous_subtype_val.comp unitAddCircleEquivComplexUnitCircle.continuous
  have hs : Continuous fun t : UnitAddCircle => Complex.ofReal ((complexSupNorm (z t))⁻¹) := by
    exact Complex.continuous_ofReal.comp <|
      (continuous_complexSupNorm.comp hz).inv₀ fun t => by
        simpa [z] using complexSupNorm_ne_zero_unitAddCircle t
  have hcont : Continuous fun t : UnitAddCircle =>
      ((⟨(Complex.ofReal ((complexSupNorm (z t))⁻¹)) * z t, by
          simpa [smul_eq_mul, z] using
            complexSupNorm_inv_smul_le_one (complexSupNorm_ne_zero_unitAddCircle t)⟩) :
        ClosedUnitSquare) := by
    exact (hs.mul hz).subtype_mk fun t => by
      simpa [smul_eq_mul, z] using
        complexSupNorm_inv_smul_le_one (complexSupNorm_ne_zero_unitAddCircle t)
  have hEq : closedUnitSquareBoundary = fun t : UnitAddCircle =>
      ((⟨(Complex.ofReal ((complexSupNorm (z t))⁻¹)) * z t, by
          simpa [smul_eq_mul, z] using
            complexSupNorm_inv_smul_le_one (complexSupNorm_ne_zero_unitAddCircle t)⟩) :
        ClosedUnitSquare) := by
    funext t
    rfl
  rw [hEq]
  exact hcont

theorem closedUnitSquareBoundary_coe (t : UnitAddCircle) :
    ((closedUnitSquareBoundary t : ClosedUnitSquare) : ℂ) =
      (Complex.ofReal ((complexSupNorm (unitAddCircleEquivComplexUnitCircle t : ℂ))⁻¹)) *
        (unitAddCircleEquivComplexUnitCircle t : ℂ) := rfl


theorem complexSupNorm_le_norm (z : ℂ) : complexSupNorm z ≤ ‖z‖ := by
  rw [complexSupNorm]
  exact max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)

theorem complexSupNorm_real_smul (r : ℝ) (z : ℂ) :
    complexSupNorm (r • z) = |r| * complexSupNorm z := by
  rw [complexSupNorm, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul]
  simpa [complexSupNorm, mul_comm, mul_left_comm, mul_assoc] using
    (max_mul_of_nonneg |z.re| |z.im| (abs_nonneg r)).symm

/-- Radial map from the closed unit square to the closed unit disk.  It preserves
rays from the origin and rescales each nonzero point so that its Euclidean norm
becomes its square sup norm. -/
def closedUnitSquareToDiskFun (z : ℂ) : ℂ :=
  Complex.ofReal (complexSupNorm z / ‖z‖) * z

theorem norm_closedUnitSquareToDiskFun (z : ℂ) :
    ‖closedUnitSquareToDiskFun z‖ = complexSupNorm z := by
  by_cases hz : z = 0
  · simp [closedUnitSquareToDiskFun, hz, complexSupNorm]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hsnonneg : 0 ≤ complexSupNorm z := complexSupNorm_nonneg z
    simp [closedUnitSquareToDiskFun, hsnonneg, hn, div_eq_mul_inv, mul_assoc]

theorem continuous_closedUnitSquareToDiskFun : Continuous closedUnitSquareToDiskFun := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro w hw
    calc
      dist (closedUnitSquareToDiskFun w) (closedUnitSquareToDiskFun 0)
          = ‖closedUnitSquareToDiskFun w‖ := by simp [closedUnitSquareToDiskFun]
      _ = complexSupNorm w := norm_closedUnitSquareToDiskFun w
      _ ≤ ‖w‖ := complexSupNorm_le_norm w
      _ = dist w 0 := by simp [dist_eq_norm]
      _ < ε := hw
  · have hs : ContinuousAt (fun w : ℂ => complexSupNorm w / ‖w‖) z :=
      (continuous_complexSupNorm.continuousAt.div continuous_norm.continuousAt
        (by simpa using norm_ne_zero_iff.mpr hz))
    simpa [closedUnitSquareToDiskFun] using
      (Complex.continuous_ofReal.continuousAt.comp hs).mul continuousAt_id

/-- Bundled radial map from the closed unit square to the closed unit disk. -/
def closedUnitSquareToDisk (z : ClosedUnitSquare) : ClosedUnitDisk := by
  refine ⟨closedUnitSquareToDiskFun z, ?_⟩
  change dist (closedUnitSquareToDiskFun (z : ℂ)) 0 ≤ 1
  rw [dist_eq_norm, sub_zero, norm_closedUnitSquareToDiskFun]
  exact z.2

theorem continuous_closedUnitSquareToDisk : Continuous closedUnitSquareToDisk := by
  have hbase : Continuous fun z : ClosedUnitSquare => closedUnitSquareToDiskFun z :=
    continuous_closedUnitSquareToDiskFun.comp continuous_subtype_val
  have hcont : Continuous fun z : ClosedUnitSquare =>
      ((⟨closedUnitSquareToDiskFun z, by
          change dist (closedUnitSquareToDiskFun (z : ℂ)) 0 ≤ 1
          rw [dist_eq_norm, sub_zero, norm_closedUnitSquareToDiskFun]
          exact z.2⟩) : ClosedUnitDisk) := by
    exact hbase.subtype_mk fun z => by
      change dist (closedUnitSquareToDiskFun (z : ℂ)) 0 ≤ 1
      rw [dist_eq_norm, sub_zero, norm_closedUnitSquareToDiskFun]
      exact z.2
  have hEq : closedUnitSquareToDisk = fun z : ClosedUnitSquare =>
      ((⟨closedUnitSquareToDiskFun z, by
          change dist (closedUnitSquareToDiskFun (z : ℂ)) 0 ≤ 1
          rw [dist_eq_norm, sub_zero, norm_closedUnitSquareToDiskFun]
          exact z.2⟩) : ClosedUnitDisk) := by
    funext z
    rfl
  rw [hEq]
  exact hcont

theorem closedUnitSquareToDiskFun_radial_cancel {u : ℂ} {s : ℝ}
    (hsdef : complexSupNorm u = s) (hu : ‖u‖ = 1) (hs : s ≠ 0) :
    closedUnitSquareToDiskFun (Complex.ofReal (s⁻¹) * u) = u := by
  have hsnonneg : 0 ≤ s := by
    rw [← hsdef]
    exact complexSupNorm_nonneg u
  have hsup : complexSupNorm (Complex.ofReal (s⁻¹) * u) = 1 := by
    simpa [smul_eq_mul, hsdef, abs_of_nonneg (inv_nonneg.mpr hsnonneg), inv_mul_cancel₀ hs] using
      complexSupNorm_real_smul (s⁻¹) u
  have hnorm : ‖Complex.ofReal (s⁻¹) * u‖ = s⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hsnonneg), hu, mul_one]
  have hratio : 1 / s⁻¹ = s := by
    field_simp [hs]
  rw [closedUnitSquareToDiskFun, hsup, hnorm, hratio]
  simp [hs]

theorem closedUnitSquareToDisk_boundary_coe (t : UnitAddCircle) :
    ((closedUnitSquareToDisk (closedUnitSquareBoundary t) : ClosedUnitDisk) : ℂ) =
      (unitAddCircleEquivComplexUnitCircle t : ℂ) := by
  let u : ℂ := (unitAddCircleEquivComplexUnitCircle t : ℂ)
  let s : ℝ := complexSupNorm u
  have hs : s ≠ 0 := by
    simpa [u, s] using complexSupNorm_ne_zero_unitAddCircle t
  simpa [closedUnitSquareToDisk, closedUnitSquareBoundary_coe, u, s] using
    closedUnitSquareToDiskFun_radial_cancel (u := u) (s := s) rfl
      (by simpa [u] using (unitAddCircleEquivComplexUnitCircle t).property) hs

theorem closedUnitSquareToDisk_boundary (t : UnitAddCircle) :
    closedUnitSquareToDisk (closedUnitSquareBoundary t) = closedUnitDiskBoundary t := by
  apply Subtype.ext
  simpa [closedUnitDiskBoundary_coe] using closedUnitSquareToDisk_boundary_coe t

theorem closedUnitSquareToDisk_comp_boundary :
    closedUnitDiskBoundary = closedUnitSquareToDisk ∘ closedUnitSquareBoundary := by
  funext t
  exact (closedUnitSquareToDisk_boundary t).symm

/-- A boundary parametrization has the mod-two extension obstruction when
no continuous circle-valued map on the whole domain can restrict to odd
degree on that boundary. -/
def HasOddBoundaryDegreeObstruction
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    ∀ d : ℤ, HasCircleDegree (H ∘ boundary) d → Odd d → False

/-- The standard closed parameter interval for every polygonal edge. -/
abbrev ClosedUnitInterval := Set.Icc (0 : ℝ) 1

def closedUnitIntervalStart : ClosedUnitInterval := ⟨0, by norm_num⟩

def closedUnitIntervalFinish : ClosedUnitInterval := ⟨1, by norm_num⟩

/-- A finite polygonal model fine enough for the particular circle map
`H`.  All indexing types are explicit finite types, every face is a
cyclic polygon, every edge has one or two incident faces according as it
is a boundary or interior edge, and the incident edge images of each face
lie in one open half-turn ball. -/
structure FinePolygonalModel
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) (H : X → UnitAddCircle) where
  vertexCount : ℕ
  edgeCount : ℕ
  faceCount : ℕ
  faceSize : ℕ
  boundarySize : ℕ
  edgeEnds : Fin edgeCount → Fin vertexCount × Fin vertexCount
  faceEdges : Fin faceCount → Finset (Fin edgeCount)
  boundaryEdges : Finset (Fin edgeCount)
  edgeFaceCount : ∀ e : Fin edgeCount,
    (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
      if e ∈ boundaryEdges then 1 else 2
  faceVertex : Fin faceCount → Fin (faceSize + 1) → Fin vertexCount
  faceEdge : Fin faceCount → Fin (faceSize + 1) → Fin edgeCount
  faceVertex_injective : ∀ f, Function.Injective (faceVertex f)
  faceEdge_injective : ∀ f, Function.Injective (faceEdge f)
  faceEdges_eq : ∀ f, faceEdges f = Finset.univ.image (faceEdge f)
  faceEdge_ends : ∀ f k, edgeEnds (faceEdge f k) =
    (faceVertex f k, faceVertex f (cyclicSucc k))
  boundaryEdge : Fin (boundarySize + 1) → Fin edgeCount
  boundaryEdge_injective : Function.Injective boundaryEdge
  boundaryVertex : Fin (boundarySize + 1) → Fin vertexCount
  boundaryEdge_ends : ∀ k, edgeEnds (boundaryEdge k) =
    (boundaryVertex k, boundaryVertex (cyclicSucc k))
  boundaryEdges_eq : boundaryEdges = Finset.univ.image boundaryEdge
  vertexPoint : Fin vertexCount → X
  edgeToX : Fin edgeCount → ClosedUnitInterval → X
  edgeToX_continuous : ∀ e, Continuous (edgeToX e)
  edgeToX_start : ∀ e, edgeToX e closedUnitIntervalStart =
    vertexPoint (edgeEnds e).1
  edgeToX_finish : ∀ e, edgeToX e closedUnitIntervalFinish =
    vertexPoint (edgeEnds e).2
  faceCenter : Fin faceCount → X
  halfTurn_mesh : ∀ (f : Fin faceCount) (e : Fin edgeCount),
    e ∈ faceEdges f → ∀ x : ClosedUnitInterval,
      dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2
  boundaryParameter : ∀ _k,
    ClosedUnitInterval → ℝ
  boundaryParameter_continuous : ∀ k, Continuous (boundaryParameter k)
  boundaryParameter_start : ∀ k,
    boundaryParameter k closedUnitIntervalStart = cyclicVertexParameter k
  boundaryParameter_finish : ∀ k,
    boundaryParameter k closedUnitIntervalFinish =
      cyclicEdgeFinishParameter k
  boundaryPath : ∀ k x,
    edgeToX (boundaryEdge k) x =
      boundary ((boundaryParameter k x : ℝ) : UnitAddCircle)


/-- An abstract version of `FinePolygonalModel` indexed by arbitrary finite
vertex, edge, and face types instead of `Fin` counts.  This is more convenient
for explicit mesh constructions, while the same finite-mesh obstruction theorem
still applies verbatim. -/
structure AbstractFinePolygonalModel
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) (H : X → UnitAddCircle) where
  Vertex : Type
  Edge : Type
  Face : Type
  [instVertexFintype : Fintype Vertex]
  [instEdgeFintype : Fintype Edge]
  [instFaceFintype : Fintype Face]
  [instVertexDecidableEq : DecidableEq Vertex]
  [instEdgeDecidableEq : DecidableEq Edge]
  [instFaceDecidableEq : DecidableEq Face]
  faceSize : ℕ
  boundarySize : ℕ
  edgeEnds : Edge → Vertex × Vertex
  faceEdges : Face → Finset Edge
  boundaryEdges : Finset Edge
  edgeFaceCount : ∀ e : Edge,
    (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
      if e ∈ boundaryEdges then 1 else 2
  faceVertex : Face → Fin (faceSize + 1) → Vertex
  faceEdge : Face → Fin (faceSize + 1) → Edge
  faceVertex_injective : ∀ f, Function.Injective (faceVertex f)
  faceEdge_injective : ∀ f, Function.Injective (faceEdge f)
  faceEdges_eq : ∀ f, faceEdges f = Finset.univ.image (faceEdge f)
  faceEdge_ends : ∀ f k, edgeEnds (faceEdge f k) =
    (faceVertex f k, faceVertex f (cyclicSucc k))
  boundaryEdge : Fin (boundarySize + 1) → Edge
  boundaryEdge_injective : Function.Injective boundaryEdge
  boundaryVertex : Fin (boundarySize + 1) → Vertex
  boundaryEdge_ends : ∀ k, edgeEnds (boundaryEdge k) =
    (boundaryVertex k, boundaryVertex (cyclicSucc k))
  boundaryEdges_eq : boundaryEdges = Finset.univ.image boundaryEdge
  vertexPoint : Vertex → X
  edgeToX : Edge → ClosedUnitInterval → X
  edgeToX_continuous : ∀ e, Continuous (edgeToX e)
  edgeToX_start : ∀ e, edgeToX e closedUnitIntervalStart =
    vertexPoint (edgeEnds e).1
  edgeToX_finish : ∀ e, edgeToX e closedUnitIntervalFinish =
    vertexPoint (edgeEnds e).2
  faceCenter : Face → X
  halfTurn_mesh : ∀ (f : Face) (e : Edge),
    e ∈ faceEdges f → ∀ x : ClosedUnitInterval,
      dist (H (faceCenter f)) (H (edgeToX e x)) < 1 / 2
  boundaryParameter : ∀ _k,
    ClosedUnitInterval → ℝ
  boundaryParameter_continuous : ∀ k, Continuous (boundaryParameter k)
  boundaryParameter_start : ∀ k,
    boundaryParameter k closedUnitIntervalStart = cyclicVertexParameter k
  boundaryParameter_finish : ∀ k,
    boundaryParameter k closedUnitIntervalFinish =
      cyclicEdgeFinishParameter k
  boundaryPath : ∀ k x,
    edgeToX (boundaryEdge k) x =
      boundary ((boundaryParameter k x : ℝ) : UnitAddCircle)

/-- The underlying finite obstruction applies equally to abstract finite-index
polygonal models. -/
theorem AbstractFinePolygonalModel.no_odd_boundary_degree
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractFinePolygonalModel boundary H) (hH : Continuous H)
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundary) degree)
    (hodd : Odd degree) : False := by
  classical
  let _ := D.instVertexFintype
  let _ := D.instEdgeFintype
  let _ := D.instFaceFintype
  let _ := D.instVertexDecidableEq
  let _ := D.instEdgeDecidableEq
  let _ := D.instFaceDecidableEq
  exact no_odd_degree_of_fine_polygonal_circle_extension
    D.edgeEnds D.faceEdges D.boundaryEdges D.edgeFaceCount
    D.faceVertex D.faceEdge D.faceVertex_injective D.faceEdge_injective
    D.faceEdges_eq D.faceEdge_ends D.boundaryEdge
    D.boundaryEdge_injective D.boundaryVertex D.boundaryEdge_ends
    D.boundaryEdges_eq D.vertexPoint (fun _ ↦ ClosedUnitInterval)
    (fun _ ↦ closedUnitIntervalStart) (fun _ ↦ closedUnitIntervalFinish)
    D.edgeToX D.edgeToX_continuous D.edgeToX_start D.edgeToX_finish
    H hH D.faceCenter D.halfTurn_mesh boundary D.boundaryParameter
    D.boundaryParameter_continuous D.boundaryParameter_start
    D.boundaryParameter_finish D.boundaryPath degree hdegree hodd

/-- Map-dependent fine polygonal models packaged with arbitrary finite index
sets. -/
def HasAbstractFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    Nonempty (AbstractFinePolygonalModel boundary H)

/-- Abstract finite-index polygonal models imply the odd boundary-degree
obstruction, just as the concrete `Fin`-indexed version does. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasAbstractFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  obtain ⟨D⟩ := hfine H hH
  exact D.no_odd_boundary_degree hH degree hdegree hodd


/-- Every concrete `Fin`-indexed model is an abstract finite-index model. -/
def FinePolygonalModel.toAbstractFinePolygonalModel
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : FinePolygonalModel boundary H) :
    AbstractFinePolygonalModel boundary H where
  Vertex := Fin D.vertexCount
  Edge := Fin D.edgeCount
  Face := Fin D.faceCount
  faceSize := D.faceSize
  boundarySize := D.boundarySize
  edgeEnds := D.edgeEnds
  faceEdges := D.faceEdges
  boundaryEdges := D.boundaryEdges
  edgeFaceCount := D.edgeFaceCount
  faceVertex := D.faceVertex
  faceEdge := D.faceEdge
  faceVertex_injective := D.faceVertex_injective
  faceEdge_injective := D.faceEdge_injective
  faceEdges_eq := D.faceEdges_eq
  faceEdge_ends := D.faceEdge_ends
  boundaryEdge := D.boundaryEdge
  boundaryEdge_injective := D.boundaryEdge_injective
  boundaryVertex := D.boundaryVertex
  boundaryEdge_ends := D.boundaryEdge_ends
  boundaryEdges_eq := D.boundaryEdges_eq
  vertexPoint := D.vertexPoint
  edgeToX := D.edgeToX
  edgeToX_continuous := D.edgeToX_continuous
  edgeToX_start := D.edgeToX_start
  edgeToX_finish := D.edgeToX_finish
  faceCenter := D.faceCenter
  halfTurn_mesh := D.halfTurn_mesh
  boundaryParameter := D.boundaryParameter
  boundaryParameter_continuous := D.boundaryParameter_continuous
  boundaryParameter_start := D.boundaryParameter_start
  boundaryParameter_finish := D.boundaryParameter_finish
  boundaryPath := D.boundaryPath

/-- The exact fine-triangulation property needed of a surface boundary:
every continuous circle map on the domain has a compatible finite
polygonal model below its half-turn scale. -/
def HasFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    Nonempty (FinePolygonalModel boundary H)

/-- The concrete `Fin`-indexed interface implies the abstract finite-index
version by forgetting that the indices were encoded as counts. -/
theorem hasAbstractFinePolygonalModels_of_finePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasFinePolygonalModels boundary) :
    HasAbstractFinePolygonalModels boundary := by
  intro H hH
  obtain ⟨D⟩ := hfine H hH
  exact ⟨D.toAbstractFinePolygonalModel⟩

/-- A purely geometric polygonal model at mesh scale `ε`.  We reuse a
`FinePolygonalModel` for the constant circle map to carry exactly the same
finite incidence, edge, and boundary data; the additional field says that
each face center is within `ε` of every point of every incident edge. -/
structure GeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (ε : ℝ) where
  model : FinePolygonalModel boundary (fun _ ↦ (0 : UnitAddCircle))
  mesh : ∀ (f : Fin model.faceCount) (e : Fin model.edgeCount),
    e ∈ model.faceEdges f → ∀ x : ClosedUnitInterval,
      dist (model.faceCenter f) (model.edgeToX e x) < ε

/-- Replace the vacuous constant-map half-turn estimate in a geometric
model by a supplied estimate for a particular circle-valued map. -/
def GeometricPolygonalModel.toFinePolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : GeometricPolygonalModel boundary ε)
    (H : X → UnitAddCircle)
    (hhalf : ∀ (f : Fin D.model.faceCount) (e : Fin D.model.edgeCount),
      e ∈ D.model.faceEdges f → ∀ x : ClosedUnitInterval,
        dist (H (D.model.faceCenter f)) (H (D.model.edgeToX e x)) < 1 / 2) :
    FinePolygonalModel boundary H :=
  { D.model with halfTurn_mesh := hhalf }

/-- Push a geometric polygonal model forward along a continuous map whose
restriction to the boundary agrees with a new parametrization.  The
combinatorics and edge parameters are unchanged; only the vertex, edge, and
face-center locations are transported. -/
def GeometricPolygonalModel.map
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {δ ε : ℝ} (D : GeometricPolygonalModel boundary δ)
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmesh : ∀ (face : Fin D.model.faceCount) (e : Fin D.model.edgeCount),
      e ∈ D.model.faceEdges face → ∀ x : ClosedUnitInterval,
        dist (f (D.model.faceCenter face)) (f (D.model.edgeToX e x)) < ε) :
    GeometricPolygonalModel boundary' ε :=
  { model :=
      { D.model with
        vertexPoint := fun v ↦ f (D.model.vertexPoint v)
        edgeToX := fun e x ↦ f (D.model.edgeToX e x)
        edgeToX_continuous := fun e ↦ hf.comp (D.model.edgeToX_continuous e)
        edgeToX_start := by
          intro e
          rw [D.model.edgeToX_start]
        edgeToX_finish := by
          intro e
          rw [D.model.edgeToX_finish]
        faceCenter := fun face ↦ f (D.model.faceCenter face)
        halfTurn_mesh := by
          intro face e he x
          simp only [D.model.halfTurn_mesh face e he x]
        boundaryPath := by
          intro k x
          rw [hboundary]
          simpa using congrArg f (D.model.boundaryPath k x) }
    mesh := hmesh }

/-- The map-independent surface input: compatible polygonal models exist
at every positive geometric mesh scale. -/
def HasArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (GeometricPolygonalModel boundary ε)

/-- Arbitrarily fine polygonal models transport across continuous maps from a
compact source: choose a sufficiently small source mesh using uniform
continuity, then push the model forward. -/
theorem hasArbitrarilyFinePolygonalModels_of_compact_continuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasArbitrarilyFinePolygonalModels boundary' := by
  intro ε hε
  have hUniform : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.map f hf hboundary ?_⟩
  intro face e he x
  exact hδf (D.mesh face e he x)

/-- Homeomorphic compact images inherit arbitrarily fine polygonal models by
transporting them along the homeomorphism. -/
theorem hasArbitrarilyFinePolygonalModels_of_homeomorph
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasArbitrarilyFinePolygonalModels boundary' :=
  hasArbitrarilyFinePolygonalModels_of_compact_continuous
    e e.continuous_toFun hboundary hmodels


/-- Closed-square models transfer to the closed disk through the radial square-to-disk
map.  This reduces the remaining disk existence theorem to an explicit square-mesh
construction. -/
theorem hasArbitrarilyFinePolygonalModels_of_closedUnitSquare
    (hsquare : HasArbitrarilyFinePolygonalModels closedUnitSquareBoundary) :
    HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareToDisk continuous_closedUnitSquareToDisk
    closedUnitSquareToDisk_comp_boundary hsquare

/-- On a compact metric domain, arbitrarily fine geometric polygonal
models provide the map-dependent half-turn models needed by the mod-two
argument.  This discharges the compactness/uniform-continuity step in the
surface triangulation interface. -/
theorem hasFinePolygonalModels_of_arbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasFinePolygonalModels boundary := by
  intro H hH
  have hUniform : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hδH⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (1 / 2) (by norm_num)
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.toFinePolygonalModel H ?_⟩
  intro f e he x
  exact hδH (D.mesh f e he x)

/-- Homeomorphic compact images inherit the map-dependent fine polygonal-model
interface after transporting arbitrarily fine geometric models and then using
uniform continuity. -/
theorem hasFinePolygonalModels_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasFinePolygonalModels boundary' :=
  hasFinePolygonalModels_of_arbitrarilyFine
    (hasArbitrarilyFinePolygonalModels_of_homeomorph e hboundary hmodels)

/-- A bundled fine polygonal model rules out an odd degree on its actual
cyclic boundary.  All auxiliary cuts and lifts are constructed by the
underlying finite-mesh theorem. -/
theorem FinePolygonalModel.no_odd_boundary_degree
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : FinePolygonalModel boundary H) (hH : Continuous H)
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundary) degree)
    (hodd : Odd degree) : False := by
  exact no_odd_degree_of_fine_polygonal_circle_extension
    D.edgeEnds D.faceEdges D.boundaryEdges D.edgeFaceCount
    D.faceVertex D.faceEdge D.faceVertex_injective D.faceEdge_injective
    D.faceEdges_eq D.faceEdge_ends D.boundaryEdge
    D.boundaryEdge_injective D.boundaryVertex D.boundaryEdge_ends
    D.boundaryEdges_eq D.vertexPoint (fun _ ↦ ClosedUnitInterval)
    (fun _ ↦ closedUnitIntervalStart) (fun _ ↦ closedUnitIntervalFinish)
    D.edgeToX D.edgeToX_continuous D.edgeToX_start D.edgeToX_finish
    H hH D.faceCenter D.halfTurn_mesh boundary D.boundaryParameter
    D.boundaryParameter_continuous D.boundaryParameter_start
    D.boundaryParameter_finish D.boundaryPath degree hdegree hodd

/-- Fine polygonal models imply the abstract odd boundary-degree
obstruction used by the coverage theorems. -/
theorem hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  obtain ⟨D⟩ := hfine H hH
  exact D.no_odd_boundary_degree hH degree hdegree hodd

/-- A compact metric domain with arbitrarily fine compatible geometric
models has the odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    (hasFinePolygonalModels_of_arbitrarilyFine hmodels)

/-- A boundary-respecting homeomorphism from a compact source carrying
arbitrarily fine polygonal models transfers the odd boundary-degree
obstruction to the target boundary.  This is the exact topological input
needed by the coverage theorems once a source-space triangulation theorem is
available. -/
theorem hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary' :=
  hasOddBoundaryDegreeObstruction_of_finePolygonalModels
    (hasFinePolygonalModels_of_homeomorph_arbitrarilyFine e hboundary hmodels)

/-- Once the closed unit disk is shown to admit arbitrarily fine polygonal
models, every compact target homeomorphic to it inherits the same
map-independent interface through its boundary identification. -/
theorem hasArbitrarilyFinePolygonalModels_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    HasArbitrarilyFinePolygonalModels boundary :=
  hasArbitrarilyFinePolygonalModels_of_homeomorph e hboundary hdisk

/-- Disk-to-target transfer for the map-dependent fine polygonal-model
interface.  This packages the exact downstream use of a future closed-disk
triangulation theorem. -/
theorem hasFinePolygonalModels_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    HasFinePolygonalModels boundary :=
  hasFinePolygonalModels_of_homeomorph_arbitrarilyFine e hboundary hdisk

/-- Disk-to-target transfer for the odd boundary-degree obstruction.  After
the actual disk existence theorem is proved, this is the one-line handoff to
the coverage theorems. -/
theorem hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
    e hboundary hdisk

end

end GromovFilling
