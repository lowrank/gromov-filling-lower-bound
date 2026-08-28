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

open unitInterval

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

/-- The standard closed parameter interval for every polygonal edge. -/
abbrev ClosedUnitInterval := Set.Icc (0 : ℝ) 1

def closedUnitIntervalStart : ClosedUnitInterval := ⟨0, by norm_num⟩

def closedUnitIntervalFinish : ClosedUnitInterval := ⟨1, by norm_num⟩

/-- The `j`-th equally spaced angular subdivision point of the circle. -/
def angularSubdivisionPoint (m : ℕ) (j : Fin (m + 1)) : UnitAddCircle :=
  (((j : ℕ) : ℝ) / (m + 1) : ℝ)

/-- The affine parameter running along the `j`-th angular edge of an
`(m + 1)`-gon. -/
def angularSubdivisionParameter (m : ℕ) (j : Fin (m + 1))
    (x : ClosedUnitInterval) : ℝ :=
  (((x : ℝ) + (j : ℝ)) / (m + 1))

/-- The corresponding angular edge path on `UnitAddCircle`. -/
def angularSubdivisionArc (m : ℕ) (j : Fin (m + 1)) :
    ClosedUnitInterval → UnitAddCircle :=
  fun x ↦ (angularSubdivisionParameter m j x : ℝ)

theorem continuous_angularSubdivisionArc (m : ℕ) (j : Fin (m + 1)) :
    Continuous (angularSubdivisionArc m j) := by
  have hbase : Continuous fun x : ClosedUnitInterval =>
      (((x : ℝ) + (j : ℝ)) / (m + 1) : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((continuous_subtype_val.add continuous_const).const_mul (((m + 1 : ℕ) : ℝ)⁻¹))
  exact (AddCircle.continuous_mk' 1).comp hbase

theorem angularSubdivisionArc_start (m : ℕ) (j : Fin (m + 1)) :
    angularSubdivisionArc m j closedUnitIntervalStart = angularSubdivisionPoint m j := by
  simp [angularSubdivisionArc, angularSubdivisionParameter, angularSubdivisionPoint,
    closedUnitIntervalStart]

theorem angularSubdivisionArc_finish (m : ℕ) (j : Fin (m + 1)) :
    angularSubdivisionArc m j closedUnitIntervalFinish =
      angularSubdivisionPoint m (cyclicSucc j) := by
  by_cases hj : j = Fin.last m
  · subst hj
    rw [cyclicSucc_last]
    have hx : ((((1 : ℝ) + (m : ℝ)) / (m + 1) : ℝ) : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).2
      refine ⟨1, ?_⟩
      have hpos : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hpos]
      ring
    simpa [angularSubdivisionArc, angularSubdivisionParameter, angularSubdivisionPoint,
      closedUnitIntervalFinish] using hx
  · have hsucc : (cyclicSucc j).val = j.val + 1 :=
      cyclicSucc_val_of_ne_last j hj
    simp [angularSubdivisionArc, angularSubdivisionParameter, angularSubdivisionPoint,
      closedUnitIntervalFinish, hsucc, add_comm]

/-- The `i`-th equally spaced radial subdivision point of `[0,1]`.  There are
`n + 2` vertices and `n + 1` radial subintervals. -/
def radialSubdivisionPoint (n : ℕ) (i : Fin (n + 2)) : ClosedUnitInterval := by
  refine ⟨(i : ℝ) / (n + 1), ?_⟩
  constructor
  · have hi0 : 0 ≤ (i : ℝ) := by positivity
    have hden : 0 < (n + 1 : ℝ) := by positivity
    exact div_nonneg hi0 hden.le
  · have hi : (i : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    simpa using hi

/-- The lower endpoint index of the `i`-th radial subinterval. -/
def radialSubdivisionLower {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self _)⟩

/-- The upper endpoint index of the `i`-th radial subinterval. -/
def radialSubdivisionUpper {n : ℕ} (i : Fin (n + 1)) : Fin (n + 2) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

/-- The affine path along the `i`-th radial subinterval. -/
def radialSubdivisionArc (n : ℕ) (i : Fin (n + 1)) :
    ClosedUnitInterval → ClosedUnitInterval := by
  intro x
  refine ⟨(((x : ℝ) + (i : ℝ)) / (n + 1)), ?_⟩
  constructor
  · have hx0 : 0 ≤ (x : ℝ) := x.2.1
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    have hden : 0 < (n + 1 : ℝ) := by positivity
    exact div_nonneg (by nlinarith) hden.le
  · have hi : (i : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hx : (x : ℝ) ≤ 1 := x.2.2
    have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith

theorem continuous_radialSubdivisionArc (n : ℕ) (i : Fin (n + 1)) :
    Continuous (radialSubdivisionArc n i) := by
  have hbase : Continuous fun x : ClosedUnitInterval =>
      (((x : ℝ) + (i : ℝ)) / (n + 1) : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((continuous_subtype_val.add continuous_const).const_mul (((n + 1 : ℕ) : ℝ)⁻¹))
  exact hbase.subtype_mk fun x ↦ by
    constructor
    · have hx0 : 0 ≤ (x : ℝ) := x.2.1
      have hi0 : 0 ≤ (i : ℝ) := by positivity
      have hden : 0 < (n + 1 : ℝ) := by positivity
      exact div_nonneg (by nlinarith) hden.le
    · have hi : (i : ℝ) ≤ n := by
        exact_mod_cast Nat.le_of_lt_succ i.isLt
      have hx : (x : ℝ) ≤ 1 := x.2.2
      have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith

theorem radialSubdivisionPoint_zero (n : ℕ) :
    radialSubdivisionPoint n 0 = closedUnitIntervalStart := by
  ext
  simp [radialSubdivisionPoint, closedUnitIntervalStart]

theorem radialSubdivisionPoint_last (n : ℕ) :
    radialSubdivisionPoint n (Fin.last (n + 1)) = closedUnitIntervalFinish := by
  apply Subtype.ext
  change (((Fin.last (n + 1) : Fin (n + 2)) : ℝ) / (n + 1) : ℝ) = 1
  have hpos : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hpos]
  simp

theorem radialSubdivisionArc_start (n : ℕ) (i : Fin (n + 1)) :
    radialSubdivisionArc n i closedUnitIntervalStart =
      radialSubdivisionPoint n (radialSubdivisionLower i) := by
  apply Subtype.ext
  simp [radialSubdivisionArc, radialSubdivisionPoint, radialSubdivisionLower,
    closedUnitIntervalStart]

theorem radialSubdivisionArc_finish (n : ℕ) (i : Fin (n + 1)) :
    radialSubdivisionArc n i closedUnitIntervalFinish =
      radialSubdivisionPoint n (radialSubdivisionUpper i) := by
  apply Subtype.ext
  simp [radialSubdivisionArc, radialSubdivisionPoint, radialSubdivisionUpper,
    closedUnitIntervalFinish]
  ring

/-- A grid vertex in the radial parameter cylinder. -/
def cylinderSubdivisionPoint (n m : ℕ)
    (i : Fin (n + 2)) (j : Fin (m + 1)) : ClosedUnitInterval × UnitAddCircle :=
  (radialSubdivisionPoint n i, angularSubdivisionPoint m j)

/-- A horizontal angular edge in the radial parameter cylinder. -/
def cylinderAngularEdgePath (n m : ℕ)
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    ClosedUnitInterval → ClosedUnitInterval × UnitAddCircle :=
  fun x ↦ (radialSubdivisionPoint n i, angularSubdivisionArc m j x)

theorem continuous_cylinderAngularEdgePath (n m : ℕ)
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    Continuous (cylinderAngularEdgePath n m i j) := by
  exact continuous_const.prodMk (continuous_angularSubdivisionArc m j)

theorem cylinderAngularEdgePath_start (n m : ℕ)
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    cylinderAngularEdgePath n m i j closedUnitIntervalStart =
      cylinderSubdivisionPoint n m i j := by
  simp [cylinderAngularEdgePath, cylinderSubdivisionPoint, angularSubdivisionArc_start]

theorem cylinderAngularEdgePath_finish (n m : ℕ)
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    cylinderAngularEdgePath n m i j closedUnitIntervalFinish =
      cylinderSubdivisionPoint n m i (cyclicSucc j) := by
  simp [cylinderAngularEdgePath, cylinderSubdivisionPoint, angularSubdivisionArc_finish]

/-- A vertical radial edge in the radial parameter cylinder. -/
def cylinderRadialEdgePath (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    ClosedUnitInterval → ClosedUnitInterval × UnitAddCircle :=
  fun x ↦ (radialSubdivisionArc n i x, angularSubdivisionPoint m j)

theorem continuous_cylinderRadialEdgePath (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Continuous (cylinderRadialEdgePath n m i j) := by
  exact (continuous_radialSubdivisionArc n i).prodMk continuous_const

theorem cylinderRadialEdgePath_start (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    cylinderRadialEdgePath n m i j closedUnitIntervalStart =
      cylinderSubdivisionPoint n m (radialSubdivisionLower i) j := by
  simp [cylinderRadialEdgePath, cylinderSubdivisionPoint, radialSubdivisionArc_start]

theorem cylinderRadialEdgePath_finish (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    cylinderRadialEdgePath n m i j closedUnitIntervalFinish =
      cylinderSubdivisionPoint n m (radialSubdivisionUpper i) j := by
  simp [cylinderRadialEdgePath, cylinderSubdivisionPoint, radialSubdivisionArc_finish]

/-- A diagonal edge across one parameter-space cell. -/
def cylinderDiagonalEdgePath (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    ClosedUnitInterval → ClosedUnitInterval × UnitAddCircle :=
  fun x ↦ (radialSubdivisionArc n i x, angularSubdivisionArc m j x)

theorem continuous_cylinderDiagonalEdgePath (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    Continuous (cylinderDiagonalEdgePath n m i j) := by
  exact (continuous_radialSubdivisionArc n i).prodMk (continuous_angularSubdivisionArc m j)

theorem cylinderDiagonalEdgePath_start (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    cylinderDiagonalEdgePath n m i j closedUnitIntervalStart =
      cylinderSubdivisionPoint n m (radialSubdivisionLower i) j := by
  simp [cylinderDiagonalEdgePath, cylinderSubdivisionPoint, radialSubdivisionArc_start,
    angularSubdivisionArc_start]

theorem cylinderDiagonalEdgePath_finish (n m : ℕ)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    cylinderDiagonalEdgePath n m i j closedUnitIntervalFinish =
      cylinderSubdivisionPoint n m (radialSubdivisionUpper i) (cyclicSucc j) := by
  simp [cylinderDiagonalEdgePath, cylinderSubdivisionPoint, radialSubdivisionArc_finish,
    angularSubdivisionArc_finish]

/-- Core grid vertices for the checkerboard cylinder mesh. -/
abbrev CylinderCoreVertex (n m : ℕ) := Fin (n + 2) × Fin (m + 1)

/-- Directed core edges for the checkerboard cylinder mesh.  We keep both
orientations of the radial and angular grid segments because the finite
obstruction theorem records an oriented cyclic boundary for each face. -/
inductive CylinderCoreEdge (n m : ℕ) : Type
  | radialUp : Fin (n + 1) → Fin (m + 1) → CylinderCoreEdge n m
  | radialDown : Fin (n + 1) → Fin (m + 1) → CylinderCoreEdge n m
  | angularForward : Fin (n + 2) → Fin (m + 1) → CylinderCoreEdge n m
  | angularBackward : Fin (n + 2) → Fin (m + 1) → CylinderCoreEdge n m
  deriving DecidableEq, Fintype

/-- Core faces of the checkerboard cylinder mesh, indexed by the rectangular
parameter cells.  Their cyclic order alternates with the parity of `i + j` so
that adjacent faces can share the same oriented edge objects. -/
abbrev CylinderCoreFace (n m : ℕ) := Fin (n + 1) × Fin (m + 1)

def cylinderCoreFaceEven {n m : ℕ} (f : CylinderCoreFace n m) : Prop :=
  Even (f.1.1 + f.2.1)

def cylinderCoreFaceParity {n m : ℕ} (f : CylinderCoreFace n m) : Bool :=
  decide (Even (f.1.1 + f.2.1))

instance cylinderCoreFaceEvenDecidable {n m : ℕ} (f : CylinderCoreFace n m) :
    Decidable (cylinderCoreFaceEven f) := by
  unfold cylinderCoreFaceEven
  infer_instance

def cylinderCoreLL {n m : ℕ} (f : CylinderCoreFace n m) : CylinderCoreVertex n m :=
  (radialSubdivisionLower f.1, f.2)

def cylinderCoreUL {n m : ℕ} (f : CylinderCoreFace n m) : CylinderCoreVertex n m :=
  (radialSubdivisionUpper f.1, f.2)

def cylinderCoreLR {n m : ℕ} (f : CylinderCoreFace n m) : CylinderCoreVertex n m :=
  (radialSubdivisionLower f.1, cyclicSucc f.2)

def cylinderCoreUR {n m : ℕ} (f : CylinderCoreFace n m) : CylinderCoreVertex n m :=
  (radialSubdivisionUpper f.1, cyclicSucc f.2)

def cylinderCoreEdgeEnds {n m : ℕ} :
    CylinderCoreEdge n m → CylinderCoreVertex n m × CylinderCoreVertex n m
  | .radialUp i j => ((radialSubdivisionLower i, j), (radialSubdivisionUpper i, j))
  | .radialDown i j => ((radialSubdivisionUpper i, j), (radialSubdivisionLower i, j))
  | .angularForward i j => ((i, j), (i, cyclicSucc j))
  | .angularBackward i j => ((i, cyclicSucc j), (i, j))

def cylinderCoreFaceVertex {n m : ℕ} (f : CylinderCoreFace n m) :
    Fin (3 + 1) → CylinderCoreVertex n m :=
  if cylinderCoreFaceParity f then
    fun k =>
      match k.1 with
      | 0 => cylinderCoreLL f
      | 1 => cylinderCoreUL f
      | 2 => cylinderCoreUR f
      | _ => cylinderCoreLR f
  else
    fun k =>
      match k.1 with
      | 0 => cylinderCoreUL f
      | 1 => cylinderCoreLL f
      | 2 => cylinderCoreLR f
      | _ => cylinderCoreUR f

def cylinderCoreFaceEdge {n m : ℕ} (f : CylinderCoreFace n m) :
    Fin (3 + 1) → CylinderCoreEdge n m :=
  if cylinderCoreFaceParity f then
    fun k =>
      match k.1 with
      | 0 => .radialUp f.1 f.2
      | 1 => .angularForward (radialSubdivisionUpper f.1) f.2
      | 2 => .radialDown f.1 (cyclicSucc f.2)
      | _ => .angularBackward (radialSubdivisionLower f.1) f.2
  else
    fun k =>
      match k.1 with
      | 0 => .radialDown f.1 f.2
      | 1 => .angularForward (radialSubdivisionLower f.1) f.2
      | 2 => .radialUp f.1 (cyclicSucc f.2)
      | _ => .angularBackward (radialSubdivisionUpper f.1) f.2

theorem cylinderCoreFaceParity_eq_true_iff {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceParity f = true ↔ cylinderCoreFaceEven f := by
  unfold cylinderCoreFaceParity cylinderCoreFaceEven
  by_cases h : Even (f.1.1 + f.2.1) <;> simp [h]

theorem cylinderCoreFaceParity_eq_false_iff {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceParity f = false ↔ ¬ cylinderCoreFaceEven f := by
  unfold cylinderCoreFaceParity cylinderCoreFaceEven
  by_cases h : Even (f.1.1 + f.2.1) <;> simp [h]

@[simp] theorem cylinderCoreFaceVertex_zero {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceVertex f 0 =
      if cylinderCoreFaceEven f then cylinderCoreLL f else cylinderCoreUL f := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]

@[simp] theorem cylinderCoreFaceVertex_one {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceVertex f 1 =
      if cylinderCoreFaceEven f then cylinderCoreUL f else cylinderCoreLL f := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]

@[simp] theorem cylinderCoreFaceVertex_two {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceVertex f 2 =
      if cylinderCoreFaceEven f then cylinderCoreUR f else cylinderCoreLR f := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]

@[simp] theorem cylinderCoreFaceVertex_three {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceVertex f 3 =
      if cylinderCoreFaceEven f then cylinderCoreLR f else cylinderCoreUR f := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceVertex, hp, h]

@[simp] theorem cylinderCoreFaceEdge_zero {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceEdge f 0 =
      if cylinderCoreFaceEven f then CylinderCoreEdge.radialUp f.1 f.2 else CylinderCoreEdge.radialDown f.1 f.2 := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]

@[simp] theorem cylinderCoreFaceEdge_one {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceEdge f 1 =
      if cylinderCoreFaceEven f then CylinderCoreEdge.angularForward (radialSubdivisionUpper f.1) f.2
      else CylinderCoreEdge.angularForward (radialSubdivisionLower f.1) f.2 := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]

@[simp] theorem cylinderCoreFaceEdge_two {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceEdge f 2 =
      if cylinderCoreFaceEven f then CylinderCoreEdge.radialDown f.1 (cyclicSucc f.2)
      else CylinderCoreEdge.radialUp f.1 (cyclicSucc f.2) := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]

@[simp] theorem cylinderCoreFaceEdge_three {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceEdge f 3 =
      if cylinderCoreFaceEven f then CylinderCoreEdge.angularBackward (radialSubdivisionLower f.1) f.2
      else CylinderCoreEdge.angularBackward (radialSubdivisionUpper f.1) f.2 := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderCoreFaceEdge, hp, h]

def cylinderCoreFaceEdges {n m : ℕ} (f : CylinderCoreFace n m) :
    Finset (CylinderCoreEdge n m) :=
  Finset.univ.image (cylinderCoreFaceEdge f)

theorem cylinderCoreFaceEdges_eq {n m : ℕ} (f : CylinderCoreFace n m) :
    cylinderCoreFaceEdges f = Finset.univ.image (cylinderCoreFaceEdge f) := rfl

theorem cylinderCoreFaceEdge_ends {n m : ℕ} (f : CylinderCoreFace n m)
    (k : Fin (3 + 1)) :
    cylinderCoreEdgeEnds (cylinderCoreFaceEdge f k) =
      (cylinderCoreFaceVertex f k, cylinderCoreFaceVertex f (cyclicSucc k)) := by
  by_cases h : cylinderCoreFaceEven f
  · have hp : cylinderCoreFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    fin_cases k <;>
      simp [cylinderCoreEdgeEnds, cylinderCoreFaceEdge, cylinderCoreFaceVertex,
        cylinderCoreLL, cylinderCoreUL, cylinderCoreUR, cylinderCoreLR, hp, cyclicSucc]
  · have hp : cylinderCoreFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    fin_cases k <;>
      simp [cylinderCoreEdgeEnds, cylinderCoreFaceEdge, cylinderCoreFaceVertex,
        cylinderCoreLL, cylinderCoreUL, cylinderCoreUR, cylinderCoreLR, hp, cyclicSucc]

theorem radialSubdivisionLower_ne_upper {n : ℕ} (i : Fin (n + 1)) :
    radialSubdivisionLower i ≠ radialSubdivisionUpper i := by
  intro h
  have hval := congrArg Fin.val h
  simp [radialSubdivisionLower, radialSubdivisionUpper] at hval

theorem radialSubdivisionUpper_ne_lower {n : ℕ} (i : Fin (n + 1)) :
    radialSubdivisionUpper i ≠ radialSubdivisionLower i := by
  intro h
  exact radialSubdivisionLower_ne_upper i h.symm

theorem cyclicSucc_ne_self_of_pos {m : ℕ} (hm : 0 < m) (j : Fin (m + 1)) :
    cyclicSucc j ≠ j := by
  intro h
  by_cases hj : j = Fin.last m
  · subst hj
    have hval := congrArg Fin.val h
    rw [cyclicSucc_last] at hval
    simp at hval
    omega
  · have hval := congrArg Fin.val h
    rw [cyclicSucc_val_of_ne_last j hj] at hval
    omega

theorem self_ne_cyclicSucc_of_pos {m : ℕ} (hm : 0 < m) (j : Fin (m + 1)) :
    j ≠ cyclicSucc j := by
  intro h
  exact cyclicSucc_ne_self_of_pos hm j h.symm

theorem cylinderCoreFaceVertex_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : CylinderCoreFace n m) :
    Function.Injective (cylinderCoreFaceVertex f) := by
  have hlu : radialSubdivisionLower f.1 ≠ radialSubdivisionUpper f.1 :=
    radialSubdivisionLower_ne_upper f.1
  have hul : radialSubdivisionUpper f.1 ≠ radialSubdivisionLower f.1 :=
    radialSubdivisionUpper_ne_lower f.1
  have hsu : cyclicSucc f.2 ≠ f.2 := cyclicSucc_ne_self_of_pos hm f.2
  have hus : f.2 ≠ cyclicSucc f.2 := self_ne_cyclicSucc_of_pos hm f.2
  intro a b h
  by_cases hpar : cylinderCoreFaceEven f
  · fin_cases a <;> fin_cases b <;>
      simp [cylinderCoreLL, cylinderCoreUL, cylinderCoreUR, cylinderCoreLR,
        hpar, hlu, hul, hsu, hus] at h ⊢
  · fin_cases a <;> fin_cases b <;>
      simp [cylinderCoreLL, cylinderCoreUL, cylinderCoreUR, cylinderCoreLR,
        hpar, hlu, hul, hsu, hus] at h ⊢

theorem cylinderCoreFaceEdge_injective {n m : ℕ} (f : CylinderCoreFace n m) :
    Function.Injective (cylinderCoreFaceEdge f) := by
  intro a b h
  by_cases hpar : cylinderCoreFaceEven f
  · fin_cases a <;> fin_cases b <;>
      simp [hpar] at h ⊢
  · fin_cases a <;> fin_cases b <;>
      simp [hpar] at h ⊢

def cylinderCoreBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) : CylinderCoreVertex n m :=
  (Fin.last (n + 1), j)

def cylinderCoreBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) : CylinderCoreEdge n m :=
  .angularForward (Fin.last (n + 1)) j

theorem cylinderCoreBoundaryEdge_injective {n m : ℕ} :
    Function.Injective (cylinderCoreBoundaryEdge (n := n) (m := m)) := by
  intro a b h
  simpa [cylinderCoreBoundaryEdge] using h

def cylinderCoreBoundaryEdges {n m : ℕ} : Finset (CylinderCoreEdge n m) :=
  Finset.univ.image (cylinderCoreBoundaryEdge (n := n) (m := m))

theorem cylinderCoreBoundaryEdges_eq {n m : ℕ} :
    cylinderCoreBoundaryEdges (n := n) (m := m) =
      Finset.univ.image (cylinderCoreBoundaryEdge (n := n) (m := m)) := rfl

theorem cylinderCoreBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    cylinderCoreEdgeEnds (cylinderCoreBoundaryEdge (n := n) (m := m) j) =
      (cylinderCoreBoundaryVertex (n := n) (m := m) j,
        cylinderCoreBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [cylinderCoreBoundaryEdge, cylinderCoreBoundaryVertex, cylinderCoreEdgeEnds]

theorem complexSupNorm_le_norm (z : ℂ) : complexSupNorm z ≤ ‖z‖ := by
  rw [complexSupNorm]
  exact max_le (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)

theorem complexSupNorm_real_smul (r : ℝ) (z : ℂ) :
    complexSupNorm (r • z) = |r| * complexSupNorm z := by
  rw [complexSupNorm, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul, abs_mul, abs_mul]
  simpa [complexSupNorm, mul_comm, mul_left_comm, mul_assoc] using
    (max_mul_of_nonneg |z.re| |z.im| (abs_nonneg r)).symm

theorem complexSupNorm_ofReal_mul (r : ℝ) (z : ℂ) :
    complexSupNorm (Complex.ofReal r * z) = |r| * complexSupNorm z := by
  simpa [smul_eq_mul] using complexSupNorm_real_smul r z


/-- The center point of the closed unit square. -/
def closedUnitSquareCenter : ClosedUnitSquare := ⟨0, by simp [complexSupNorm]⟩

/-- Radial scaling inside the closed unit square. -/
def closedUnitSquareScale (r : ClosedUnitInterval) (z : ClosedUnitSquare) : ClosedUnitSquare := by
  refine ⟨Complex.ofReal (r : ℝ) * (z : ℂ), ?_⟩
  have hr0 : 0 ≤ (r : ℝ) := r.2.1
  have hr1 : (r : ℝ) ≤ 1 := r.2.2
  rw [complexSupNorm_ofReal_mul, abs_of_nonneg hr0]
  nlinarith [z.2, complexSupNorm_nonneg (z : ℂ)]

theorem continuous_closedUnitSquareScale :
    Continuous fun p : ClosedUnitInterval × ClosedUnitSquare => closedUnitSquareScale p.1 p.2 := by
  have hbase : Continuous fun p : ClosedUnitInterval × ClosedUnitSquare =>
      Complex.ofReal ((p.1 : ClosedUnitInterval) : ℝ) * ((p.2 : ClosedUnitSquare) : ℂ) := by
    exact (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)
  have hcont : Continuous fun p : ClosedUnitInterval × ClosedUnitSquare =>
      ((⟨Complex.ofReal ((p.1 : ClosedUnitInterval) : ℝ) * ((p.2 : ClosedUnitSquare) : ℂ), by
          have hr0 : 0 ≤ ((p.1 : ClosedUnitInterval) : ℝ) := p.1.2.1
          have hr1 : ((p.1 : ClosedUnitInterval) : ℝ) ≤ 1 := p.1.2.2
          rw [complexSupNorm_ofReal_mul, abs_of_nonneg hr0]
          nlinarith [p.2.2, complexSupNorm_nonneg ((p.2 : ClosedUnitSquare) : ℂ)]⟩) : ClosedUnitSquare) := by
    exact hbase.subtype_mk fun p => by
      have hr0 : 0 ≤ ((p.1 : ClosedUnitInterval) : ℝ) := p.1.2.1
      have hr1 : ((p.1 : ClosedUnitInterval) : ℝ) ≤ 1 := p.1.2.2
      rw [complexSupNorm_ofReal_mul, abs_of_nonneg hr0]
      nlinarith [p.2.2, complexSupNorm_nonneg ((p.2 : ClosedUnitSquare) : ℂ)]
  have hEq : (fun p : ClosedUnitInterval × ClosedUnitSquare => closedUnitSquareScale p.1 p.2) =
      fun p : ClosedUnitInterval × ClosedUnitSquare =>
        ((⟨Complex.ofReal ((p.1 : ClosedUnitInterval) : ℝ) * ((p.2 : ClosedUnitSquare) : ℂ), by
            have hr0 : 0 ≤ ((p.1 : ClosedUnitInterval) : ℝ) := p.1.2.1
            have hr1 : ((p.1 : ClosedUnitInterval) : ℝ) ≤ 1 := p.1.2.2
            rw [complexSupNorm_ofReal_mul, abs_of_nonneg hr0]
            nlinarith [p.2.2, complexSupNorm_nonneg ((p.2 : ClosedUnitSquare) : ℂ)]⟩) : ClosedUnitSquare) := by
    funext p
    rfl
  rw [hEq]
  exact hcont

/-- The radial filling of the closed unit square, obtained by scaling the square
boundary toward the center. -/
def closedUnitSquareRadial (p : ClosedUnitInterval × UnitAddCircle) : ClosedUnitSquare :=
  closedUnitSquareScale p.1 (closedUnitSquareBoundary p.2)

theorem continuous_closedUnitSquareRadial : Continuous closedUnitSquareRadial := by
  have hpair : Continuous fun p : ClosedUnitInterval × UnitAddCircle =>
      (p.1, closedUnitSquareBoundary p.2) :=
    continuous_fst.prodMk (continuous_closedUnitSquareBoundary.comp continuous_snd)
  simpa [closedUnitSquareRadial] using continuous_closedUnitSquareScale.comp hpair

theorem closedUnitSquareScale_start (z : ClosedUnitSquare) :
    closedUnitSquareScale closedUnitIntervalStart z = closedUnitSquareCenter := by
  apply Subtype.ext
  change Complex.ofReal ((closedUnitIntervalStart : ClosedUnitInterval) : ℝ) * (z : ℂ) = 0
  norm_num [closedUnitIntervalStart]

theorem closedUnitSquareScale_finish (z : ClosedUnitSquare) :
    closedUnitSquareScale closedUnitIntervalFinish z = z := by
  apply Subtype.ext
  change Complex.ofReal ((closedUnitIntervalFinish : ClosedUnitInterval) : ℝ) * (z : ℂ) = (z : ℂ)
  norm_num [closedUnitIntervalFinish]

theorem closedUnitSquareRadial_start (t : UnitAddCircle) :
    closedUnitSquareRadial (closedUnitIntervalStart, t) = closedUnitSquareCenter := by
  simp [closedUnitSquareRadial, closedUnitSquareScale_start]

theorem closedUnitSquareRadial_finish (t : UnitAddCircle) :
    closedUnitSquareRadial (closedUnitIntervalFinish, t) = closedUnitSquareBoundary t := by
  simp [closedUnitSquareRadial, closedUnitSquareScale_finish]

/-- The outer boundary circle of the radial square parameter cylinder. -/
def closedUnitSquareCylinderBoundary (t : UnitAddCircle) :
    ClosedUnitInterval × UnitAddCircle :=
  (closedUnitIntervalFinish, t)

theorem continuous_closedUnitSquareCylinderBoundary :
    Continuous closedUnitSquareCylinderBoundary := by
  simpa [closedUnitSquareCylinderBoundary] using
    (continuous_const.prodMk continuous_id)

theorem cylinderAngularEdgePath_on_closedUnitSquareCylinderBoundary
    (n m : ℕ) (j : Fin (m + 1)) (x : ClosedUnitInterval) :
    cylinderAngularEdgePath n m (Fin.last (n + 1)) j x =
      closedUnitSquareCylinderBoundary (angularSubdivisionArc m j x) := by
  simp [cylinderAngularEdgePath, closedUnitSquareCylinderBoundary, radialSubdivisionPoint_last]

theorem closedUnitSquareRadial_comp_cylinderBoundary :
    closedUnitSquareBoundary =
      closedUnitSquareRadial ∘ closedUnitSquareCylinderBoundary := by
  funext t
  exact (closedUnitSquareRadial_finish t).symm

/-- The lower positive radial level in the disk-like square mesh. -/
def lowerSquareRingLevel {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self _)⟩

/-- The upper positive radial level in the disk-like square mesh. -/
def upperSquareRingLevel {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp] theorem radialSubdivisionLower_upperSquareRingLevel {n : ℕ} (i : Fin n) :
    radialSubdivisionLower (upperSquareRingLevel i) =
      radialSubdivisionUpper (lowerSquareRingLevel i) := by
  apply Fin.ext
  simp [radialSubdivisionLower, radialSubdivisionUpper,
    lowerSquareRingLevel, upperSquareRingLevel]

/-- Vertices of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskVertex (n m : ℕ)
  | center
  | ring (i : Fin (n + 1)) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Edges of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskEdge (n m : ℕ)
  | spokeOut (j : Fin (m + 1))
  | spokeIn (j : Fin (m + 1))
  | radialOut (i : Fin n) (j : Fin (m + 1))
  | radialIn (i : Fin n) (j : Fin (m + 1))
  | angularForward (i : Fin (n + 1)) (j : Fin (m + 1))
  | angularBackward (i : Fin (n + 1)) (j : Fin (m + 1))
  | diagonalUp (i : Fin n) (j : Fin (m + 1))
  | diagonalDown (i : Fin n) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Faces of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskFace (n m : ℕ)
  | center (j : Fin (m + 1))
  | lower (i : Fin n) (j : Fin (m + 1))
  | upper (i : Fin n) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Reverse the unit interval parameter. -/
def reverseClosedUnitInterval (x : ClosedUnitInterval) : ClosedUnitInterval := by
  refine ⟨1 - (x : ℝ), ?_⟩
  constructor <;> nlinarith [x.2.1, x.2.2]

@[simp] theorem reverseClosedUnitInterval_start :
    reverseClosedUnitInterval closedUnitIntervalStart = closedUnitIntervalFinish := by
  apply Subtype.ext
  simp [reverseClosedUnitInterval, closedUnitIntervalStart, closedUnitIntervalFinish]

@[simp] theorem reverseClosedUnitInterval_finish :
    reverseClosedUnitInterval closedUnitIntervalFinish = closedUnitIntervalStart := by
  apply Subtype.ext
  simp [reverseClosedUnitInterval, closedUnitIntervalStart, closedUnitIntervalFinish]

theorem continuous_reverseClosedUnitInterval :
    Continuous reverseClosedUnitInterval := by
  have hbase : Continuous fun x : ClosedUnitInterval => (1 : ℝ) - (x : ℝ) :=
    continuous_const.sub continuous_subtype_val
  have hcont : Continuous fun x : ClosedUnitInterval =>
      ((⟨1 - (x : ℝ), by
          constructor <;> nlinarith [x.2.1, x.2.2]⟩) : ClosedUnitInterval) := by
    exact hbase.subtype_mk fun x => by
      constructor <;> nlinarith [x.2.1, x.2.2]
  have hEq : reverseClosedUnitInterval = fun x : ClosedUnitInterval =>
      ((⟨1 - (x : ℝ), by
          constructor <;> nlinarith [x.2.1, x.2.2]⟩) : ClosedUnitInterval) := by
    funext x
    rfl
  rw [hEq]
  exact hcont

/-- Edge paths for the checkerboard cylinder mesh. -/
def cylinderCoreEdgePath (n m : ℕ) :
    CylinderCoreEdge n m → ClosedUnitInterval → ClosedUnitInterval × UnitAddCircle
  | .radialUp i j => cylinderRadialEdgePath n m i j
  | .radialDown i j => cylinderRadialEdgePath n m i j ∘ reverseClosedUnitInterval
  | .angularForward i j => cylinderAngularEdgePath n m i j
  | .angularBackward i j => cylinderAngularEdgePath n m i j ∘ reverseClosedUnitInterval

theorem continuous_cylinderCoreEdgePath (n m : ℕ) (e : CylinderCoreEdge n m) :
    Continuous (cylinderCoreEdgePath n m e) := by
  cases e with
  | radialUp i j =>
      exact continuous_cylinderRadialEdgePath n m i j
  | radialDown i j =>
      exact (continuous_cylinderRadialEdgePath n m i j).comp continuous_reverseClosedUnitInterval
  | angularForward i j =>
      exact continuous_cylinderAngularEdgePath n m i j
  | angularBackward i j =>
      exact (continuous_cylinderAngularEdgePath n m i j).comp continuous_reverseClosedUnitInterval

theorem cylinderCoreEdgePath_start {n m : ℕ} (e : CylinderCoreEdge n m) :
    cylinderCoreEdgePath n m e closedUnitIntervalStart =
      cylinderSubdivisionPoint n m (cylinderCoreEdgeEnds e).1.1 (cylinderCoreEdgeEnds e).1.2 := by
  cases e with
  | radialUp i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, cylinderRadialEdgePath_start, cylinderSubdivisionPoint]
  | radialDown i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, reverseClosedUnitInterval_start,
        cylinderRadialEdgePath_finish, cylinderSubdivisionPoint]
  | angularForward i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, cylinderAngularEdgePath_start, cylinderSubdivisionPoint]
  | angularBackward i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, reverseClosedUnitInterval_start,
        cylinderAngularEdgePath_finish, cylinderSubdivisionPoint]

theorem cylinderCoreEdgePath_finish {n m : ℕ} (e : CylinderCoreEdge n m) :
    cylinderCoreEdgePath n m e closedUnitIntervalFinish =
      cylinderSubdivisionPoint n m (cylinderCoreEdgeEnds e).2.1 (cylinderCoreEdgeEnds e).2.2 := by
  cases e with
  | radialUp i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, cylinderRadialEdgePath_finish, cylinderSubdivisionPoint]
  | radialDown i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, reverseClosedUnitInterval_finish,
        cylinderRadialEdgePath_start, cylinderSubdivisionPoint]
  | angularForward i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, cylinderAngularEdgePath_finish, cylinderSubdivisionPoint]
  | angularBackward i j =>
      simp [cylinderCoreEdgePath, cylinderCoreEdgeEnds, reverseClosedUnitInterval_finish,
        cylinderAngularEdgePath_start, cylinderSubdivisionPoint]

@[simp] theorem cylinderCoreBoundaryEdgePath_eq {n m : ℕ} (j : Fin (m + 1)) :
    cylinderCoreEdgePath n m (cylinderCoreBoundaryEdge (n := n) (m := m) j) =
      fun x ↦ closedUnitSquareCylinderBoundary (angularSubdivisionArc m j x) := by
  funext x
  simp [cylinderCoreEdgePath, cylinderCoreBoundaryEdge, cylinderAngularEdgePath,
    closedUnitSquareCylinderBoundary, radialSubdivisionPoint_last]


/-- Vertex locations in the closed unit square. -/
def squareDiskVertexPoint (n m : ℕ) : SquareDiskVertex n m → ClosedUnitSquare
  | .center => closedUnitSquareCenter
  | .ring i j =>
      closedUnitSquareRadial
        (radialSubdivisionPoint n (radialSubdivisionUpper i), angularSubdivisionPoint m j)

@[simp] theorem squareDiskVertexPoint_center (n m : ℕ) :
    squareDiskVertexPoint n m .center = closedUnitSquareCenter := rfl

@[simp] theorem squareDiskVertexPoint_ring (n m : ℕ) (i : Fin (n + 1)) (j : Fin (m + 1)) :
    squareDiskVertexPoint n m (.ring i j) =
      closedUnitSquareRadial
        (radialSubdivisionPoint n (radialSubdivisionUpper i), angularSubdivisionPoint m j) := rfl

/-- Edge endpoints in the disk-like radial mesh. -/
def squareDiskEdgeEnds {n m : ℕ} : SquareDiskEdge n m → SquareDiskVertex n m × SquareDiskVertex n m
  | .spokeOut j => (.center, .ring 0 j)
  | .spokeIn j => (.ring 0 j, .center)
  | .radialOut i j => (.ring (lowerSquareRingLevel i) j, .ring (upperSquareRingLevel i) j)
  | .radialIn i j => (.ring (upperSquareRingLevel i) j, .ring (lowerSquareRingLevel i) j)
  | .angularForward i j => (.ring i j, .ring i (cyclicSucc j))
  | .angularBackward i j => (.ring i (cyclicSucc j), .ring i j)
  | .diagonalUp i j => (.ring (lowerSquareRingLevel i) j, .ring (upperSquareRingLevel i) (cyclicSucc j))
  | .diagonalDown i j => (.ring (upperSquareRingLevel i) (cyclicSucc j), .ring (lowerSquareRingLevel i) j)

/-- Edge paths in the closed unit square. -/
def squareDiskEdgePath (n m : ℕ) : SquareDiskEdge n m → ClosedUnitInterval → ClosedUnitSquare
  | .spokeOut j =>
      fun x ↦ closedUnitSquareRadial (radialSubdivisionArc n 0 x, angularSubdivisionPoint m j)
  | .spokeIn j =>
      fun x ↦ closedUnitSquareRadial (radialSubdivisionArc n 0 (reverseClosedUnitInterval x), angularSubdivisionPoint m j)
  | .radialOut i j =>
      fun x ↦ closedUnitSquareRadial (cylinderRadialEdgePath n m (upperSquareRingLevel i) j x)
  | .radialIn i j =>
      fun x ↦ closedUnitSquareRadial (cylinderRadialEdgePath n m (upperSquareRingLevel i) j (reverseClosedUnitInterval x))
  | .angularForward i j =>
      fun x ↦ closedUnitSquareRadial (cylinderAngularEdgePath n m (radialSubdivisionUpper i) j x)
  | .angularBackward i j =>
      fun x ↦ closedUnitSquareRadial (cylinderAngularEdgePath n m (radialSubdivisionUpper i) j (reverseClosedUnitInterval x))
  | .diagonalUp i j =>
      fun x ↦ closedUnitSquareRadial (cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j x)
  | .diagonalDown i j =>
      fun x ↦ closedUnitSquareRadial (cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j (reverseClosedUnitInterval x))

theorem continuous_squareDiskEdgePath (n m : ℕ) (e : SquareDiskEdge n m) :
    Continuous (squareDiskEdgePath n m e) := by
  cases e with
  | spokeOut j =>
      exact continuous_closedUnitSquareRadial.comp <|
        (continuous_radialSubdivisionArc n 0).prodMk continuous_const
  | spokeIn j =>
      exact continuous_closedUnitSquareRadial.comp <|
        ((continuous_radialSubdivisionArc n 0).comp continuous_reverseClosedUnitInterval).prodMk continuous_const
  | radialOut i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderRadialEdgePath n m (upperSquareRingLevel i) j
  | radialIn i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        (continuous_cylinderRadialEdgePath n m (upperSquareRingLevel i) j).comp continuous_reverseClosedUnitInterval
  | angularForward i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderAngularEdgePath n m (radialSubdivisionUpper i) j
  | angularBackward i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        (continuous_cylinderAngularEdgePath n m (radialSubdivisionUpper i) j).comp continuous_reverseClosedUnitInterval
  | diagonalUp i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j
  | diagonalDown i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        (continuous_cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j).comp continuous_reverseClosedUnitInterval

theorem squareDiskEdgePath_start {n m : ℕ} (e : SquareDiskEdge n m) :
    squareDiskEdgePath n m e closedUnitIntervalStart =
      squareDiskVertexPoint n m (squareDiskEdgeEnds e).1 := by
  cases e with
  | spokeOut j =>
      simpa [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        radialSubdivisionArc_start, radialSubdivisionPoint_zero,
        radialSubdivisionLower] using
        closedUnitSquareRadial_start (angularSubdivisionPoint m j)
  | spokeIn j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_start, radialSubdivisionArc_finish]
  | radialOut i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderRadialEdgePath_start, cylinderSubdivisionPoint,
        radialSubdivisionLower_upperSquareRingLevel]
  | radialIn i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_start, cylinderRadialEdgePath_finish,
        cylinderSubdivisionPoint]
  | angularForward i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderAngularEdgePath_start, cylinderSubdivisionPoint]
  | angularBackward i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_start, cylinderAngularEdgePath_finish,
        cylinderSubdivisionPoint]
  | diagonalUp i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderDiagonalEdgePath_start, cylinderSubdivisionPoint,
        radialSubdivisionLower_upperSquareRingLevel]
  | diagonalDown i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_start, cylinderDiagonalEdgePath_finish,
        cylinderSubdivisionPoint]

theorem squareDiskEdgePath_finish {n m : ℕ} (e : SquareDiskEdge n m) :
    squareDiskEdgePath n m e closedUnitIntervalFinish =
      squareDiskVertexPoint n m (squareDiskEdgeEnds e).2 := by
  cases e with
  | spokeOut j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        radialSubdivisionArc_finish]
  | spokeIn j =>
      simpa [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_finish, radialSubdivisionArc_start,
        radialSubdivisionPoint_zero, radialSubdivisionLower] using
        closedUnitSquareRadial_start (angularSubdivisionPoint m j)
  | radialOut i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderRadialEdgePath_finish, cylinderSubdivisionPoint]
  | radialIn i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_finish, cylinderRadialEdgePath_start,
        cylinderSubdivisionPoint, radialSubdivisionLower_upperSquareRingLevel]
  | angularForward i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderAngularEdgePath_finish, cylinderSubdivisionPoint]
  | angularBackward i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_finish, cylinderAngularEdgePath_start,
        cylinderSubdivisionPoint]
  | diagonalUp i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderDiagonalEdgePath_finish, cylinderSubdivisionPoint]
  | diagonalDown i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        reverseClosedUnitInterval_finish, cylinderDiagonalEdgePath_start,
        cylinderSubdivisionPoint, radialSubdivisionLower_upperSquareRingLevel]

/-- Face vertices of the disk-like radial mesh. -/
def squareDiskFaceVertex {n m : ℕ} : SquareDiskFace n m → Fin (2 + 1) → SquareDiskVertex n m
  | .center j => fun k =>
      match k.1 with
      | 0 => .center
      | 1 => .ring 0 j
      | _ => .ring 0 (cyclicSucc j)
  | .lower i j => fun k =>
      match k.1 with
      | 0 => .ring (lowerSquareRingLevel i) j
      | 1 => .ring (upperSquareRingLevel i) j
      | _ => .ring (upperSquareRingLevel i) (cyclicSucc j)
  | .upper i j => fun k =>
      match k.1 with
      | 0 => .ring (lowerSquareRingLevel i) j
      | 1 => .ring (upperSquareRingLevel i) (cyclicSucc j)
      | _ => .ring (lowerSquareRingLevel i) (cyclicSucc j)

/-- Face edges of the disk-like radial mesh. -/
def squareDiskFaceEdge {n m : ℕ} : SquareDiskFace n m → Fin (2 + 1) → SquareDiskEdge n m
  | .center j => fun k =>
      match k.1 with
      | 0 => .spokeOut j
      | 1 => .angularForward 0 j
      | _ => .spokeIn (cyclicSucc j)
  | .lower i j => fun k =>
      match k.1 with
      | 0 => .radialOut i j
      | 1 => .angularForward (upperSquareRingLevel i) j
      | _ => .diagonalDown i j
  | .upper i j => fun k =>
      match k.1 with
      | 0 => .diagonalUp i j
      | 1 => .radialIn i (cyclicSucc j)
      | _ => .angularBackward (lowerSquareRingLevel i) j

@[simp] theorem squareDiskFaceVertex_zero {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceVertex f 0 =
      match f with
      | .center _ => .center
      | .lower i j => .ring (lowerSquareRingLevel i) j
      | .upper i j => .ring (lowerSquareRingLevel i) j := by
  cases f <;> rfl

@[simp] theorem squareDiskFaceVertex_one {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceVertex f 1 =
      match f with
      | .center j => .ring 0 j
      | .lower i j => .ring (upperSquareRingLevel i) j
      | .upper i j => .ring (upperSquareRingLevel i) (cyclicSucc j) := by
  cases f <;> rfl

@[simp] theorem squareDiskFaceVertex_two {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceVertex f 2 =
      match f with
      | .center j => .ring 0 (cyclicSucc j)
      | .lower i j => .ring (upperSquareRingLevel i) (cyclicSucc j)
      | .upper i j => .ring (lowerSquareRingLevel i) (cyclicSucc j) := by
  cases f <;> rfl

@[simp] theorem squareDiskFaceEdge_zero {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceEdge f 0 =
      match f with
      | .center j => SquareDiskEdge.spokeOut j
      | .lower i j => SquareDiskEdge.radialOut i j
      | .upper i j => SquareDiskEdge.diagonalUp i j := by
  cases f <;> rfl

@[simp] theorem squareDiskFaceEdge_one {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceEdge f 1 =
      match f with
      | .center j => SquareDiskEdge.angularForward 0 j
      | .lower i j => SquareDiskEdge.angularForward (upperSquareRingLevel i) j
      | .upper i j => SquareDiskEdge.radialIn i (cyclicSucc j) := by
  cases f <;> rfl

@[simp] theorem squareDiskFaceEdge_two {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceEdge f 2 =
      match f with
      | .center j => SquareDiskEdge.spokeIn (cyclicSucc j)
      | .lower i j => SquareDiskEdge.diagonalDown i j
      | .upper i j => SquareDiskEdge.angularBackward (lowerSquareRingLevel i) j := by
  cases f <;> rfl

theorem lowerSquareRingLevel_ne_upperSquareRingLevel {n : ℕ} (i : Fin n) :
    lowerSquareRingLevel i ≠ upperSquareRingLevel i := by
  intro h
  have hval := congrArg Fin.val h
  simp [lowerSquareRingLevel, upperSquareRingLevel] at hval

theorem upperSquareRingLevel_ne_lowerSquareRingLevel {n : ℕ} (i : Fin n) :
    upperSquareRingLevel i ≠ lowerSquareRingLevel i := by
  intro h
  exact lowerSquareRingLevel_ne_upperSquareRingLevel i h.symm

theorem squareDiskFaceVertex_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : SquareDiskFace n m) :
    Function.Injective (squareDiskFaceVertex f) := by
  have hcyc₁ (j : Fin (m + 1)) : j ≠ cyclicSucc j := self_ne_cyclicSucc_of_pos hm j
  have hcyc₂ (j : Fin (m + 1)) : cyclicSucc j ≠ j := cyclicSucc_ne_self_of_pos hm j
  have hlevel₁ (i : Fin n) : lowerSquareRingLevel i ≠ upperSquareRingLevel i :=
    lowerSquareRingLevel_ne_upperSquareRingLevel i
  have hlevel₂ (i : Fin n) : upperSquareRingLevel i ≠ lowerSquareRingLevel i :=
    upperSquareRingLevel_ne_lowerSquareRingLevel i
  intro a b h
  cases f with
  | center j =>
      fin_cases a <;> fin_cases b <;> simp [hcyc₁ j, hcyc₂ j] at h ⊢
  | lower i j =>
      fin_cases a <;> fin_cases b <;> simp [hlevel₁ i, hlevel₂ i, hcyc₁ j, hcyc₂ j] at h ⊢
  | upper i j =>
      fin_cases a <;> fin_cases b <;> simp [hlevel₁ i, hlevel₂ i, hcyc₁ j, hcyc₂ j] at h ⊢

theorem squareDiskFaceEdge_injective {n m : ℕ} (f : SquareDiskFace n m) :
    Function.Injective (squareDiskFaceEdge f) := by
  intro a b h
  cases f with
  | center j =>
      fin_cases a <;> fin_cases b <;> simp at h ⊢
  | lower i j =>
      fin_cases a <;> fin_cases b <;> simp at h ⊢
  | upper i j =>
      fin_cases a <;> fin_cases b <;> simp at h ⊢

def squareDiskFaceEdges {n m : ℕ} (f : SquareDiskFace n m) :
    Finset (SquareDiskEdge n m) :=
  Finset.univ.image (squareDiskFaceEdge f)

theorem squareDiskFaceEdges_eq {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceEdges f = Finset.univ.image (squareDiskFaceEdge f) := rfl

theorem squareDiskFaceEdge_ends {n m : ℕ} (f : SquareDiskFace n m)
    (k : Fin (2 + 1)) :
    squareDiskEdgeEnds (squareDiskFaceEdge f k) =
      (squareDiskFaceVertex f k, squareDiskFaceVertex f (cyclicSucc k)) := by
  cases f with
  | center j =>
      fin_cases k <;> simp [squareDiskEdgeEnds, squareDiskFaceEdge, squareDiskFaceVertex, cyclicSucc]
  | lower i j =>
      fin_cases k <;> simp [squareDiskEdgeEnds, squareDiskFaceEdge, squareDiskFaceVertex, cyclicSucc]
  | upper i j =>
      fin_cases k <;> simp [squareDiskEdgeEnds, squareDiskFaceEdge, squareDiskFaceVertex, cyclicSucc]

/-- Boundary vertices of the disk-like radial mesh. -/
def squareDiskBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) : SquareDiskVertex n m :=
  .ring (Fin.last n) j

/-- Boundary edges of the disk-like radial mesh. -/
def squareDiskBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) : SquareDiskEdge n m :=
  .angularForward (Fin.last n) j

@[simp] theorem squareDiskBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    squareDiskEdgeEnds (squareDiskBoundaryEdge (n := n) (m := m) j) =
      (squareDiskBoundaryVertex (n := n) (m := m) j,
        squareDiskBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [squareDiskBoundaryEdge, squareDiskBoundaryVertex, squareDiskEdgeEnds]

@[simp] theorem squareDiskBoundaryEdge_injective {n m : ℕ} :
    Function.Injective (squareDiskBoundaryEdge (n := n) (m := m)) := by
  intro a b h
  simpa [squareDiskBoundaryEdge] using h

def squareDiskBoundaryEdges {n m : ℕ} : Finset (SquareDiskEdge n m) :=
  Finset.univ.image (squareDiskBoundaryEdge (n := n) (m := m))

theorem squareDiskBoundaryEdges_eq {n m : ℕ} :
    squareDiskBoundaryEdges (n := n) (m := m) =
      Finset.univ.image (squareDiskBoundaryEdge (n := n) (m := m)) := rfl

@[simp] theorem squareDiskBoundaryEdgePath_eq {n m : ℕ} (j : Fin (m + 1)) :
    squareDiskEdgePath n m (squareDiskBoundaryEdge (n := n) (m := m) j) =
      fun x ↦ closedUnitSquareRadial
        (cylinderAngularEdgePath n m (Fin.last (n + 1)) j x) := by
  funext x
  rw [squareDiskBoundaryEdge, squareDiskEdgePath]
  exact congrArg (fun i => closedUnitSquareRadial (cylinderAngularEdgePath n m i j x)) <| by
    apply Fin.ext
    simp [radialSubdivisionUpper]

theorem cyclicSucc_even_iff_not_even_of_odd {m : ℕ} (hm : Odd m)
    (j : Fin (m + 1)) :
    Even (cyclicSucc j).1 ↔ ¬ Even j.1 := by
  by_cases hj : j = Fin.last m
  · subst hj
    rw [cyclicSucc_last]
    simpa [Nat.not_even_iff_odd] using hm
  · rw [cyclicSucc_val_of_ne_last j hj]
    simp [Nat.even_add_one]

theorem cyclicSucc_not_even_iff_even_of_odd {m : ℕ} (hm : Odd m)
    (j : Fin (m + 1)) :
    ¬ Even (cyclicSucc j).1 ↔ Even j.1 := by
  rw [cyclicSucc_even_iff_not_even_of_odd hm j]
  exact not_not

/-- Alternating central-triangle vertex order for an even boundary subdivision. -/
def squareDiskCenterFaceVertexAlt {n m : ℕ} (j : Fin (m + 1)) :
    Fin (2 + 1) → SquareDiskVertex n m :=
  if Even j.1 then
    fun k =>
      match k.1 with
      | 0 => .center
      | 1 => .ring 0 j
      | _ => .ring 0 (cyclicSucc j)
  else
    fun k =>
      match k.1 with
      | 0 => .ring 0 j
      | 1 => .center
      | _ => .ring 0 (cyclicSucc j)

/-- Alternating central-triangle edge order for an even boundary subdivision. -/
def squareDiskCenterFaceEdgeAlt {n m : ℕ} (j : Fin (m + 1)) :
    Fin (2 + 1) → SquareDiskEdge n m :=
  if Even j.1 then
    fun k =>
      match k.1 with
      | 0 => .spokeOut j
      | 1 => .angularForward 0 j
      | _ => .spokeIn (cyclicSucc j)
  else
    fun k =>
      match k.1 with
      | 0 => .spokeIn j
      | 1 => .spokeOut (cyclicSucc j)
      | _ => .angularBackward 0 j

@[simp] theorem squareDiskCenterFaceVertexAlt_zero_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 0 = SquareDiskVertex.center := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceVertexAlt_one_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 1 = SquareDiskVertex.ring 0 j := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceVertexAlt_two_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 2 = SquareDiskVertex.ring 0 (cyclicSucc j) := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceVertexAlt_zero_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 0 = SquareDiskVertex.ring 0 j := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceVertexAlt_one_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 1 = SquareDiskVertex.center := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceVertexAlt_two_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceVertexAlt (n := n) j 2 = SquareDiskVertex.ring 0 (cyclicSucc j) := by
  simp [squareDiskCenterFaceVertexAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_zero_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 0 = SquareDiskEdge.spokeOut j := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_one_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 1 = SquareDiskEdge.angularForward 0 j := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_two_even {n m : ℕ} {j : Fin (m + 1)}
    (hj : Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 2 = SquareDiskEdge.spokeIn (cyclicSucc j) := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_zero_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 0 = SquareDiskEdge.spokeIn j := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_one_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 1 = SquareDiskEdge.spokeOut (cyclicSucc j) := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

@[simp] theorem squareDiskCenterFaceEdgeAlt_two_odd {n m : ℕ} {j : Fin (m + 1)}
    (hj : ¬ Even j.1) :
    squareDiskCenterFaceEdgeAlt (n := n) j 2 = SquareDiskEdge.angularBackward 0 j := by
  simp [squareDiskCenterFaceEdgeAlt, hj]

theorem squareDiskCenterFaceVertexAlt_injective_of_odd {n m : ℕ} (hm : Odd m)
    (j : Fin (m + 1)) :
    Function.Injective (squareDiskCenterFaceVertexAlt (n := n) j) := by
  have hcyc₁ : j ≠ cyclicSucc j := by
    have hm' : 0 < m := hm.pos
    exact self_ne_cyclicSucc_of_pos hm' j
  have hcyc₂ : cyclicSucc j ≠ j := by
    have hm' : 0 < m := hm.pos
    exact cyclicSucc_ne_self_of_pos hm' j
  intro a b h
  by_cases hj : Even j.1
  · fin_cases a <;> fin_cases b <;> simp [squareDiskCenterFaceVertexAlt, hj, hcyc₁, hcyc₂] at h ⊢
  · fin_cases a <;> fin_cases b <;> simp [squareDiskCenterFaceVertexAlt, hj, hcyc₁, hcyc₂] at h ⊢

theorem squareDiskCenterFaceEdgeAlt_injective_of_odd {n m : ℕ} (_hm : Odd m)
    (j : Fin (m + 1)) :
    Function.Injective (squareDiskCenterFaceEdgeAlt (n := n) j) := by
  intro a b h
  by_cases hj : Even j.1
  · fin_cases a <;> fin_cases b <;> simp [squareDiskCenterFaceEdgeAlt, hj] at h ⊢
  · fin_cases a <;> fin_cases b <;> simp [squareDiskCenterFaceEdgeAlt, hj] at h ⊢

theorem squareDiskCenterFaceEdgeAlt_ends_of_odd {n m : ℕ} (_hm : Odd m)
    (j : Fin (m + 1)) (k : Fin (2 + 1)) :
    squareDiskEdgeEnds (squareDiskCenterFaceEdgeAlt (n := n) j k) =
      (squareDiskCenterFaceVertexAlt (n := n) j k,
        squareDiskCenterFaceVertexAlt (n := n) j (cyclicSucc k)) := by
  by_cases hj : Even j.1
  · fin_cases k <;>
      simp [squareDiskCenterFaceEdgeAlt, squareDiskCenterFaceVertexAlt,
        squareDiskEdgeEnds, hj, cyclicSucc]
  · fin_cases k <;>
      simp [squareDiskCenterFaceEdgeAlt, squareDiskCenterFaceVertexAlt,
        squareDiskEdgeEnds, hj, cyclicSucc]

/-- The alternating center-face ordering assembled into a full cyclic vertex
order for the disk-like mesh.  Only the center faces change; the annular
triangles keep the standard order. -/
def squareDiskFaceVertexAlt {n m : ℕ} :
    SquareDiskFace n m → Fin (2 + 1) → SquareDiskVertex n m
  | .center j => squareDiskCenterFaceVertexAlt (n := n) j
  | .lower i j => squareDiskFaceVertex (.lower i j)
  | .upper i j => squareDiskFaceVertex (.upper i j)

/-- The matching alternating cyclic edge order for the disk-like mesh. -/
def squareDiskFaceEdgeAlt {n m : ℕ} :
    SquareDiskFace n m → Fin (2 + 1) → SquareDiskEdge n m
  | .center j => squareDiskCenterFaceEdgeAlt (n := n) j
  | .lower i j => squareDiskFaceEdge (.lower i j)
  | .upper i j => squareDiskFaceEdge (.upper i j)

theorem squareDiskFaceVertexAlt_injective_of_odd {n m : ℕ} (hm : Odd m)
    (f : SquareDiskFace n m) :
    Function.Injective (squareDiskFaceVertexAlt f) := by
  cases f with
  | center j => simpa [squareDiskFaceVertexAlt] using
      squareDiskCenterFaceVertexAlt_injective_of_odd (n := n) hm j
  | lower i j => simpa [squareDiskFaceVertexAlt] using
      squareDiskFaceVertex_injective_of_pos hm.pos (.lower i j)
  | upper i j => simpa [squareDiskFaceVertexAlt] using
      squareDiskFaceVertex_injective_of_pos hm.pos (.upper i j)

theorem squareDiskFaceEdgeAlt_injective_of_odd {n m : ℕ} (hm : Odd m)
    (f : SquareDiskFace n m) :
    Function.Injective (squareDiskFaceEdgeAlt f) := by
  cases f with
  | center j => simpa [squareDiskFaceEdgeAlt] using
      squareDiskCenterFaceEdgeAlt_injective_of_odd (n := n) hm j
  | lower i j => simpa [squareDiskFaceEdgeAlt] using
      squareDiskFaceEdge_injective (.lower i j)
  | upper i j => simpa [squareDiskFaceEdgeAlt] using
      squareDiskFaceEdge_injective (.upper i j)

def squareDiskFaceEdgesAlt {n m : ℕ} (f : SquareDiskFace n m) :
    Finset (SquareDiskEdge n m) :=
  Finset.univ.image (squareDiskFaceEdgeAlt f)

theorem squareDiskFaceEdgesAlt_eq {n m : ℕ} (f : SquareDiskFace n m) :
    squareDiskFaceEdgesAlt f = Finset.univ.image (squareDiskFaceEdgeAlt f) := rfl

theorem squareDiskFaceEdgeAlt_ends_of_odd {n m : ℕ} (hm : Odd m)
    (f : SquareDiskFace n m) (k : Fin (2 + 1)) :
    squareDiskEdgeEnds (squareDiskFaceEdgeAlt f k) =
      (squareDiskFaceVertexAlt f k, squareDiskFaceVertexAlt f (cyclicSucc k)) := by
  cases f with
  | center j => simpa [squareDiskFaceEdgeAlt, squareDiskFaceVertexAlt] using
      squareDiskCenterFaceEdgeAlt_ends_of_odd (n := n) hm j k
  | lower i j => simpa [squareDiskFaceEdgeAlt, squareDiskFaceVertexAlt] using
      squareDiskFaceEdge_ends (.lower i j) k
  | upper i j => simpa [squareDiskFaceEdgeAlt, squareDiskFaceVertexAlt] using
      squareDiskFaceEdge_ends (.upper i j) k

theorem cyclicPred_even_iff_not_even_of_odd {m : ℕ} (hm : Odd m)
    (j : Fin (m + 1)) :
    Even (cyclicPred j).1 ↔ ¬ Even j.1 := by
  simpa using (cyclicSucc_not_even_iff_even_of_odd hm (cyclicPred j)).symm

theorem cyclicPred_not_even_iff_even_of_odd {m : ℕ} (hm : Odd m)
    (j : Fin (m + 1)) :
    ¬ Even (cyclicPred j).1 ↔ Even j.1 := by
  rw [cyclicPred_even_iff_not_even_of_odd hm j]
  exact not_not

theorem mem_squareDiskCenterFaceEdgesAlt_spokeOut_iff
    {n m : ℕ} (k j : Fin (m + 1)) :
    SquareDiskEdge.spokeOut j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k) ↔
      (Even k.1 ∧ k = j) ∨ (¬ Even k.1 ∧ cyclicSucc k = j) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    by_cases hk : Even k.1
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact Or.inl ⟨hk, ht⟩
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact Or.inr ⟨hk, ht⟩
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
  · rintro (⟨hk, rfl⟩ | ⟨hk, hsucc⟩)
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk]⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk, hsucc]⟩

theorem mem_squareDiskCenterFaceEdgesAlt_spokeIn_iff
    {n m : ℕ} (k j : Fin (m + 1)) :
    SquareDiskEdge.spokeIn j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k) ↔
      (¬ Even k.1 ∧ k = j) ∨ (Even k.1 ∧ cyclicSucc k = j) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    by_cases hk : Even k.1
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact Or.inr ⟨hk, ht⟩
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact Or.inl ⟨hk, ht⟩
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
  · rintro (⟨hk, rfl⟩ | ⟨hk, hsucc⟩)
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk]⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk, hsucc]⟩

theorem mem_squareDiskCenterFaceEdgesAlt_angularForward_iff
    {n m : ℕ} (k j : Fin (m + 1)) :
    SquareDiskEdge.angularForward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k) ↔
      Even k.1 ∧ k = j := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    by_cases hk : Even k.1
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact ⟨hk, ht⟩
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
    · fin_cases t <;> simp [squareDiskCenterFaceEdgeAlt, hk] at ht
  · rintro ⟨hk, rfl⟩
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk]⟩

theorem mem_squareDiskCenterFaceEdgesAlt_angularBackward_iff
    {n m : ℕ} (k j : Fin (m + 1)) :
    SquareDiskEdge.angularBackward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k) ↔
      ¬ Even k.1 ∧ k = j := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    by_cases hk : Even k.1
    · fin_cases t <;> simp [squareDiskCenterFaceEdgeAlt, hk] at ht
    · fin_cases t
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
      · simp [squareDiskCenterFaceEdgeAlt, hk] at ht
        exact ⟨hk, ht⟩
  · rintro ⟨hk, rfl⟩
    exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by simp [squareDiskCenterFaceEdgeAlt, hk]⟩

theorem squareDiskCenterFaceAlt_angularForward_faceCount_of_odd
    {n m : ℕ} (_hm : Odd m) (j : Fin (m + 1)) :
    (Finset.univ.filter fun k : Fin (m + 1) ↦
      SquareDiskEdge.angularForward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)).card =
        if Even j.1 then 1 else 0 := by
  by_cases hj : Even j.1
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.angularForward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          ({j} : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [mem_squareDiskCenterFaceEdgesAlt_angularForward_iff]
      constructor
      · rintro ⟨hk, hk'⟩
        simpa [hk'] using hk
      · intro hk
        subst hk
        exact ⟨hj, rfl⟩
    rw [hfilter, if_pos hj]
    simp
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.angularForward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          (∅ : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_squareDiskCenterFaceEdgesAlt_angularForward_iff]
      constructor
      · rintro ⟨hk, hk'⟩
        exact False.elim (hj (by simpa [hk'] using hk))
      · intro hk
        simp at hk
    rw [hfilter, if_neg hj]
    simp

theorem squareDiskCenterFaceAlt_angularBackward_faceCount_of_odd
    {n m : ℕ} (_hm : Odd m) (j : Fin (m + 1)) :
    (Finset.univ.filter fun k : Fin (m + 1) ↦
      SquareDiskEdge.angularBackward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)).card =
        if Even j.1 then 0 else 1 := by
  by_cases hj : Even j.1
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.angularBackward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          (∅ : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_squareDiskCenterFaceEdgesAlt_angularBackward_iff]
      constructor
      · rintro ⟨hk, hk'⟩
        simpa using hk (by simpa [hk'] using hj)
      · intro hk
        simp at hk
    rw [hfilter, if_pos hj]
    simp
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.angularBackward 0 j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          ({j} : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [mem_squareDiskCenterFaceEdgesAlt_angularBackward_iff]
      constructor
      · rintro ⟨hk, hk'⟩
        exact hk'
      · intro hk
        subst hk
        exact ⟨hj, rfl⟩
    rw [hfilter, if_neg hj]
    simp

theorem squareDiskCenterFaceAlt_spokeOut_faceCount_of_odd
    {n m : ℕ} (hm : Odd m) (j : Fin (m + 1)) :
    (Finset.univ.filter fun k : Fin (m + 1) ↦
      SquareDiskEdge.spokeOut j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)).card =
        if Even j.1 then 2 else 0 := by
  by_cases hj : Even j.1
  · have hpred : ¬ Even (cyclicPred j).1 :=
      (cyclicPred_not_even_iff_even_of_odd hm j).2 hj
    have hneq : cyclicPred j ≠ j := by
      intro h
      exact hpred (h.symm ▸ hj)
    have hfilter :
        (Finset.univ.filter fun k : Fin (m + 1) ↦
          SquareDiskEdge.spokeOut j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
            ({j, cyclicPred j} : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hk
        rcases (mem_squareDiskCenterFaceEdgesAlt_spokeOut_iff (n := n) k j).mp hk with h | h
        · exact Or.inl h.2
        · exact Or.inr <| by
            have hsucc := h.2
            apply_fun cyclicPred at hsucc
            simpa using hsucc
      · intro hk
        rcases hk with hk | hk
        · subst k
          exact (mem_squareDiskCenterFaceEdgesAlt_spokeOut_iff (n := n) j j).2 <|
            Or.inl ⟨hj, rfl⟩
        · subst k
          have hsucc : cyclicSucc (cyclicPred j) = j := by simp
          exact (mem_squareDiskCenterFaceEdgesAlt_spokeOut_iff (n := n) (cyclicPred j) j).2 <|
            Or.inr ⟨hpred, hsucc⟩
    rw [hfilter, if_pos hj]
    exact Finset.card_pair hneq.symm
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.spokeOut j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          (∅ : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hk
        rcases (mem_squareDiskCenterFaceEdgesAlt_spokeOut_iff (n := n) k j).mp hk with h | h
        · have : Even j.1 := by simpa [h.2] using h.1
          exact False.elim (hj this)
        · have : Even j.1 := by simpa [← h.2] using (cyclicSucc_even_iff_not_even_of_odd hm k).2 h.1
          exact False.elim (hj this)
      · intro hk
        simp at hk
    rw [hfilter, if_neg hj]
    simp

theorem squareDiskCenterFaceAlt_spokeIn_faceCount_of_odd
    {n m : ℕ} (hm : Odd m) (j : Fin (m + 1)) :
    (Finset.univ.filter fun k : Fin (m + 1) ↦
      SquareDiskEdge.spokeIn j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)).card =
        if Even j.1 then 0 else 2 := by
  by_cases hj : Even j.1
  · have hfilter :
      (Finset.univ.filter fun k : Fin (m + 1) ↦
        SquareDiskEdge.spokeIn j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
          (∅ : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hk
        rcases (mem_squareDiskCenterFaceEdgesAlt_spokeIn_iff (n := n) k j).mp hk with h | h
        · have : Even k.1 := by simpa [h.2] using hj
          exact False.elim (h.1 this)
        · have : ¬ Even j.1 := by simpa [← h.2] using (cyclicSucc_not_even_iff_even_of_odd hm k).2 h.1
          exact False.elim (this hj)
      · intro hk
        simp at hk
    rw [hfilter, if_pos hj]
    simp
  · have hpred : Even (cyclicPred j).1 :=
      (cyclicPred_even_iff_not_even_of_odd hm j).2 hj
    have hneq : cyclicPred j ≠ j := by
      intro h
      exact hj (h.symm ▸ hpred)
    have hfilter :
        (Finset.univ.filter fun k : Fin (m + 1) ↦
          SquareDiskEdge.spokeIn j ∈ Finset.univ.image (squareDiskCenterFaceEdgeAlt (n := n) k)) =
            ({j, cyclicPred j} : Finset (Fin (m + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hk
        rcases (mem_squareDiskCenterFaceEdgesAlt_spokeIn_iff (n := n) k j).mp hk with h | h
        · exact Or.inl h.2
        · exact Or.inr <| by
            have hsucc := h.2
            apply_fun cyclicPred at hsucc
            simpa using hsucc
      · intro hk
        rcases hk with hk | hk
        · subst k
          exact (mem_squareDiskCenterFaceEdgesAlt_spokeIn_iff (n := n) j j).2 <|
            Or.inl ⟨hj, rfl⟩
        · subst k
          have hsucc : cyclicSucc (cyclicPred j) = j := by simp
          exact (mem_squareDiskCenterFaceEdgesAlt_spokeIn_iff (n := n) (cyclicPred j) j).2 <|
            Or.inr ⟨hpred, hsucc⟩
    rw [hfilter, if_neg hj]
    exact Finset.card_pair hneq.symm


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

/-- The odd boundary-degree obstruction transports across any
boundary-respecting continuous map by precomposing the test map. -/
theorem hasOddBoundaryDegreeObstruction_of_comp_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    HasOddBoundaryDegreeObstruction boundary' := by
  intro H hH degree hdegree hodd
  apply hobstruction (H ∘ f) (hH.comp hf) degree
  · simpa [Function.comp_assoc, hboundary] using hdegree
  · exact hodd

/-- The odd boundary-degree obstruction transports across boundary-respecting
homeomorphisms by specializing the continuous-map transport theorem. -/
theorem hasOddBoundaryDegreeObstruction_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    HasOddBoundaryDegreeObstruction boundary' :=
  hasOddBoundaryDegreeObstruction_of_comp_continuous
    e e.continuous_toFun hboundary hobstruction

/-- A boundary map has the odd-degree obstruction as soon as it is nullhomotopic:
if it contracts through a continuous homotopy to a constant loop, then every
continuous circle-valued map on the ambient space restricts to degree zero on
that boundary. -/
theorem hasOddBoundaryDegreeObstruction_of_nullhomotopy
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  let FH : C(I × UnitAddCircle, UnitAddCircle) :=
    ⟨fun p ↦ H (F p), hH.comp F.continuous⟩
  have hFH0 : ∀ t : UnitAddCircle, FH (0, t) = H center := by
    intro t
    simp [FH, hF0]
  have hFH1 : ∀ t : UnitAddCircle, FH (1, t) = H (boundary t) := by
    intro t
    simp [FH, hF1]
  have hzero : HasCircleDegree (H ∘ boundary) 0 :=
    HasCircleDegree.of_homotopy (hasCircleDegree_const (H center)) FH hFH0 hFH1
  have hdeg0 : degree = 0 := HasCircleDegree.unique hdegree hzero
  have hnot : ¬ Odd degree := by
    rw [hdeg0]
    decide
  exact hnot hodd

/-- The standard boundary of the closed unit square has degree zero against every
continuous extension to the whole square, by contracting the boundary to the
center along the radial homotopy. -/
theorem hasOddBoundaryDegreeObstruction_closedUnitSquareBoundary :
    HasOddBoundaryDegreeObstruction closedUnitSquareBoundary := by
  apply hasOddBoundaryDegreeObstruction_of_nullhomotopy closedUnitSquareCenter
    ⟨closedUnitSquareRadial, continuous_closedUnitSquareRadial⟩
  · exact closedUnitSquareRadial_start
  · exact closedUnitSquareRadial_finish

/-- The standard boundary of the closed unit disk inherits the odd boundary-degree
obstruction from the square boundary through the radial square-to-disk map. -/
theorem hasOddBoundaryDegreeObstruction_closedUnitDiskBoundary :
    HasOddBoundaryDegreeObstruction closedUnitDiskBoundary := by
  intro H hH degree hdegree hodd
  have hdegreeSquare :
      HasCircleDegree ((H ∘ closedUnitSquareToDisk) ∘ closedUnitSquareBoundary) degree := by
    simpa [Function.comp_assoc, closedUnitSquareToDisk_comp_boundary] using hdegree
  exact hasOddBoundaryDegreeObstruction_closedUnitSquareBoundary
    (H := H ∘ closedUnitSquareToDisk)
    (hH.comp continuous_closedUnitSquareToDisk)
    degree hdegreeSquare hodd

/-- Any boundary obtained from the closed-disk boundary by a continuous
extension map inherits the odd boundary-degree obstruction directly from the
disk model domain. -/
theorem hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension
    {Y : Type*} [TopologicalSpace Y]
    {boundary : UnitAddCircle → Y}
    (F : ClosedUnitDisk → Y) (hF : Continuous F)
    (hboundary : boundary = F ∘ closedUnitDiskBoundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_comp_continuous
    F hF hboundary hasOddBoundaryDegreeObstruction_closedUnitDiskBoundary

/-- Any boundary obtained from the closed disk boundary by a homeomorphism inherits the
odd boundary-degree obstruction directly from the disk model domain. -/
theorem hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct
    {Y : Type*} [TopologicalSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension
    e e.continuous_toFun hboundary

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

/-- Abstract finite-index polygonal models with a face-dependent cyclic size.
This is the natural bundled interface for polygonal decompositions containing,
for example, one central polygon together with quadrilateral annulus faces. -/
structure AbstractVariableFinePolygonalModel
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
  faceSize : Face → ℕ
  boundarySize : ℕ
  edgeEnds : Edge → Vertex × Vertex
  faceEdges : Face → Finset Edge
  boundaryEdges : Finset Edge
  edgeFaceCount : ∀ e : Edge,
    (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
      if e ∈ boundaryEdges then 1 else 2
  faceVertex : ∀ f, Fin (faceSize f + 1) → Vertex
  faceEdge : ∀ f, Fin (faceSize f + 1) → Edge
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

/-- The variable-face-size obstruction theorem applied to a bundled abstract
finite model. -/
theorem AbstractVariableFinePolygonalModel.no_odd_boundary_degree
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractVariableFinePolygonalModel boundary H) (hH : Continuous H)
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundary) degree)
    (hodd : Odd degree) : False := by
  classical
  let _ := D.instVertexFintype
  let _ := D.instEdgeFintype
  let _ := D.instFaceFintype
  let _ := D.instVertexDecidableEq
  let _ := D.instEdgeDecidableEq
  let _ := D.instFaceDecidableEq
  exact no_odd_degree_of_fine_polygonal_circle_extension_variable
    D.edgeEnds D.faceEdges D.boundaryEdges D.edgeFaceCount D.faceSize
    D.faceVertex D.faceEdge D.faceVertex_injective D.faceEdge_injective
    D.faceEdges_eq D.faceEdge_ends D.boundaryEdge
    D.boundaryEdge_injective D.boundaryVertex D.boundaryEdge_ends
    D.boundaryEdges_eq D.vertexPoint (fun _ ↦ ClosedUnitInterval)
    (fun _ ↦ closedUnitIntervalStart) (fun _ ↦ closedUnitIntervalFinish)
    D.edgeToX D.edgeToX_continuous D.edgeToX_start D.edgeToX_finish
    H hH D.faceCenter D.halfTurn_mesh boundary D.boundaryParameter
    D.boundaryParameter_continuous D.boundaryParameter_start
    D.boundaryParameter_finish D.boundaryPath degree hdegree hodd

/-- Map-dependent variable-face-size fine polygonal models with arbitrary
finite index sets. -/
def HasAbstractVariableFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    Nonempty (AbstractVariableFinePolygonalModel boundary H)

/-- Variable-face-size abstract fine polygonal models imply the odd
boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractVariableFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasAbstractVariableFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  obtain ⟨D⟩ := hfine H hH
  exact D.no_odd_boundary_degree hH degree hdegree hodd

/-- An abstract geometric polygonal model with face-dependent cyclic sizes. -/
structure AbstractVariableGeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (ε : ℝ) where
  model : AbstractVariableFinePolygonalModel boundary (fun _ ↦ (0 : UnitAddCircle))
  mesh : ∀ (f : model.Face) (e : model.Edge),
    e ∈ model.faceEdges f → ∀ x : ClosedUnitInterval,
      dist (model.faceCenter f) (model.edgeToX e x) < ε

/-- Replace the vacuous constant-map half-turn estimate in a variable-face-size
abstract geometric model by a supplied estimate for a particular circle-valued
map. -/
def AbstractVariableGeometricPolygonalModel.toAbstractVariableFinePolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : AbstractVariableGeometricPolygonalModel boundary ε)
    (H : X → UnitAddCircle)
    (hhalf : ∀ (f : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges f → ∀ x : ClosedUnitInterval,
        dist (H (D.model.faceCenter f)) (H (D.model.edgeToX e x)) < 1 / 2) :
    AbstractVariableFinePolygonalModel boundary H :=
  { D.model with halfTurn_mesh := hhalf }

/-- Push a variable-face-size abstract geometric polygonal model forward along
 a continuous map whose restriction to the boundary agrees with a new
parametrization. -/
def AbstractVariableGeometricPolygonalModel.map
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {δ ε : ℝ} (D : AbstractVariableGeometricPolygonalModel boundary δ)
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmesh : ∀ (face : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges face → ∀ x : ClosedUnitInterval,
        dist (f (D.model.faceCenter face)) (f (D.model.edgeToX e x)) < ε) :
    AbstractVariableGeometricPolygonalModel boundary' ε :=
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
          simp
        boundaryPath := by
          intro k x
          rw [hboundary]
          simpa using congrArg f (D.model.boundaryPath k x) }
    mesh := hmesh }

/-- The map-independent variable-face-size surface input: compatible polygonal
models exist at every positive geometric mesh scale. -/
def HasAbstractVariableArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (AbstractVariableGeometricPolygonalModel boundary ε)

/-- Variable-face-size abstract arbitrarily fine polygonal models transport
across continuous maps from a compact source by uniform continuity. -/
theorem hasAbstractVariableArbitrarilyFinePolygonalModels_of_compact_continuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableArbitrarilyFinePolygonalModels boundary' := by
  intro ε hε
  have hUniform : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.map f hf hboundary ?_⟩
  intro face e he x
  exact hδf (D.mesh face e he x)

/-- Homeomorphic compact images inherit variable-face-size abstract arbitrarily
fine polygonal models. -/
theorem hasAbstractVariableArbitrarilyFinePolygonalModels_of_homeomorph
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableArbitrarilyFinePolygonalModels boundary' :=
  hasAbstractVariableArbitrarilyFinePolygonalModels_of_compact_continuous
    e e.continuous_toFun hboundary hmodels

/-- Variable-face-size abstract closed-square models transfer to abstract
closed-disk models through the radial square-to-disk map. -/
theorem hasAbstractVariableArbitrarilyFinePolygonalModels_of_closedUnitSquare
    (hsquare : HasAbstractVariableArbitrarilyFinePolygonalModels closedUnitSquareBoundary) :
    HasAbstractVariableArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasAbstractVariableArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareToDisk continuous_closedUnitSquareToDisk
    closedUnitSquareToDisk_comp_boundary hsquare

/-- Variable-face-size abstract models on the radial cylinder boundary push
forward directly to the closed unit square boundary. -/
theorem hasAbstractVariableArbitrarilyFinePolygonalModels_of_closedUnitSquareCylinderBoundary
    (hcyl : HasAbstractVariableArbitrarilyFinePolygonalModels closedUnitSquareCylinderBoundary) :
    HasAbstractVariableArbitrarilyFinePolygonalModels closedUnitSquareBoundary :=
  hasAbstractVariableArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareRadial continuous_closedUnitSquareRadial
    closedUnitSquareRadial_comp_cylinderBoundary hcyl

/-- On a compact metric domain, variable-face-size abstract arbitrarily fine
geometric polygonal models provide the map-dependent abstract fine models
needed by the mod-two argument. -/
theorem hasAbstractVariableFinePolygonalModels_of_abstractVariableArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractVariableArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableFinePolygonalModels boundary := by
  intro H hH
  have hUniform : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hδH⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (1 / 2) (by norm_num)
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.toAbstractVariableFinePolygonalModel H ?_⟩
  intro f e he x
  exact hδH (D.mesh f e he x)

/-- Variable-face-size abstract arbitrarily fine compatible geometric models
imply the odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractVariableArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractVariableArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_abstractVariableFinePolygonalModels
    (hasAbstractVariableFinePolygonalModels_of_abstractVariableArbitrarilyFine hmodels)

/-- Continuity of the real boundary parameter on one angular subdivision arc. -/
theorem continuous_angularSubdivisionParameter (m : ℕ) (j : Fin (m + 1)) :
    Continuous (angularSubdivisionParameter m j) := by
  have hbase : Continuous fun x : ClosedUnitInterval =>
      (((x : ℝ) + (j : ℝ)) / (m + 1) : ℝ) := by
    simpa [angularSubdivisionParameter, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((continuous_subtype_val.add continuous_const).const_mul (((m + 1 : ℕ) : ℝ)⁻¹))
  simpa [angularSubdivisionParameter] using hbase

/-- Abstract finite-index polygonal models with both variable face sizes and
face-local edge directions. -/
structure AbstractVariableDirectedFinePolygonalModel
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
  faceSize : Face → ℕ
  boundarySize : ℕ
  edgeEnds : Edge → Vertex × Vertex
  faceEdges : Face → Finset Edge
  boundaryEdges : Finset Edge
  edgeFaceCount : ∀ e : Edge,
    (Finset.univ.filter fun f ↦ e ∈ faceEdges f).card =
      if e ∈ boundaryEdges then 1 else 2
  faceVertex : ∀ f, Fin (faceSize f + 1) → Vertex
  faceEdge : ∀ f, Fin (faceSize f + 1) → Edge
  faceEdgeForward : ∀ f, Fin (faceSize f + 1) → Bool
  faceVertex_injective : ∀ f, Function.Injective (faceVertex f)
  faceEdge_injective : ∀ f, Function.Injective (faceEdge f)
  faceEdges_eq : ∀ f, faceEdges f = Finset.univ.image (faceEdge f)
  faceEdge_ends : ∀ f k, edgeEnds (faceEdge f k) =
    if faceEdgeForward f k then
      (faceVertex f k, faceVertex f (cyclicSucc k))
    else
      (faceVertex f (cyclicSucc k), faceVertex f k)
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

/-- The face-local-direction obstruction theorem applied to a bundled abstract
finite model. -/
theorem AbstractVariableDirectedFinePolygonalModel.no_odd_boundary_degree
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractVariableDirectedFinePolygonalModel boundary H) (hH : Continuous H)
    (degree : ℤ) (hdegree : HasCircleDegree (H ∘ boundary) degree)
    (hodd : Odd degree) : False := by
  classical
  let _ := D.instVertexFintype
  let _ := D.instEdgeFintype
  let _ := D.instFaceFintype
  let _ := D.instVertexDecidableEq
  let _ := D.instEdgeDecidableEq
  let _ := D.instFaceDecidableEq
  exact no_odd_degree_of_fine_polygonal_circle_extension_variable_with_edge_directions
    D.edgeEnds D.faceEdges D.boundaryEdges D.edgeFaceCount D.faceSize
    D.faceVertex D.faceEdge D.faceEdgeForward D.faceVertex_injective
    D.faceEdge_injective D.faceEdges_eq D.faceEdge_ends D.boundaryEdge
    D.boundaryEdge_injective D.boundaryVertex D.boundaryEdge_ends
    D.boundaryEdges_eq D.vertexPoint (fun _ ↦ ClosedUnitInterval)
    (fun _ ↦ closedUnitIntervalStart) (fun _ ↦ closedUnitIntervalFinish)
    D.edgeToX D.edgeToX_continuous D.edgeToX_start D.edgeToX_finish
    H hH D.faceCenter D.halfTurn_mesh boundary D.boundaryParameter
    D.boundaryParameter_continuous D.boundaryParameter_start
    D.boundaryParameter_finish D.boundaryPath degree hdegree hodd

/-- Map-dependent directed fine polygonal models with arbitrary finite index
sets. -/
def HasAbstractVariableDirectedFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ (H : X → UnitAddCircle), Continuous H →
    Nonempty (AbstractVariableDirectedFinePolygonalModel boundary H)

/-- Directed abstract fine polygonal models imply the odd boundary-degree
obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasAbstractVariableDirectedFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary := by
  intro H hH degree hdegree hodd
  obtain ⟨D⟩ := hfine H hH
  exact D.no_odd_boundary_degree hH degree hdegree hodd

/-- An abstract geometric polygonal model with variable face sizes and
face-local edge directions. -/
structure AbstractVariableDirectedGeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (ε : ℝ) where
  model : AbstractVariableDirectedFinePolygonalModel boundary (fun _ ↦ (0 : UnitAddCircle))
  mesh : ∀ (f : model.Face) (e : model.Edge),
    e ∈ model.faceEdges f → ∀ x : ClosedUnitInterval,
      dist (model.faceCenter f) (model.edgeToX e x) < ε

/-- Replace the vacuous constant-map half-turn estimate in a directed abstract
geometric model by a supplied estimate for a particular circle-valued map. -/
def AbstractVariableDirectedGeometricPolygonalModel.toAbstractVariableDirectedFinePolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : AbstractVariableDirectedGeometricPolygonalModel boundary ε)
    (H : X → UnitAddCircle)
    (hhalf : ∀ (f : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges f → ∀ x : ClosedUnitInterval,
        dist (H (D.model.faceCenter f)) (H (D.model.edgeToX e x)) < 1 / 2) :
    AbstractVariableDirectedFinePolygonalModel boundary H :=
  { D.model with halfTurn_mesh := hhalf }

/-- Push a directed variable-face-size abstract geometric polygonal model
forward along a continuous map whose restriction to the boundary agrees with a
new parametrization. -/
def AbstractVariableDirectedGeometricPolygonalModel.map
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {δ ε : ℝ} (D : AbstractVariableDirectedGeometricPolygonalModel boundary δ)
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmesh : ∀ (face : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges face → ∀ x : ClosedUnitInterval,
        dist (f (D.model.faceCenter face)) (f (D.model.edgeToX e x)) < ε) :
    AbstractVariableDirectedGeometricPolygonalModel boundary' ε :=
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
          simp
        boundaryPath := by
          intro k x
          rw [hboundary]
          simpa using congrArg f (D.model.boundaryPath k x) }
    mesh := hmesh }

/-- The map-independent directed surface input: compatible polygonal models
exist at every positive geometric mesh scale. -/
def HasAbstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (AbstractVariableDirectedGeometricPolygonalModel boundary ε)

/-- On a compact metric domain, directed abstract arbitrarily fine geometric
polygonal models provide the map-dependent abstract fine models needed by the
mod-two argument. -/
theorem hasAbstractVariableDirectedFinePolygonalModels_of_abstractVariableDirectedArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableDirectedFinePolygonalModels boundary := by
  intro H hH
  have hUniform : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hδH⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (1 / 2) (by norm_num)
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.toAbstractVariableDirectedFinePolygonalModel H ?_⟩
  intro f e he x
  exact hδH (D.mesh f e he x)

/-- Directed abstract arbitrarily fine compatible geometric models imply the
odd boundary-degree obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedFinePolygonalModels
    (hasAbstractVariableDirectedFinePolygonalModels_of_abstractVariableDirectedArbitrarilyFine hmodels)

/-- Directed variable-face-size abstract arbitrarily fine polygonal models
transport across continuous maps from a compact source by uniform continuity. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_compact_continuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary' := by
  intro ε hε
  have hUniform : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.map f hf hboundary ?_⟩
  intro face e he x
  exact hδf (D.mesh face e he x)

/-- Homeomorphic compact images inherit directed variable-face-size abstract
arbitrarily fine polygonal models. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_homeomorph
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary' :=
  hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_compact_continuous
    e e.continuous_toFun hboundary hmodels

/-- Directed variable-face-size abstract closed-square models transfer to the
closed-disk boundary through the radial square-to-disk map. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_closedUnitSquare
    (hsquare : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitSquareBoundary) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareToDisk continuous_closedUnitSquareToDisk
    closedUnitSquareToDisk_comp_boundary hsquare

/-- Directed variable-face-size abstract models on the radial cylinder boundary
push forward directly to the closed unit square boundary. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_closedUnitSquareCylinderBoundary
    (hcyl : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitSquareCylinderBoundary) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitSquareBoundary :=
  hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareRadial continuous_closedUnitSquareRadial
    closedUnitSquareRadial_comp_cylinderBoundary hcyl

/-- Core grid vertices for the undirected checkerboard cylinder strip. -/
abbrev CylinderStripVertex (n m : ℕ) := CylinderCoreVertex n m

/-- Undirected radial and angular grid segments for the checkerboard cylinder strip. -/
inductive CylinderStripEdge (n m : ℕ) : Type
  | radial : Fin (n + 1) → Fin (m + 1) → CylinderStripEdge n m
  | angular : Fin (n + 2) → Fin (m + 1) → CylinderStripEdge n m
  deriving DecidableEq, Fintype

/-- Faces of the undirected checkerboard cylinder strip. -/
abbrev CylinderStripFace (n m : ℕ) := CylinderCoreFace n m

abbrev cylinderStripFaceEven {n m : ℕ} (f : CylinderStripFace n m) : Prop :=
  cylinderCoreFaceEven f

abbrev cylinderStripFaceParity {n m : ℕ} (f : CylinderStripFace n m) : Bool :=
  cylinderCoreFaceParity f

abbrev cylinderStripLL {n m : ℕ} (f : CylinderStripFace n m) : CylinderStripVertex n m :=
  cylinderCoreLL f

abbrev cylinderStripUL {n m : ℕ} (f : CylinderStripFace n m) : CylinderStripVertex n m :=
  cylinderCoreUL f

abbrev cylinderStripLR {n m : ℕ} (f : CylinderStripFace n m) : CylinderStripVertex n m :=
  cylinderCoreLR f

abbrev cylinderStripUR {n m : ℕ} (f : CylinderStripFace n m) : CylinderStripVertex n m :=
  cylinderCoreUR f

def cylinderStripEdgeEnds {n m : ℕ} :
    CylinderStripEdge n m → CylinderStripVertex n m × CylinderStripVertex n m
  | .radial i j => ((radialSubdivisionLower i, j), (radialSubdivisionUpper i, j))
  | .angular i j => ((i, j), (i, cyclicSucc j))

def cylinderStripFaceVertex {n m : ℕ} (f : CylinderStripFace n m) :
    Fin (3 + 1) → CylinderStripVertex n m :=
  cylinderCoreFaceVertex f

def cylinderStripFaceEdge {n m : ℕ} (f : CylinderStripFace n m) :
    Fin (3 + 1) → CylinderStripEdge n m :=
  if cylinderStripFaceParity f then
    fun k =>
      match k.1 with
      | 0 => .radial f.1 f.2
      | 1 => .angular (radialSubdivisionUpper f.1) f.2
      | 2 => .radial f.1 (cyclicSucc f.2)
      | _ => .angular (radialSubdivisionLower f.1) f.2
  else
    fun k =>
      match k.1 with
      | 0 => .radial f.1 f.2
      | 1 => .angular (radialSubdivisionLower f.1) f.2
      | 2 => .radial f.1 (cyclicSucc f.2)
      | _ => .angular (radialSubdivisionUpper f.1) f.2

def cylinderStripFaceEdgeForward {n m : ℕ} (f : CylinderStripFace n m) :
    Fin (3 + 1) → Bool :=
  if cylinderStripFaceParity f then
    fun k =>
      match k.1 with
      | 0 => true
      | 1 => true
      | 2 => false
      | _ => false
  else
    fun k =>
      match k.1 with
      | 0 => false
      | 1 => true
      | 2 => true
      | _ => false

@[simp] theorem cylinderStripFaceEdge_zero {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdge f 0 = CylinderStripEdge.radial f.1 f.2 := by
  by_cases h : cylinderStripFaceParity f <;> simp [cylinderStripFaceEdge, h]

@[simp] theorem cylinderStripFaceEdge_one {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdge f 1 =
      if cylinderStripFaceEven f then
        CylinderStripEdge.angular (radialSubdivisionUpper f.1) f.2
      else
        CylinderStripEdge.angular (radialSubdivisionLower f.1) f.2 := by
  by_cases h : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderStripFaceEdge, hp, h, cylinderStripFaceEven]
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderStripFaceEdge, hp, h, cylinderStripFaceEven]

@[simp] theorem cylinderStripFaceEdge_two {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdge f 2 = CylinderStripEdge.radial f.1 (cyclicSucc f.2) := by
  by_cases h : cylinderStripFaceParity f <;> simp [cylinderStripFaceEdge, h]

@[simp] theorem cylinderStripFaceEdge_three {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdge f 3 =
      if cylinderStripFaceEven f then
        CylinderStripEdge.angular (radialSubdivisionLower f.1) f.2
      else
        CylinderStripEdge.angular (radialSubdivisionUpper f.1) f.2 := by
  by_cases h : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderStripFaceEdge, hp, h, cylinderStripFaceEven]
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderStripFaceEdge, hp, h, cylinderStripFaceEven]

@[simp] theorem cylinderStripFaceEdgeForward_zero {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdgeForward f 0 = cylinderStripFaceEven f := by
  by_cases h : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderStripFaceEdgeForward, hp, h, cylinderStripFaceEven]
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderStripFaceEdgeForward, hp, h, cylinderStripFaceEven]

@[simp] theorem cylinderStripFaceEdgeForward_one {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdgeForward f 1 = true := by
  by_cases h : cylinderStripFaceParity f <;> simp [cylinderStripFaceEdgeForward, h]

@[simp] theorem cylinderStripFaceEdgeForward_two {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdgeForward f 2 = ¬ cylinderStripFaceEven f := by
  by_cases h : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    simp [cylinderStripFaceEdgeForward, hp, h, cylinderStripFaceEven]
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    simp [cylinderStripFaceEdgeForward, hp, h, cylinderStripFaceEven]

@[simp] theorem cylinderStripFaceEdgeForward_three {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdgeForward f 3 = false := by
  by_cases h : cylinderStripFaceParity f <;> simp [cylinderStripFaceEdgeForward, h]

def cylinderStripFaceEdges {n m : ℕ} (f : CylinderStripFace n m) :
    Finset (CylinderStripEdge n m) :=
  Finset.univ.image (cylinderStripFaceEdge f)

theorem cylinderStripFaceEdges_eq {n m : ℕ} (f : CylinderStripFace n m) :
    cylinderStripFaceEdges f = Finset.univ.image (cylinderStripFaceEdge f) := rfl

theorem cylinderStripFaceVertex_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : CylinderStripFace n m) :
    Function.Injective (cylinderStripFaceVertex f) := by
  simpa [cylinderStripFaceVertex] using cylinderCoreFaceVertex_injective_of_pos hm f

theorem cylinderStripFaceEdge_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : CylinderStripFace n m) :
    Function.Injective (cylinderStripFaceEdge f) := by
  have hlu : radialSubdivisionLower f.1 ≠ radialSubdivisionUpper f.1 :=
    radialSubdivisionLower_ne_upper f.1
  have hul : radialSubdivisionUpper f.1 ≠ radialSubdivisionLower f.1 :=
    radialSubdivisionUpper_ne_lower f.1
  have hsu : cyclicSucc f.2 ≠ f.2 := cyclicSucc_ne_self_of_pos hm f.2
  have hus : f.2 ≠ cyclicSucc f.2 := self_ne_cyclicSucc_of_pos hm f.2
  intro a b h
  by_cases hpar : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 hpar
    fin_cases a <;> fin_cases b <;>
      simp [cylinderStripFaceEdge, hp, hlu, hul, hsu, hus] at h ⊢
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 hpar
    fin_cases a <;> fin_cases b <;>
      simp [cylinderStripFaceEdge, hp, hlu, hul, hsu, hus] at h ⊢

theorem cylinderStripFaceEdge_ends {n m : ℕ} (f : CylinderStripFace n m)
    (k : Fin (3 + 1)) :
    cylinderStripEdgeEnds (cylinderStripFaceEdge f k) =
      if cylinderStripFaceEdgeForward f k then
        (cylinderStripFaceVertex f k,
          cylinderStripFaceVertex f (cyclicSucc k))
      else
        (cylinderStripFaceVertex f (cyclicSucc k),
          cylinderStripFaceVertex f k) := by
  by_cases h : cylinderStripFaceEven f
  · have hp : cylinderStripFaceParity f = true :=
      (cylinderCoreFaceParity_eq_true_iff f).2 h
    fin_cases k <;>
      simp [cylinderStripEdgeEnds, cylinderStripFaceEdge, cylinderStripFaceEdgeForward,
        cylinderStripFaceVertex, cylinderCoreLL, cylinderCoreUL, cylinderCoreUR,
        cylinderCoreLR, hp, h, cyclicSucc]
  · have hp : cylinderStripFaceParity f = false :=
      (cylinderCoreFaceParity_eq_false_iff f).2 h
    fin_cases k <;>
      simp [cylinderStripEdgeEnds, cylinderStripFaceEdge, cylinderStripFaceEdgeForward,
        cylinderStripFaceVertex, cylinderCoreLL, cylinderCoreUL, cylinderCoreUR,
        cylinderCoreLR, hp, h, cyclicSucc]

def cylinderStripBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) : CylinderStripVertex n m :=
  (Fin.last (n + 1), j)

def cylinderStripBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) : CylinderStripEdge n m :=
  .angular (Fin.last (n + 1)) j

@[simp] theorem cylinderStripBoundaryEdge_injective {n m : ℕ} :
    Function.Injective (cylinderStripBoundaryEdge (n := n) (m := m)) := by
  intro a b h
  simpa [cylinderStripBoundaryEdge] using h

def cylinderStripBoundaryEdges {n m : ℕ} : Finset (CylinderStripEdge n m) :=
  Finset.univ.image (cylinderStripBoundaryEdge (n := n) (m := m))

theorem cylinderStripBoundaryEdges_eq {n m : ℕ} :
    cylinderStripBoundaryEdges (n := n) (m := m) =
      Finset.univ.image (cylinderStripBoundaryEdge (n := n) (m := m)) := rfl

@[simp] theorem cylinderStripBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    cylinderStripEdgeEnds (cylinderStripBoundaryEdge (n := n) (m := m) j) =
      (cylinderStripBoundaryVertex (n := n) (m := m) j,
        cylinderStripBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [cylinderStripBoundaryEdge, cylinderStripBoundaryVertex, cylinderStripEdgeEnds]

def cylinderStripLowerBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) : CylinderStripVertex n m :=
  (0, j)

def cylinderStripLowerBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) : CylinderStripEdge n m :=
  .angular 0 j

@[simp] theorem cylinderStripLowerBoundaryEdge_injective {n m : ℕ} :
    Function.Injective (cylinderStripLowerBoundaryEdge (n := n) (m := m)) := by
  intro a b h
  simpa [cylinderStripLowerBoundaryEdge] using h

def cylinderStripLowerBoundaryEdges {n m : ℕ} : Finset (CylinderStripEdge n m) :=
  Finset.univ.image (cylinderStripLowerBoundaryEdge (n := n) (m := m))

theorem cylinderStripLowerBoundaryEdges_eq {n m : ℕ} :
    cylinderStripLowerBoundaryEdges (n := n) (m := m) =
      Finset.univ.image (cylinderStripLowerBoundaryEdge (n := n) (m := m)) := rfl

@[simp] theorem cylinderStripLowerBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    cylinderStripEdgeEnds (cylinderStripLowerBoundaryEdge (n := n) (m := m) j) =
      (cylinderStripLowerBoundaryVertex (n := n) (m := m) j,
        cylinderStripLowerBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [cylinderStripLowerBoundaryEdge, cylinderStripLowerBoundaryVertex, cylinderStripEdgeEnds]

/-- The full free boundary of the cylinder strip consists of its lower and upper
angular circles.  Later quotient constructions will pair part or all of the
lower circle while preserving the top circle as the actual boundary. -/
def cylinderStripFreeBoundaryEdges {n m : ℕ} : Finset (CylinderStripEdge n m) :=
  cylinderStripLowerBoundaryEdges (n := n) (m := m) ∪
    cylinderStripBoundaryEdges (n := n) (m := m)

@[simp] theorem radialSubdivisionLower_injective {n : ℕ} :
    Function.Injective (@radialSubdivisionLower n) := by
  intro a b h
  apply Fin.ext
  simpa [radialSubdivisionLower] using congrArg Fin.val h

@[simp] theorem radialSubdivisionUpper_injective {n : ℕ} :
    Function.Injective (@radialSubdivisionUpper n) := by
  intro a b h
  apply Fin.ext
  simpa [radialSubdivisionUpper] using congrArg Fin.val h

@[simp] theorem radialSubdivisionUpper_last {n : ℕ} :
    radialSubdivisionUpper (Fin.last n) = Fin.last (n + 1) := by
  apply Fin.ext
  simp [radialSubdivisionUpper]

theorem radialSubdivisionUpper_ne_zero {n : ℕ} (i : Fin (n + 1)) :
    radialSubdivisionUpper i ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  simp [radialSubdivisionUpper] at hval

theorem radialSubdivisionLower_ne_last {n : ℕ} (i : Fin (n + 1)) :
    radialSubdivisionLower i ≠ Fin.last (n + 1) := by
  intro h
  have hval := congrArg Fin.val h
  simp [radialSubdivisionLower] at hval
  omega

@[simp] theorem radialSubdivisionLower_castPred {n : ℕ} (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    radialSubdivisionLower (i.castPred hi) = i := by
  apply Fin.ext
  simp [radialSubdivisionLower]

@[simp] theorem radialSubdivisionUpper_pred {n : ℕ} (i : Fin (n + 2)) (hi : i ≠ 0) :
    radialSubdivisionUpper (i.pred hi) = i := by
  apply Fin.ext
  have hpos : 0 < (i : ℕ) := Fin.pos_iff_ne_zero.mpr hi
  change ((i.pred hi : Fin (n + 1)).1 + 1) = i.1
  rw [Fin.val_pred]
  omega

@[simp] theorem mem_cylinderStripLowerBoundaryEdges_radial_iff {n m : ℕ}
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    CylinderStripEdge.radial i j ∈
      cylinderStripLowerBoundaryEdges (n := n) (m := m) ↔ False := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    simp [cylinderStripLowerBoundaryEdge] at hk
  · intro h
    exact False.elim h

theorem mem_cylinderStripLowerBoundaryEdges_angular_iff {n m : ℕ}
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    CylinderStripEdge.angular i j ∈ cylinderStripLowerBoundaryEdges (n := n) (m := m) ↔ i = 0 := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    have hk' : CylinderStripEdge.angular 0 k = CylinderStripEdge.angular i j := by
      simpa [cylinderStripLowerBoundaryEdge] using hk
    have hi' : (0 : Fin (n + 2)) = i := by
      simpa using congrArg (fun e => match e with
        | .angular i _ => i
        | .radial _ _ => 0) hk'
    exact hi'.symm
  · intro hi
    subst hi
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem mem_cylinderStripBoundaryEdges_radial_iff {n m : ℕ}
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    CylinderStripEdge.radial i j ∈
      cylinderStripBoundaryEdges (n := n) (m := m) ↔ False := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    simp [cylinderStripBoundaryEdge] at hk
  · intro h
    exact False.elim h

theorem mem_cylinderStripBoundaryEdges_angular_iff {n m : ℕ}
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    CylinderStripEdge.angular i j ∈ cylinderStripBoundaryEdges (n := n) (m := m) ↔
      i = Fin.last (n + 1) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    have hk' : CylinderStripEdge.angular (Fin.last (n + 1)) k = CylinderStripEdge.angular i j := by
      simpa [cylinderStripBoundaryEdge] using hk
    have hi' : Fin.last (n + 1) = i := by
      simpa using congrArg (fun e => match e with
        | .angular i _ => i
        | .radial _ _ => 0) hk'
    exact hi'.symm
  · intro hi
    subst hi
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem mem_cylinderStripFreeBoundaryEdges_radial_iff {n m : ℕ}
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    CylinderStripEdge.radial i j ∈
      cylinderStripFreeBoundaryEdges (n := n) (m := m) ↔ False := by
  rw [cylinderStripFreeBoundaryEdges, Finset.mem_union]
  simp [mem_cylinderStripLowerBoundaryEdges_radial_iff,
    mem_cylinderStripBoundaryEdges_radial_iff]

theorem mem_cylinderStripFreeBoundaryEdges_angular_iff {n m : ℕ}
    (i : Fin (n + 2)) (j : Fin (m + 1)) :
    CylinderStripEdge.angular i j ∈ cylinderStripFreeBoundaryEdges (n := n) (m := m) ↔
      i = 0 ∨ i = Fin.last (n + 1) := by
  rw [cylinderStripFreeBoundaryEdges, Finset.mem_union]
  rw [mem_cylinderStripLowerBoundaryEdges_angular_iff,
    mem_cylinderStripBoundaryEdges_angular_iff]

@[simp] theorem mem_cylinderStripFaceEdges_radial_iff {n m : ℕ}
    (i i' : Fin (n + 1)) (j k : Fin (m + 1)) :
    CylinderStripEdge.radial i j ∈ cylinderStripFaceEdges (i', k) ↔
      i' = i ∧ (k = j ∨ cyclicSucc k = j) := by
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨a, _ha, ha⟩
    by_cases hpar : cylinderStripFaceEven (i', k)
    · have hp : cylinderStripFaceParity (i', k) = true :=
        (cylinderCoreFaceParity_eq_true_iff (i', k)).2 hpar
      fin_cases a
      · have h0 : i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h0.1, Or.inl h0.2⟩
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h2 : i' = i ∧ cyclicSucc k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h2.1, Or.inr h2.2⟩
      · simp [cylinderStripFaceEdge, hp] at ha
    · have hp : cylinderStripFaceParity (i', k) = false :=
        (cylinderCoreFaceParity_eq_false_iff (i', k)).2 hpar
      fin_cases a
      · have h0 : i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h0.1, Or.inl h0.2⟩
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h2 : i' = i ∧ cyclicSucc k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h2.1, Or.inr h2.2⟩
      · simp [cylinderStripFaceEdge, hp] at ha
  · intro hk
    rcases hk with ⟨hi, hk⟩
    subst i'
    rcases hk with hk | hk
    · subst k
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by
        simpa using (cylinderStripFaceEdge_zero (f := (i, j)))⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by
        simpa [hk] using (cylinderStripFaceEdge_two (f := (i, k)))⟩

theorem mem_cylinderStripFaceEdges_angular_iff {n m : ℕ}
    (i : Fin (n + 2)) (i' : Fin (n + 1)) (j k : Fin (m + 1)) :
    CylinderStripEdge.angular i j ∈ cylinderStripFaceEdges (i', k) ↔
      k = j ∧ (radialSubdivisionLower i' = i ∨ radialSubdivisionUpper i' = i) := by
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨a, _ha, ha⟩
    by_cases hpar : cylinderStripFaceEven (i', k)
    · have hp : cylinderStripFaceParity (i', k) = true :=
        (cylinderCoreFaceParity_eq_true_iff (i', k)).2 hpar
      fin_cases a
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h1 : radialSubdivisionUpper i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h1.2, Or.inr h1.1⟩
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h3 : radialSubdivisionLower i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h3.2, Or.inl h3.1⟩
    · have hp : cylinderStripFaceParity (i', k) = false :=
        (cylinderCoreFaceParity_eq_false_iff (i', k)).2 hpar
      fin_cases a
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h1 : radialSubdivisionLower i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h1.2, Or.inl h1.1⟩
      · simp [cylinderStripFaceEdge, hp] at ha
      · have h3 : radialSubdivisionUpper i' = i ∧ k = j := by
          simpa [cylinderStripFaceEdge, hp] using ha
        exact ⟨h3.2, Or.inr h3.1⟩
  · intro hk
    rcases hk with ⟨hkj, hlevel⟩
    subst k
    rcases hlevel with hl | hu
    · by_cases hpar : cylinderStripFaceEven (i', j)
      · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, by
          simpa [hpar, hl] using (cylinderStripFaceEdge_three (f := (i', j)))⟩
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by
          simpa [hpar, hl] using (cylinderStripFaceEdge_one (f := (i', j)))⟩
    · by_cases hpar : cylinderStripFaceEven (i', j)
      · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by
          simpa [hpar, hu] using (cylinderStripFaceEdge_one (f := (i', j)))⟩
      · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, by
          simpa [hpar, hu] using (cylinderStripFaceEdge_three (f := (i', j)))⟩

theorem cylinderStripRadial_faceCount_of_pos {n m : ℕ} (hm : 0 < m)
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    (Finset.univ.filter fun f : CylinderStripFace n m ↦
      CylinderStripEdge.radial i j ∈ cylinderStripFaceEdges f).card = 2 := by
  have hneq : cyclicPred j ≠ j := by
    intro h
    have hsucc : cyclicSucc j = j := by
      simpa [h] using (show cyclicSucc (cyclicPred j) = j by simp)
    exact (cyclicSucc_ne_self_of_pos hm j) hsucc
  have hfilter :
      (Finset.univ.filter fun f : CylinderStripFace n m ↦
        CylinderStripEdge.radial i j ∈ cylinderStripFaceEdges f) =
          ({(i, j), (i, cyclicPred j)} : Finset (CylinderStripFace n m)) := by
    ext f
    rcases f with ⟨i', k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      rcases (mem_cylinderStripFaceEdges_radial_iff i i' j k).1 hk with ⟨hi, hk⟩
      rcases hk with hkj | hsucc
      · simp [hi, hkj]
      · have hk' : k = cyclicPred j := by
          simpa using congrArg cyclicPred hsucc
        simp [hi, hk']
    · intro hk
      rcases hk with hk | hk
      · rw [Prod.mk_inj] at hk
        rcases hk with ⟨hi, hk'⟩
        subst i'
        subst k
        exact (mem_cylinderStripFaceEdges_radial_iff i i j j).2 ⟨rfl, Or.inl rfl⟩
      · rw [Prod.mk_inj] at hk
        rcases hk with ⟨hi, hk'⟩
        subst i'
        subst k
        have hsucc : cyclicSucc (cyclicPred j) = j := by simp
        exact (mem_cylinderStripFaceEdges_radial_iff i i j (cyclicPred j)).2
          ⟨rfl, Or.inr hsucc⟩
  rw [hfilter]
  exact Finset.card_pair <| by
    intro h
    have hk : j = cyclicPred j := by
      simpa using congrArg Prod.snd h
    exact hneq hk.symm

theorem cylinderStripAngular_faceCount_of_eq_zero {n m : ℕ}
    (j : Fin (m + 1)) :
    (Finset.univ.filter fun f : CylinderStripFace n m ↦
      CylinderStripEdge.angular 0 j ∈ cylinderStripFaceEdges f).card = 1 := by
  have hfilter :
      (Finset.univ.filter fun f : CylinderStripFace n m ↦
        CylinderStripEdge.angular 0 j ∈ cylinderStripFaceEdges f) =
          ({((0 : Fin (n + 1)), j)} : Finset (CylinderStripFace n m)) := by
    ext f
    rcases f with ⟨i', k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      rcases (mem_cylinderStripFaceEdges_angular_iff (0 : Fin (n + 2)) i' j k).1 hk with ⟨hkj, hlevel⟩
      subst k
      rcases hlevel with hl | hu
      · have hi' : i' = 0 := by
          apply radialSubdivisionLower_injective
          simpa using hl
        simp [hi']
      · exact False.elim (radialSubdivisionUpper_ne_zero i' hu)
    · intro hk
      rw [Prod.mk_inj] at hk
      rcases hk with ⟨hi, hk⟩
      subst i'
      subst k
      exact (mem_cylinderStripFaceEdges_angular_iff (0 : Fin (n + 2)) 0 j j).2
        ⟨rfl, Or.inl rfl⟩
  rw [hfilter]
  simp

theorem cylinderStripAngular_faceCount_of_eq_last {n m : ℕ}
    (j : Fin (m + 1)) :
    (Finset.univ.filter fun f : CylinderStripFace n m ↦
      CylinderStripEdge.angular (Fin.last (n + 1)) j ∈ cylinderStripFaceEdges f).card = 1 := by
  have hfilter :
      (Finset.univ.filter fun f : CylinderStripFace n m ↦
        CylinderStripEdge.angular (Fin.last (n + 1)) j ∈ cylinderStripFaceEdges f) =
          ({((Fin.last n), j)} : Finset (CylinderStripFace n m)) := by
    ext f
    rcases f with ⟨i', k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      rcases (mem_cylinderStripFaceEdges_angular_iff (Fin.last (n + 1)) i' j k).1 hk with ⟨hkj, hlevel⟩
      subst k
      rcases hlevel with hl | hu
      · exact False.elim (radialSubdivisionLower_ne_last i' hl)
      · have hi' : i' = Fin.last n := by
          apply radialSubdivisionUpper_injective
          calc
            radialSubdivisionUpper i' = Fin.last (n + 1) := hu
            _ = radialSubdivisionUpper (Fin.last n) := radialSubdivisionUpper_last.symm
        simp [hi']
    · intro hk
      rw [Prod.mk_inj] at hk
      rcases hk with ⟨hi, hk⟩
      subst i'
      subst k
      exact (mem_cylinderStripFaceEdges_angular_iff (Fin.last (n + 1)) (Fin.last n) j j).2
        ⟨rfl, Or.inr radialSubdivisionUpper_last⟩
  rw [hfilter]
  simp

theorem cylinderStripAngular_faceCount_of_ne_zero_ne_last {n m : ℕ}
    (i : Fin (n + 2)) (j : Fin (m + 1))
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1)) :
    (Finset.univ.filter fun f : CylinderStripFace n m ↦
      CylinderStripEdge.angular i j ∈ cylinderStripFaceEdges f).card = 2 := by
  have hfilter :
      (Finset.univ.filter fun f : CylinderStripFace n m ↦
        CylinderStripEdge.angular i j ∈ cylinderStripFaceEdges f) =
          ({(i.pred hi0, j), (i.castPred hiLast, j)} : Finset (CylinderStripFace n m)) := by
    ext f
    rcases f with ⟨i', k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      rcases (mem_cylinderStripFaceEdges_angular_iff i i' j k).1 hk with ⟨hk, hlevel⟩
      subst hk
      rcases hlevel with hl | hu
      · have hi' : i' = i.castPred hiLast := by
          apply radialSubdivisionLower_injective
          simpa using hl
        exact Or.inr (by simpa [hi'])
      · have hi' : i' = i.pred hi0 := by
          apply radialSubdivisionUpper_injective
          simpa using hu
        exact Or.inl (by simpa [hi'])
    · intro hk
      rcases hk with hk | hk
      · cases hk
        exact (mem_cylinderStripFaceEdges_angular_iff i (i.pred hi0) j j).2 <|
          ⟨rfl, Or.inr (radialSubdivisionUpper_pred i hi0)⟩
      · cases hk
        exact (mem_cylinderStripFaceEdges_angular_iff i (i.castPred hiLast) j j).2 <|
          ⟨rfl, Or.inl (radialSubdivisionLower_castPred i hiLast)⟩
  rw [hfilter]
  apply Finset.card_pair
  intro h
  have hidx : i.pred hi0 = i.castPred hiLast := by
    simpa using congrArg Prod.fst h
  have hcontr : radialSubdivisionLower (i.pred hi0) = radialSubdivisionUpper (i.pred hi0) := by
    calc
      radialSubdivisionLower (i.pred hi0) = radialSubdivisionLower (i.castPred hiLast) := by simpa [hidx]
      _ = i := radialSubdivisionLower_castPred i hiLast
      _ = radialSubdivisionUpper (i.pred hi0) := by symm; exact radialSubdivisionUpper_pred i hi0
  exact radialSubdivisionLower_ne_upper (i.pred hi0) hcontr

theorem cylinderStripFreeBoundaryEdgeFaceCount_of_pos {n m : ℕ} (hm : 0 < m)
    (e : CylinderStripEdge n m) :
    (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
      if e ∈ cylinderStripFreeBoundaryEdges (n := n) (m := m) then 1 else 2 := by
  cases e with
  | radial i j =>
      rw [if_neg]
      · exact cylinderStripRadial_faceCount_of_pos hm i j
      · simpa using (mem_cylinderStripFreeBoundaryEdges_radial_iff (n := n) (m := m) i j)
  | angular i j =>
      by_cases hi0 : i = 0
      · rw [if_pos]
        · subst hi0
          exact cylinderStripAngular_faceCount_of_eq_zero j
        · exact (mem_cylinderStripFreeBoundaryEdges_angular_iff (n := n) (m := m) i j).2 (Or.inl hi0)
      · by_cases hiLast : i = Fin.last (n + 1)
        · rw [if_pos]
          · subst hiLast
            exact cylinderStripAngular_faceCount_of_eq_last j
          · exact (mem_cylinderStripFreeBoundaryEdges_angular_iff (n := n) (m := m) i j).2 (Or.inr hiLast)
        · rw [if_neg]
          · exact cylinderStripAngular_faceCount_of_ne_zero_ne_last i j hi0 hiLast
          · exact mt (mem_cylinderStripFreeBoundaryEdges_angular_iff (n := n) (m := m) i j).1 (by simp [hi0, hiLast])

/-- Bundle explicit checkerboard-cylinder strip data into the directed abstract
variable-face-size geometric polygonal-model interface on the square-cylinder
boundary. -/
def cylinderStripAbstractVariableDirectedGeometricModel_of_mesh
    {ε : ℝ} (n m : ℕ) (hm : 0 < m)
    (hedgeFaceCount : ∀ e : CylinderStripEdge n m,
      (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
        if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2)
    (faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle)
    (hmesh : ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
      e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
        dist (faceCenter f)
          (match e with
            | .radial i j => cylinderRadialEdgePath n m i j x
            | .angular i j => cylinderAngularEdgePath n m i j x) < ε) :
    AbstractVariableDirectedGeometricPolygonalModel closedUnitSquareCylinderBoundary ε where
  model :=
    { Vertex := CylinderStripVertex n m
      Edge := CylinderStripEdge n m
      Face := CylinderStripFace n m
      faceSize := fun _ => 3
      boundarySize := m
      edgeEnds := cylinderStripEdgeEnds
      faceEdges := cylinderStripFaceEdges
      boundaryEdges := cylinderStripBoundaryEdges (n := n) (m := m)
      edgeFaceCount := hedgeFaceCount
      faceVertex := cylinderStripFaceVertex
      faceEdge := cylinderStripFaceEdge
      faceEdgeForward := cylinderStripFaceEdgeForward
      faceVertex_injective := cylinderStripFaceVertex_injective_of_pos hm
      faceEdge_injective := cylinderStripFaceEdge_injective_of_pos hm
      faceEdges_eq := cylinderStripFaceEdges_eq
      faceEdge_ends := cylinderStripFaceEdge_ends
      boundaryEdge := cylinderStripBoundaryEdge (n := n) (m := m)
      boundaryEdge_injective := cylinderStripBoundaryEdge_injective (n := n) (m := m)
      boundaryVertex := cylinderStripBoundaryVertex (n := n) (m := m)
      boundaryEdge_ends := cylinderStripBoundaryEdge_ends (n := n) (m := m)
      boundaryEdges_eq := cylinderStripBoundaryEdges_eq (n := n) (m := m)
      vertexPoint := fun v ↦ cylinderSubdivisionPoint n m v.1 v.2
      edgeToX := fun e x =>
        match e with
        | .radial i j => cylinderRadialEdgePath n m i j x
        | .angular i j => cylinderAngularEdgePath n m i j x
      edgeToX_continuous := by
        intro e
        cases e with
        | radial i j => simpa using continuous_cylinderRadialEdgePath n m i j
        | angular i j => simpa using continuous_cylinderAngularEdgePath n m i j
      edgeToX_start := by
        intro e
        cases e with
        | radial i j => simp [cylinderStripEdgeEnds, cylinderSubdivisionPoint, cylinderRadialEdgePath_start]
        | angular i j => simp [cylinderStripEdgeEnds, cylinderSubdivisionPoint, cylinderAngularEdgePath_start]
      edgeToX_finish := by
        intro e
        cases e with
        | radial i j => simp [cylinderStripEdgeEnds, cylinderSubdivisionPoint, cylinderRadialEdgePath_finish]
        | angular i j => simp [cylinderStripEdgeEnds, cylinderSubdivisionPoint, cylinderAngularEdgePath_finish]
      faceCenter := faceCenter
      halfTurn_mesh := by
        intro f e he x
        simp
      boundaryParameter := fun k ↦ angularSubdivisionParameter m k
      boundaryParameter_continuous := continuous_angularSubdivisionParameter m
      boundaryParameter_start := by
        intro k
        simp [angularSubdivisionParameter, cyclicVertexParameter, closedUnitIntervalStart]
      boundaryParameter_finish := by
        intro k
        simp [angularSubdivisionParameter, cyclicEdgeFinishParameter, closedUnitIntervalFinish, add_comm]
      boundaryPath := by
        intro k x
        simpa [angularSubdivisionParameter] using
          cylinderAngularEdgePath_on_closedUnitSquareCylinderBoundary n m k x }
  mesh := by
    intro f e he x
    simpa using hmesh f e he x

/-- A source-level wrapper reducing the directed abstract square-cylinder
existence theorem to explicit checkerboard-cylinder strip data. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_cylinderStrip_data
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ hm : 0 < m,
      ∃ hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
        e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match e with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels
      closedUnitSquareCylinderBoundary := by
  intro ε hε
  obtain ⟨n, m, hm, hedgeFaceCount, faceCenter, hmesh⟩ := hmodels ε hε
  exact ⟨cylinderStripAbstractVariableDirectedGeometricModel_of_mesh
    n m hm hedgeFaceCount faceCenter hmesh⟩

/-- Vertices of the disk-like model with one central polygon and a quadrilateral annulus. -/
abbrev SquareCenterPolygonVertex (n m : ℕ) := Fin (n + 1) × Fin (m + 1)

/-- Global edges of the disk-like model with one central polygon and a quadrilateral annulus. -/
inductive SquareCenterPolygonEdge (n m : ℕ)
  | radial (i : Fin n) (j : Fin (m + 1))
  | angular (i : Fin (n + 1)) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Faces of the disk-like model with one central polygon and a quadrilateral annulus. -/
inductive SquareCenterPolygonFace (n m : ℕ)
  | center
  | annulus (i : Fin n) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Edge endpoints in the center-polygon annulus model. -/
def squareCenterPolygonEdgeEnds {n m : ℕ} :
    SquareCenterPolygonEdge n m → SquareCenterPolygonVertex n m × SquareCenterPolygonVertex n m
  | .radial i j => ((lowerSquareRingLevel i, j), (upperSquareRingLevel i, j))
  | .angular i j => ((i, j), (i, cyclicSucc j))

/-- Geometric location of a vertex in the center-polygon annulus model. -/
def squareCenterPolygonVertexPoint (n m : ℕ) :
    SquareCenterPolygonVertex n m → ClosedUnitSquare
  | (i, j) =>
      closedUnitSquareRadial
        (radialSubdivisionPoint n (radialSubdivisionUpper i), angularSubdivisionPoint m j)

/-- Edge paths in the center-polygon annulus model. -/
def squareCenterPolygonEdgePath (n m : ℕ) :
    SquareCenterPolygonEdge n m → ClosedUnitInterval → ClosedUnitSquare
  | .radial i j =>
      fun x ↦ closedUnitSquareRadial
        (cylinderRadialEdgePath n m (upperSquareRingLevel i) j x)
  | .angular i j =>
      fun x ↦ closedUnitSquareRadial
        (cylinderAngularEdgePath n m (radialSubdivisionUpper i) j x)

theorem continuous_squareCenterPolygonEdgePath (n m : ℕ)
    (e : SquareCenterPolygonEdge n m) :
    Continuous (squareCenterPolygonEdgePath n m e) := by
  cases e with
  | radial i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderRadialEdgePath n m (upperSquareRingLevel i) j
  | angular i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderAngularEdgePath n m (radialSubdivisionUpper i) j

theorem squareCenterPolygonEdgePath_start {n m : ℕ}
    (e : SquareCenterPolygonEdge n m) :
    squareCenterPolygonEdgePath n m e closedUnitIntervalStart =
      squareCenterPolygonVertexPoint n m (squareCenterPolygonEdgeEnds e).1 := by
  cases e with
  | radial i j =>
      simp [squareCenterPolygonEdgePath, squareCenterPolygonEdgeEnds,
        squareCenterPolygonVertexPoint, cylinderRadialEdgePath_start,
        cylinderSubdivisionPoint, radialSubdivisionLower_upperSquareRingLevel]
  | angular i j =>
      simp [squareCenterPolygonEdgePath, squareCenterPolygonEdgeEnds,
        squareCenterPolygonVertexPoint, cylinderAngularEdgePath_start,
        cylinderSubdivisionPoint]

theorem squareCenterPolygonEdgePath_finish {n m : ℕ}
    (e : SquareCenterPolygonEdge n m) :
    squareCenterPolygonEdgePath n m e closedUnitIntervalFinish =
      squareCenterPolygonVertexPoint n m (squareCenterPolygonEdgeEnds e).2 := by
  cases e with
  | radial i j =>
      simp [squareCenterPolygonEdgePath, squareCenterPolygonEdgeEnds,
        squareCenterPolygonVertexPoint, cylinderRadialEdgePath_finish,
        cylinderSubdivisionPoint]
  | angular i j =>
      simp [squareCenterPolygonEdgePath, squareCenterPolygonEdgeEnds,
        squareCenterPolygonVertexPoint, cylinderAngularEdgePath_finish,
        cylinderSubdivisionPoint]

/-- Face sizes for the center-polygon annulus model. -/
def squareCenterPolygonFaceSize {n m : ℕ} : SquareCenterPolygonFace n m → ℕ
  | .center => m
  | .annulus _ _ => 3

/-- Face vertices for the center-polygon annulus model. -/
def squareCenterPolygonFaceVertex {n m : ℕ} :
    ∀ f : SquareCenterPolygonFace n m,
      Fin (squareCenterPolygonFaceSize f + 1) → SquareCenterPolygonVertex n m
  | .center => fun k => (0, k)
  | .annulus i j =>
      fun k =>
        match k.1 with
        | 0 => (lowerSquareRingLevel i, j)
        | 1 => (upperSquareRingLevel i, j)
        | 2 => (upperSquareRingLevel i, cyclicSucc j)
        | _ => (lowerSquareRingLevel i, cyclicSucc j)

/-- Face edges for the center-polygon annulus model. -/
def squareCenterPolygonFaceEdge {n m : ℕ} :
    ∀ f : SquareCenterPolygonFace n m,
      Fin (squareCenterPolygonFaceSize f + 1) → SquareCenterPolygonEdge n m
  | .center => fun k => .angular 0 k
  | .annulus i j =>
      fun k =>
        match k.1 with
        | 0 => .radial i j
        | 1 => .angular (upperSquareRingLevel i) j
        | 2 => .radial i (cyclicSucc j)
        | _ => .angular (lowerSquareRingLevel i) j

/-- Whether a face traverses a global edge in its forward direction. -/
def squareCenterPolygonFaceEdgeForward {n m : ℕ} :
    ∀ f : SquareCenterPolygonFace n m,
      Fin (squareCenterPolygonFaceSize f + 1) → Bool
  | .center => fun _ => true
  | .annulus _ _ =>
      fun k =>
        match k.1 with
        | 0 => true
        | 1 => true
        | 2 => false
        | _ => false

def squareCenterPolygonFaceEdges {n m : ℕ} (f : SquareCenterPolygonFace n m) :
    Finset (SquareCenterPolygonEdge n m) :=
  Finset.univ.image (squareCenterPolygonFaceEdge f)

theorem squareCenterPolygonFaceEdges_eq {n m : ℕ} (f : SquareCenterPolygonFace n m) :
    squareCenterPolygonFaceEdges f = Finset.univ.image (squareCenterPolygonFaceEdge f) := rfl

theorem squareCenterPolygonFaceVertex_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : SquareCenterPolygonFace n m) :
    Function.Injective (squareCenterPolygonFaceVertex f) := by
  intro a b h
  cases f with
  | center =>
      simpa [squareCenterPolygonFaceSize, squareCenterPolygonFaceVertex] using congrArg Prod.snd h
  | annulus i j =>
      have hcyc₁ : j ≠ cyclicSucc j := self_ne_cyclicSucc_of_pos hm j
      have hcyc₂ : cyclicSucc j ≠ j := cyclicSucc_ne_self_of_pos hm j
      have hlevel₁ : lowerSquareRingLevel i ≠ upperSquareRingLevel i :=
        lowerSquareRingLevel_ne_upperSquareRingLevel i
      have hlevel₂ : upperSquareRingLevel i ≠ lowerSquareRingLevel i :=
        upperSquareRingLevel_ne_lowerSquareRingLevel i
      fin_cases a <;> fin_cases b <;>
        simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceVertex,
          hcyc₁, hcyc₂, hlevel₁, hlevel₂] at h ⊢

theorem squareCenterPolygonFaceEdge_injective_of_pos {n m : ℕ} (hm : 0 < m)
    (f : SquareCenterPolygonFace n m) :
    Function.Injective (squareCenterPolygonFaceEdge f) := by
  intro a b h
  cases f with
  | center =>
      simpa [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] using
        congrArg (fun e => match e with | .angular _ j => j | _ => 0) h
  | annulus i j =>
      have hcyc₁ : j ≠ cyclicSucc j := self_ne_cyclicSucc_of_pos hm j
      have hcyc₂ : cyclicSucc j ≠ j := cyclicSucc_ne_self_of_pos hm j
      have hlevel₁ : lowerSquareRingLevel i ≠ upperSquareRingLevel i :=
        lowerSquareRingLevel_ne_upperSquareRingLevel i
      have hlevel₂ : upperSquareRingLevel i ≠ lowerSquareRingLevel i :=
        upperSquareRingLevel_ne_lowerSquareRingLevel i
      fin_cases a <;> fin_cases b <;>
        simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge,
          hcyc₁, hcyc₂, hlevel₁, hlevel₂] at h ⊢

theorem squareCenterPolygonFaceEdge_ends {n m : ℕ}
    (f : SquareCenterPolygonFace n m)
    (k : Fin (squareCenterPolygonFaceSize f + 1)) :
    squareCenterPolygonEdgeEnds (squareCenterPolygonFaceEdge f k) =
      if squareCenterPolygonFaceEdgeForward f k then
        (squareCenterPolygonFaceVertex f k,
          squareCenterPolygonFaceVertex f (cyclicSucc k))
      else
        (squareCenterPolygonFaceVertex f (cyclicSucc k),
          squareCenterPolygonFaceVertex f k) := by
  cases f with
  | center =>
      simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge,
        squareCenterPolygonFaceVertex, squareCenterPolygonFaceEdgeForward,
        squareCenterPolygonEdgeEnds, cyclicSucc]
  | annulus i j =>
      fin_cases k <;>
        simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge,
          squareCenterPolygonFaceVertex, squareCenterPolygonFaceEdgeForward,
          squareCenterPolygonEdgeEnds, cyclicSucc]

/-- Boundary vertices of the center-polygon annulus model. -/
def squareCenterPolygonBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) :
    SquareCenterPolygonVertex n m :=
  (Fin.last n, j)

/-- Boundary edges of the center-polygon annulus model. -/
def squareCenterPolygonBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) :
    SquareCenterPolygonEdge n m :=
  .angular (Fin.last n) j

@[simp] theorem squareCenterPolygonBoundaryEdge_injective {n m : ℕ} :
    Function.Injective (squareCenterPolygonBoundaryEdge (n := n) (m := m)) := by
  intro a b h
  simpa [squareCenterPolygonBoundaryEdge] using h

def squareCenterPolygonBoundaryEdges {n m : ℕ} : Finset (SquareCenterPolygonEdge n m) :=
  Finset.univ.image (squareCenterPolygonBoundaryEdge (n := n) (m := m))

theorem squareCenterPolygonBoundaryEdges_eq {n m : ℕ} :
    squareCenterPolygonBoundaryEdges (n := n) (m := m) =
      Finset.univ.image (squareCenterPolygonBoundaryEdge (n := n) (m := m)) := rfl

@[simp] theorem squareCenterPolygonBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    squareCenterPolygonEdgeEnds (squareCenterPolygonBoundaryEdge (n := n) (m := m) j) =
      (squareCenterPolygonBoundaryVertex (n := n) (m := m) j,
        squareCenterPolygonBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [squareCenterPolygonBoundaryEdge, squareCenterPolygonBoundaryVertex,
    squareCenterPolygonEdgeEnds]


theorem lowerSquareRingLevel_injective {n : ℕ} :
    Function.Injective (@lowerSquareRingLevel n) := by
  intro a b h
  apply Fin.ext
  simpa [lowerSquareRingLevel] using congrArg Fin.val h

theorem upperSquareRingLevel_injective {n : ℕ} :
    Function.Injective (@upperSquareRingLevel n) := by
  intro a b h
  apply Fin.ext
  simpa [upperSquareRingLevel] using congrArg Fin.val h

@[simp] theorem upperSquareRingLevel_last {n : ℕ} :
    upperSquareRingLevel (Fin.last n) = Fin.last (n + 1) := by
  apply Fin.ext
  simp [upperSquareRingLevel]

@[simp] theorem mem_squareCenterPolygonBoundaryEdges_radial_iff {n m : ℕ}
    (i : Fin n) (j : Fin (m + 1)) :
    SquareCenterPolygonEdge.radial i j ∈ squareCenterPolygonBoundaryEdges (n := n) (m := m) ↔ False := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    simp [squareCenterPolygonBoundaryEdge] at hk
  · intro h
    exact False.elim h

theorem mem_squareCenterPolygonBoundaryEdges_angular_iff {n m : ℕ}
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    SquareCenterPolygonEdge.angular i j ∈ squareCenterPolygonBoundaryEdges (n := n) (m := m) ↔
      i = Fin.last n := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    have hk' : SquareCenterPolygonEdge.angular (Fin.last n) k =
        SquareCenterPolygonEdge.angular i j := by
      simpa [squareCenterPolygonBoundaryEdge] using hk
    have hi' : Fin.last n = i := by
      simpa using congrArg (fun e => match e with
        | .angular i _ => i
        | .radial _ _ => 0) hk'
    exact hi'.symm
  · intro hi
    subst hi
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem mem_squareCenterPolygonFaceEdges_center_radial_iff {n m : ℕ}
    (i : Fin n) (j : Fin (m + 1)) :
    SquareCenterPolygonEdge.radial i j ∈
        squareCenterPolygonFaceEdges (SquareCenterPolygonFace.center : SquareCenterPolygonFace n m) ↔ False := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    simp [squareCenterPolygonFaceEdges, squareCenterPolygonFaceEdge] at hk
  · intro h
    exact False.elim h

theorem mem_squareCenterPolygonFaceEdges_center_angular_iff {n m : ℕ}
    (i : Fin (n + 1)) (j : Fin (m + 1)) :
    SquareCenterPolygonEdge.angular i j ∈
        squareCenterPolygonFaceEdges (SquareCenterPolygonFace.center : SquareCenterPolygonFace n m) ↔
      i = 0 := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨k, _hk, hk⟩
    have hk' : (0 : Fin (n + 1)) = i ∧ k = j := by
      simpa [squareCenterPolygonFaceEdge] using hk
    exact hk'.1.symm
  · intro hi
    subst hi
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem mem_squareCenterPolygonFaceEdges_annulus_radial_iff {n m : ℕ}
    (i' i : Fin n) (k j : Fin (m + 1)) :
    SquareCenterPolygonEdge.radial i j ∈
        squareCenterPolygonFaceEdges (SquareCenterPolygonFace.annulus i' k : SquareCenterPolygonFace n m) ↔
      i' = i ∧ (k = j ∨ cyclicSucc k = j) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    fin_cases t
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
      exact ⟨ht.1, Or.inl ht.2⟩
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
      exact ⟨ht.1, Or.inr ht.2⟩
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
  · rintro ⟨rfl, rfl | hsucc⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge]⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, by simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge, hsucc]⟩

theorem mem_squareCenterPolygonFaceEdges_annulus_angular_iff {n m : ℕ}
    (i : Fin (n + 1)) (i' : Fin n) (j k : Fin (m + 1)) :
    SquareCenterPolygonEdge.angular i j ∈
        squareCenterPolygonFaceEdges (SquareCenterPolygonFace.annulus i' k : SquareCenterPolygonFace n m) ↔
      (upperSquareRingLevel i' = i ∧ k = j) ∨ (lowerSquareRingLevel i' = i ∧ k = j) := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨t, _ht, ht⟩
    fin_cases t
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
      exact Or.inl ⟨ht.1, ht.2⟩
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
    · simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge] at ht
      exact Or.inr ⟨ht.1, ht.2⟩
  · rintro (⟨hu, rfl⟩ | ⟨hl, rfl⟩)
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge, hu]⟩
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, by simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge, hl]⟩

theorem cyclicPred_ne_self_of_pos {m : ℕ} (hm : 0 < m) (j : Fin (m + 1)) :
    cyclicPred j ≠ j := by
  intro h
  have hsucc : cyclicSucc j = j := by
    simpa [h] using (show cyclicSucc (cyclicPred j) = j by simp)
  exact (cyclicSucc_ne_self_of_pos hm j) hsucc

@[simp] theorem lowerSquareRingLevel_castLT {n : ℕ} (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    lowerSquareRingLevel (i.castLT (Fin.val_lt_last hi)) = i := by
  apply Fin.ext
  simp [lowerSquareRingLevel]

@[simp] theorem upperSquareRingLevel_pred {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    upperSquareRingLevel (i.pred hi) = i := by
  apply Fin.ext
  have hpos : 0 < (i : ℕ) := Fin.pos_iff_ne_zero.mpr hi
  change ((i.pred hi : Fin n).1 + 1) = i.1
  rw [Fin.val_pred]
  omega

theorem upperSquareRingLevel_ne_zero {n : ℕ} (i : Fin (n + 1)) :
    upperSquareRingLevel i ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  simp [upperSquareRingLevel] at hval

theorem lowerSquareRingLevel_ne_last {n : ℕ} (i : Fin n) :
    lowerSquareRingLevel i ≠ Fin.last n := by
  intro h
  have hval := congrArg Fin.val h
  simp [lowerSquareRingLevel] at hval
  omega

theorem squareCenterPolygonRadial_faceCount_of_pos {n m : ℕ} (hm : 0 < m)
    (i : Fin n) (j : Fin (m + 1)) :
    (Finset.univ.filter fun f : SquareCenterPolygonFace n m ↦
      SquareCenterPolygonEdge.radial i j ∈ squareCenterPolygonFaceEdges f).card = 2 := by
  have hneq : cyclicPred j ≠ j := cyclicPred_ne_self_of_pos hm j
  have hfilter :
      (Finset.univ.filter fun f : SquareCenterPolygonFace n m ↦
        SquareCenterPolygonEdge.radial i j ∈ squareCenterPolygonFaceEdges f) =
          ({SquareCenterPolygonFace.annulus i j,
            SquareCenterPolygonFace.annulus i (cyclicPred j)} :
              Finset (SquareCenterPolygonFace n m)) := by
    ext f
    cases f with
    | center =>
        simp
    | annulus i' k =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hk
          rcases (mem_squareCenterPolygonFaceEdges_annulus_radial_iff i' i k j).mp hk with ⟨hi, hkj⟩
          rcases hkj with hEq | hEq
          · subst hi
            exact Or.inl (by simpa [hEq])
          · subst hi
            right
            have hk' : k = cyclicPred j := by
              simpa using congrArg cyclicPred hEq
            simpa using hk'
        · intro hk
          rcases hk with hk | hk
          · cases hk
            exact (mem_squareCenterPolygonFaceEdges_annulus_radial_iff i i j j).2 ⟨rfl, Or.inl rfl⟩
          · cases hk
            have hsucc : cyclicSucc (cyclicPred j) = j := by simp
            exact (mem_squareCenterPolygonFaceEdges_annulus_radial_iff i i (cyclicPred j) j).2
              ⟨rfl, Or.inr hsucc⟩
  rw [hfilter]
  exact Finset.card_pair <| by
    intro h
    have hk : j = cyclicPred j := by
      simpa using congrArg (fun f => match f with
        | SquareCenterPolygonFace.annulus _ k => k
        | SquareCenterPolygonFace.center => j) h
    exact hneq hk.symm


@[simp] theorem lowerSquareRingLevel_castPred {n : ℕ} (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    lowerSquareRingLevel (i.castPred hi) = i := by
  simpa [Fin.castPred] using lowerSquareRingLevel_castLT i hi

theorem squareCenterPolygonAngular_faceCount_of_eq_last {n m : ℕ}
    (j : Fin (m + 1)) :
    (Finset.univ.filter fun f : SquareCenterPolygonFace n m ↦
      SquareCenterPolygonEdge.angular (Fin.last n) j ∈ squareCenterPolygonFaceEdges f).card = 1 := by
  cases n with
  | zero =>
      have hfilter :
          (Finset.univ.filter fun f : SquareCenterPolygonFace 0 m ↦
            SquareCenterPolygonEdge.angular (Fin.last 0) j ∈ squareCenterPolygonFaceEdges f) =
              ({SquareCenterPolygonFace.center} : Finset (SquareCenterPolygonFace 0 m)) := by
        ext f
        cases f with
        | center => simp [squareCenterPolygonFaceEdges, squareCenterPolygonFaceEdge]
        | annulus i k => exact Fin.elim0 i
      rw [hfilter]
      simp
  | succ n =>
      have hlast0 : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
      have hfilter :
          (Finset.univ.filter fun f : SquareCenterPolygonFace (n + 1) m ↦
            SquareCenterPolygonEdge.angular (Fin.last (n + 1)) j ∈ squareCenterPolygonFaceEdges f) =
              ({SquareCenterPolygonFace.annulus (Fin.last n) j} : Finset (SquareCenterPolygonFace (n + 1) m)) := by
        ext f
        cases f with
        | center =>
            simp [mem_squareCenterPolygonFaceEdges_center_angular_iff, hlast0]
        | annulus i' k =>
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro hk
              rcases (mem_squareCenterPolygonFaceEdges_annulus_angular_iff (Fin.last (n + 1)) i' j k).mp hk with h | h
              · rcases h with ⟨hu, hk⟩
                have hi' : i' = Fin.last n := by
                  apply upperSquareRingLevel_injective
                  simpa [upperSquareRingLevel_last] using hu
                subst hi'
                simpa [hk]
              · rcases h with ⟨hl, hk⟩
                exact False.elim (lowerSquareRingLevel_ne_last i' hl)
            · intro hk
              injection hk with hi' hk'
              subst hi'
              subst hk'
              exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by
                simp [squareCenterPolygonFaceSize, squareCenterPolygonFaceEdge, upperSquareRingLevel_last]⟩
      rw [hfilter]
      simp

theorem squareCenterPolygonAngular_faceCount_of_ne_last {n m : ℕ} (hm : 0 < m)
    (i : Fin (n + 1)) (j : Fin (m + 1)) (hi : i ≠ Fin.last n) :
    (Finset.univ.filter fun f : SquareCenterPolygonFace n m ↦
      SquareCenterPolygonEdge.angular i j ∈ squareCenterPolygonFaceEdges f).card = 2 := by
  cases n with
  | zero =>
      fin_cases i
      exfalso
      exact hi (by simp)
  | succ n =>
      by_cases hi0 : i = 0
      · have hfilter :
          (Finset.univ.filter fun f : SquareCenterPolygonFace (n + 1) m ↦
            SquareCenterPolygonEdge.angular i j ∈ squareCenterPolygonFaceEdges f) =
              ({SquareCenterPolygonFace.center, SquareCenterPolygonFace.annulus 0 j} :
                Finset (SquareCenterPolygonFace (n + 1) m)) := by
          ext f
          cases f with
          | center =>
              simp [mem_squareCenterPolygonFaceEdges_center_angular_iff, hi0]
          | annulus i' k =>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · intro hk
                rcases (mem_squareCenterPolygonFaceEdges_annulus_angular_iff i i' j k).mp hk with h | h
                · rcases h with ⟨hu, hk⟩
                  exact False.elim (upperSquareRingLevel_ne_zero i' (hu.trans hi0))
                · rcases h with ⟨hl, hk⟩
                  have hi' : i' = 0 := by
                    apply lowerSquareRingLevel_injective
                    simpa [hi0] using hl
                  subst hi'
                  exact Or.inr (by simpa [hk])
              · intro hk
                rcases hk with hk | hk
                · cases hk
                · cases hk
                  simpa [hi0] using (mem_squareCenterPolygonFaceEdges_annulus_angular_iff 0 0 j j).2 <|
                    Or.inr ⟨show lowerSquareRingLevel (0 : Fin (n + 1)) = (0 : Fin (n + 2)) by rfl, rfl⟩
        rw [hfilter]
        apply Finset.card_pair
        intro h
        cases h
      · have hfilter :
          (Finset.univ.filter fun f : SquareCenterPolygonFace (n + 1) m ↦
            SquareCenterPolygonEdge.angular i j ∈ squareCenterPolygonFaceEdges f) =
              ({SquareCenterPolygonFace.annulus (i.pred hi0) j,
                SquareCenterPolygonFace.annulus (i.castPred hi) j} :
                  Finset (SquareCenterPolygonFace (n + 1) m)) := by
          ext f
          cases f with
          | center =>
              simp [mem_squareCenterPolygonFaceEdges_center_angular_iff, hi0]
          | annulus i' k =>
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
              constructor
              · intro hk
                rcases (mem_squareCenterPolygonFaceEdges_annulus_angular_iff i i' j k).mp hk with h | h
                · rcases h with ⟨hu, hk⟩
                  have hi' : i' = i.pred hi0 := by
                    apply upperSquareRingLevel_injective
                    simpa using hu
                  subst hi'
                  exact Or.inl (by simpa [hk])
                · rcases h with ⟨hl, hk⟩
                  have hi'' : i' = i.castPred hi := by
                    apply lowerSquareRingLevel_injective
                    simpa using hl
                  subst hi''
                  exact Or.inr (by simpa [hk])
              · intro hk
                rcases hk with hk | hk
                · cases hk
                  exact (mem_squareCenterPolygonFaceEdges_annulus_angular_iff i (i.pred hi0) j j).2 <|
                    Or.inl ⟨upperSquareRingLevel_pred i hi0, rfl⟩
                · cases hk
                  exact (mem_squareCenterPolygonFaceEdges_annulus_angular_iff i (i.castPred hi) j j).2 <|
                    Or.inr ⟨lowerSquareRingLevel_castPred i hi, rfl⟩
        rw [hfilter]
        apply Finset.card_pair
        intro h
        have hidx : i.pred hi0 = i.castPred hi := by
          simpa using congrArg (fun f => match f with
            | SquareCenterPolygonFace.annulus i _ => i
            | SquareCenterPolygonFace.center => i.pred hi0) h
        have hcontr : lowerSquareRingLevel (i.pred hi0) = upperSquareRingLevel (i.pred hi0) := by
          calc
            lowerSquareRingLevel (i.pred hi0) = lowerSquareRingLevel (i.castPred hi) := by simpa [hidx]
            _ = i := lowerSquareRingLevel_castPred i hi
            _ = upperSquareRingLevel (i.pred hi0) := by symm; exact upperSquareRingLevel_pred i hi0
        exact lowerSquareRingLevel_ne_upperSquareRingLevel (i.pred hi0) hcontr

theorem squareCenterPolygonEdgeFaceCount_of_pos {n m : ℕ} (hm : 0 < m)
    (e : SquareCenterPolygonEdge n m) :
    (Finset.univ.filter fun f ↦ e ∈ squareCenterPolygonFaceEdges f).card =
      if e ∈ squareCenterPolygonBoundaryEdges (n := n) (m := m) then 1 else 2 := by
  cases e with
  | radial i j =>
      rw [if_neg]
      · exact squareCenterPolygonRadial_faceCount_of_pos hm i j
      · simpa using (mem_squareCenterPolygonBoundaryEdges_radial_iff (n := n) (m := m) i j)
  | angular i j =>
      by_cases hi : i = Fin.last n
      · rw [if_pos]
        · subst hi
          exact squareCenterPolygonAngular_faceCount_of_eq_last j
        · exact (mem_squareCenterPolygonBoundaryEdges_angular_iff (n := n) (m := m) i j).2 hi
      · rw [if_neg]
        · exact squareCenterPolygonAngular_faceCount_of_ne_last hm i j hi
        · exact mt (mem_squareCenterPolygonBoundaryEdges_angular_iff (n := n) (m := m) i j).1 hi



theorem norm_coe_closedUnitSquare_le_sqrt_two (z : ClosedUnitSquare) :
    ‖(z : ℂ)‖ ≤ Real.sqrt 2 := by
  calc
    ‖(z : ℂ)‖ ≤ Real.sqrt 2 * complexSupNorm (z : ℂ) := by
      simpa [complexSupNorm] using Complex.norm_le_sqrt_two_mul_max (z : ℂ)
    _ ≤ Real.sqrt 2 * 1 := by
      gcongr
      exact z.2
    _ = Real.sqrt 2 := by ring

theorem dist_angularSubdivisionArc_point_le (m : ℕ) (hm : 0 < m)
    (j : Fin (m + 1)) (x : ClosedUnitInterval) :
    dist (angularSubdivisionArc m j x) (angularSubdivisionPoint m j) ≤ 1 / (m + 1 : ℝ) := by
  have hadd : angularSubdivisionArc m j x =
      angularSubdivisionPoint m j + ((((x : ℝ) / (m + 1 : ℝ)) : ℝ) : UnitAddCircle) := by
    simp [angularSubdivisionArc, angularSubdivisionParameter, angularSubdivisionPoint]
    rw [← AddCircle.coe_add]
    congr 1
    ring
  rw [dist_eq_norm, hadd, add_sub_cancel_left]
  have hxnonneg : 0 ≤ (x : ℝ) / (m + 1 : ℝ) := by
    exact div_nonneg x.2.1 (by positivity : 0 ≤ (m + 1 : ℝ))
  have hhalf : |(x : ℝ) / (m + 1 : ℝ)| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg hxnonneg, abs_of_pos zero_lt_one]
    have hxle : (x : ℝ) / (m + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
      gcongr
      exact x.2.2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm2 : (2 : ℝ) ≤ m + 1 := by nlinarith
    have hstep : 1 / (m + 1 : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2) hm2
    exact hxle.trans hstep
  calc
    ‖((((x : ℝ) / (m + 1 : ℝ)) : ℝ) : UnitAddCircle)‖ = |(x : ℝ) / (m + 1 : ℝ)| := by
      exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hhalf
    _ ≤ 1 / (m + 1 : ℝ) := by
      rw [abs_of_nonneg hxnonneg]
      have hxle : (x : ℝ) / (m + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
        gcongr
        exact x.2.2
      exact hxle

theorem dist_angularSubdivisionPoint_cyclicSucc_le (m : ℕ) (hm : 0 < m)
    (j : Fin (m + 1)) :
    dist (angularSubdivisionPoint m j) (angularSubdivisionPoint m (cyclicSucc j)) ≤
      1 / (m + 1 : ℝ) := by
  simpa [dist_comm, angularSubdivisionArc_finish] using
    dist_angularSubdivisionArc_point_le m hm j closedUnitIntervalFinish

theorem dist_radialSubdivisionArc_start_le (n : ℕ) (i : Fin (n + 1))
    (x : ClosedUnitInterval) :
    dist (radialSubdivisionArc n i x)
      (radialSubdivisionPoint n (radialSubdivisionLower i)) ≤ 1 / (n + 1 : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  have hxnonneg : 0 ≤ (x : ℝ) / (n + 1 : ℝ) := by
    exact div_nonneg x.2.1 (by positivity : 0 ≤ (n + 1 : ℝ))
  have hcalc : (((x : ℝ) + (i : ℝ)) / (n + 1 : ℝ)) - ((i : ℝ) / (n + 1 : ℝ)) =
      (x : ℝ) / (n + 1 : ℝ) := by
    ring
  rw [radialSubdivisionArc, radialSubdivisionPoint, radialSubdivisionLower, hcalc,
    abs_of_nonneg hxnonneg]
  have hxle : (x : ℝ) / (n + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
    gcongr
    exact x.2.2
  exact hxle

theorem dist_radialSubdivision_upper_lower_le (n : ℕ) (i : Fin (n + 1)) :
    dist (radialSubdivisionPoint n (radialSubdivisionUpper i))
      (radialSubdivisionPoint n (radialSubdivisionLower i)) ≤ 1 / (n + 1 : ℝ) := by
  simpa [radialSubdivisionArc_finish] using
    dist_radialSubdivisionArc_start_le n i closedUnitIntervalFinish

theorem dist_closedUnitSquareCenter_closedUnitSquareRadial_le
    (r : ClosedUnitInterval) (t : UnitAddCircle) :
    dist closedUnitSquareCenter (closedUnitSquareRadial (r, t)) ≤ (r : ℝ) * Real.sqrt 2 := by
  rw [Subtype.dist_eq, dist_eq_norm]
  simp [closedUnitSquareCenter, closedUnitSquareRadial, closedUnitSquareScale]
  calc
    |(r : ℝ)| * ‖((closedUnitSquareBoundary t : ClosedUnitSquare) : ℂ)‖
        ≤ |(r : ℝ)| * Real.sqrt 2 := by
          gcongr
          exact norm_coe_closedUnitSquare_le_sqrt_two (closedUnitSquareBoundary t)
    _ = (r : ℝ) * Real.sqrt 2 := by
      rw [abs_of_nonneg r.2.1]

/-- Bundle the explicit center-polygon annulus data into the abstract directed
variable-face-size geometric interface, isolating the remaining global edge-count
and mesh estimates as hypotheses. -/
def squareCenterPolygonAbstractVariableDirectedGeometricModel_of_mesh
    (n m : ℕ) (hm : 0 < m) {ε : ℝ}
    (faceCenter : SquareCenterPolygonFace n m → ClosedUnitSquare)
    (hmesh : ∀ (f : SquareCenterPolygonFace n m) (e : SquareCenterPolygonEdge n m),
      e ∈ squareCenterPolygonFaceEdges f → ∀ x : ClosedUnitInterval,
        dist (faceCenter f) (squareCenterPolygonEdgePath n m e x) < ε) :
    AbstractVariableDirectedGeometricPolygonalModel closedUnitSquareBoundary ε where
  model :=
    { Vertex := SquareCenterPolygonVertex n m
      Edge := SquareCenterPolygonEdge n m
      Face := SquareCenterPolygonFace n m
      faceSize := squareCenterPolygonFaceSize
      boundarySize := m
      edgeEnds := squareCenterPolygonEdgeEnds
      faceEdges := squareCenterPolygonFaceEdges
      boundaryEdges := squareCenterPolygonBoundaryEdges (n := n) (m := m)
      edgeFaceCount := squareCenterPolygonEdgeFaceCount_of_pos hm
      faceVertex := squareCenterPolygonFaceVertex
      faceEdge := squareCenterPolygonFaceEdge
      faceEdgeForward := squareCenterPolygonFaceEdgeForward
      faceVertex_injective := squareCenterPolygonFaceVertex_injective_of_pos hm
      faceEdge_injective := squareCenterPolygonFaceEdge_injective_of_pos hm
      faceEdges_eq := squareCenterPolygonFaceEdges_eq
      faceEdge_ends := squareCenterPolygonFaceEdge_ends
      boundaryEdge := squareCenterPolygonBoundaryEdge (n := n) (m := m)
      boundaryEdge_injective := squareCenterPolygonBoundaryEdge_injective (n := n) (m := m)
      boundaryVertex := squareCenterPolygonBoundaryVertex (n := n) (m := m)
      boundaryEdge_ends := squareCenterPolygonBoundaryEdge_ends (n := n) (m := m)
      boundaryEdges_eq := squareCenterPolygonBoundaryEdges_eq (n := n) (m := m)
      vertexPoint := squareCenterPolygonVertexPoint n m
      edgeToX := squareCenterPolygonEdgePath n m
      edgeToX_continuous := continuous_squareCenterPolygonEdgePath n m
      edgeToX_start := squareCenterPolygonEdgePath_start
      edgeToX_finish := squareCenterPolygonEdgePath_finish
      faceCenter := faceCenter
      halfTurn_mesh := by
        intro f e he x
        simp
      boundaryParameter := angularSubdivisionParameter m
      boundaryParameter_continuous := continuous_angularSubdivisionParameter m
      boundaryParameter_start := by
        intro k
        simp [angularSubdivisionParameter, cyclicVertexParameter, closedUnitIntervalStart]
      boundaryParameter_finish := by
        intro k
        simp [angularSubdivisionParameter, cyclicEdgeFinishParameter, closedUnitIntervalFinish, add_comm]
      boundaryPath := by
        intro k x
        rw [show squareCenterPolygonEdgePath n m (squareCenterPolygonBoundaryEdge (n := n) (m := m) k) x =
            closedUnitSquareRadial (cylinderAngularEdgePath n m (Fin.last (n + 1)) k x) by
              simp [squareCenterPolygonEdgePath, squareCenterPolygonBoundaryEdge, radialSubdivisionUpper_last]]
        rw [closedUnitSquareRadial_comp_cylinderBoundary]
        simp [cylinderAngularEdgePath_on_closedUnitSquareCylinderBoundary,
          angularSubdivisionArc, angularSubdivisionParameter] }
  mesh := hmesh

/-- The explicit center-polygon annulus data already yields abstract directed
variable-face-size fine polygonal models as soon as the geometric mesh estimates
are supplied at every scale. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_squareCenterPolygon_data
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ faceCenter : SquareCenterPolygonFace n m → ClosedUnitSquare,
      (∀ (f : SquareCenterPolygonFace n m) (e : SquareCenterPolygonEdge n m),
        e ∈ squareCenterPolygonFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f) (squareCenterPolygonEdgePath n m e x) < ε)) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitSquareBoundary := by
  intro ε hε
  obtain ⟨n, m, hm, faceCenter, hmesh⟩ := hmodels ε hε
  exact ⟨squareCenterPolygonAbstractVariableDirectedGeometricModel_of_mesh
    n m hm faceCenter hmesh⟩



theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_closedUnitSquareBoundary :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitSquareBoundary := by
  apply hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_squareCenterPolygon_data
  intro ε hε
  have hUniform : UniformContinuous closedUnitSquareRadial :=
    CompactSpace.uniformContinuous_of_continuous continuous_closedUnitSquareRadial
  obtain ⟨δ, hδ, hδradial⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < 2)
  have hminpos : 0 < min (ε / Real.sqrt 2) δ := by
    exact lt_min (div_pos hε hsqrt) hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hminpos
  have hnε : 1 / (n + 1 : ℝ) < ε / Real.sqrt 2 := lt_of_lt_of_le hn (min_le_left _ _)
  have hnδ : 1 / (n + 1 : ℝ) < δ := lt_of_lt_of_le hn (min_le_right _ _)
  have hmpos : 0 < min δ (1 / 2 : ℝ) := by
    exact lt_min hδ (by norm_num)
  obtain ⟨m, hmstep⟩ := exists_nat_one_div_lt hmpos
  have hm : 0 < m := by
    by_contra hm0
    have hmz : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst hmz
    norm_num at hmstep
  have hmδ : 1 / (m + 1 : ℝ) < δ := lt_of_lt_of_le hmstep (min_le_left _ _)
  let faceCenter : SquareCenterPolygonFace n m → ClosedUnitSquare
    | .center => closedUnitSquareCenter
    | .annulus i j =>
        closedUnitSquareRadial
          (cylinderSubdivisionPoint n m (radialSubdivisionLower (upperSquareRingLevel i)) j)
  refine ⟨n, m, hm, faceCenter, ?_⟩
  intro f e he x
  cases f with
  | center =>
      cases e with
      | radial i j =>
          exact False.elim ((mem_squareCenterPolygonFaceEdges_center_radial_iff i j).1 he)
      | angular i j =>
          have hi : i = 0 := (mem_squareCenterPolygonFaceEdges_center_angular_iff i j).1 he
          subst hi
          have hdist := dist_closedUnitSquareCenter_closedUnitSquareRadial_le
            (radialSubdivisionPoint n (radialSubdivisionUpper 0)) (angularSubdivisionArc m j x)
          have hr : ((radialSubdivisionPoint n (radialSubdivisionUpper 0) : ClosedUnitInterval) : ℝ) =
              1 / (n + 1 : ℝ) := by
            simp [radialSubdivisionPoint, radialSubdivisionUpper]
          have hmul : (1 / (n + 1 : ℝ)) * Real.sqrt 2 < ε := by
            calc
              (1 / (n + 1 : ℝ)) * Real.sqrt 2 < (ε / Real.sqrt 2) * Real.sqrt 2 := by
                gcongr
              _ = ε := by
                field_simp [hsqrt.ne']
          have hdist' : dist (faceCenter SquareCenterPolygonFace.center)
                (squareCenterPolygonEdgePath n m (SquareCenterPolygonEdge.angular 0 j) x) ≤
                  (1 / (n + 1 : ℝ)) * Real.sqrt 2 := by
            simpa [faceCenter, squareCenterPolygonEdgePath, hr] using hdist
          exact hdist'.trans_lt hmul
  | annulus i j =>
      cases e with
      | radial i' j' =>
          rcases (mem_squareCenterPolygonFaceEdges_annulus_radial_iff i i' j j').1 he with ⟨hi', hj'⟩
          subst hi'
          rcases hj' with rfl | hsucc
          · have hsrc :
                dist
                  (cylinderSubdivisionPoint n m (radialSubdivisionLower (upperSquareRingLevel i)) j)
                  (cylinderRadialEdgePath n m (upperSquareRingLevel i) j x) < δ := by
              rw [cylinderSubdivisionPoint, cylinderRadialEdgePath, Prod.dist_eq]
              refine max_lt_iff.2 ?_
              constructor
              · simpa [cylinderSubdivisionPoint, cylinderRadialEdgePath, dist_comm,
                  radialSubdivisionLower_upperSquareRingLevel] using
                  (dist_radialSubdivisionArc_start_le n (upperSquareRingLevel i) x).trans_lt hnδ
              · simpa
            simpa [faceCenter, squareCenterPolygonEdgePath] using hδradial hsrc
          · subst j'
            have hang :
                dist (angularSubdivisionPoint m j) (angularSubdivisionPoint m (cyclicSucc j)) < δ := by
              exact (dist_angularSubdivisionPoint_cyclicSucc_le m hm j).trans_lt hmδ
            have hsrc :
                dist
                  (cylinderSubdivisionPoint n m (radialSubdivisionLower (upperSquareRingLevel i)) j)
                  (cylinderRadialEdgePath n m (upperSquareRingLevel i) (cyclicSucc j) x) < δ := by
              rw [cylinderSubdivisionPoint, cylinderRadialEdgePath, Prod.dist_eq]
              refine max_lt_iff.2 ?_
              constructor
              · simpa [cylinderSubdivisionPoint, cylinderRadialEdgePath, dist_comm,
                  radialSubdivisionLower_upperSquareRingLevel] using
                  (dist_radialSubdivisionArc_start_le n (upperSquareRingLevel i) x).trans_lt hnδ
              · simpa [cylinderSubdivisionPoint, cylinderRadialEdgePath, dist_comm] using hang
            simpa [faceCenter, squareCenterPolygonEdgePath] using hδradial hsrc
      | angular i' j' =>
          rcases (mem_squareCenterPolygonFaceEdges_annulus_angular_iff i' i j' j).1 he with h | h
          · rcases h with ⟨hi', hj'⟩
            subst hi'; subst hj'
            have hsrc :
                dist
                  (cylinderSubdivisionPoint n m (radialSubdivisionLower (upperSquareRingLevel i)) j)
                  (cylinderAngularEdgePath n m (radialSubdivisionUpper (upperSquareRingLevel i)) j x) < δ := by
              rw [cylinderSubdivisionPoint, cylinderAngularEdgePath, Prod.dist_eq]
              refine max_lt_iff.2 ?_
              constructor
              · simpa [cylinderSubdivisionPoint, cylinderAngularEdgePath, dist_comm] using
                  (dist_radialSubdivision_upper_lower_le n (upperSquareRingLevel i)).trans_lt hnδ
              · simpa [cylinderSubdivisionPoint, cylinderAngularEdgePath, dist_comm] using
                  (dist_angularSubdivisionArc_point_le m hm j x).trans_lt hmδ
            simpa [faceCenter, squareCenterPolygonEdgePath] using hδradial hsrc
          · rcases h with ⟨hi', hj'⟩
            subst hi'; subst hj'
            have hsrc :
                dist
                  (cylinderSubdivisionPoint n m (radialSubdivisionLower (upperSquareRingLevel i)) j)
                  (cylinderAngularEdgePath n m (radialSubdivisionUpper (lowerSquareRingLevel i)) j x) < δ := by
              rw [cylinderSubdivisionPoint, cylinderAngularEdgePath, Prod.dist_eq]
              refine max_lt_iff.2 ?_
              constructor
              · simpa [cylinderSubdivisionPoint, cylinderAngularEdgePath,
                  radialSubdivisionLower_upperSquareRingLevel] using hδ
              · simpa [cylinderSubdivisionPoint, cylinderAngularEdgePath, dist_comm] using
                  (dist_angularSubdivisionArc_point_le m hm j x).trans_lt hmδ
            simpa [faceCenter, squareCenterPolygonEdgePath] using hδradial hsrc

/-- The explicit square-center construction immediately yields the directed
closed-disk boundary model family via the radial square-to-disk map. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_closedUnitDiskBoundary :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_closedUnitSquare
    hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_closedUnitSquareBoundary

/-- Any compact metric boundary identified with the standard closed-disk
boundary inherits the directed variable-face-size abstract arbitrarily fine
polygonal-model interface from the explicit square-center disk construction. -/
theorem hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary) :
    HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary :=
  hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_homeomorph e hboundary
    hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_closedUnitDiskBoundary

/-- The same disk-homeomorphic hypothesis also yields the map-dependent directed
fine polygonal-model interface after the compact uniform-continuity step. -/
theorem hasAbstractVariableDirectedFinePolygonalModels_of_closedUnitDisk_homeomorph
    {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary) :
    HasAbstractVariableDirectedFinePolygonalModels boundary :=
  hasAbstractVariableDirectedFinePolygonalModels_of_abstractVariableDirectedArbitrarilyFine
    (hasAbstractVariableDirectedArbitrarilyFinePolygonalModels_of_closedUnitDisk_homeomorph
      e hboundary)


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

private theorem mem_image_equiv_iff
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) (b : β) :
    b ∈ s.image e ↔ e.symm b ∈ s := by
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, hab⟩
    have hsymm : a = e.symm b := by
      simpa using congrArg e.symm hab
    simpa [hsymm] using ha
  · intro hb
    exact Finset.mem_image.mpr ⟨e.symm b, hb, by simp⟩

noncomputable def AbstractFinePolygonalModel.vertexEquiv
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractFinePolygonalModel boundary H) :
    D.Vertex ≃ Fin (Nat.card D.Vertex) := by
  classical
  let _ := D.instVertexFintype
  exact Finite.equivFin D.Vertex

noncomputable def AbstractFinePolygonalModel.edgeEquiv
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractFinePolygonalModel boundary H) :
    D.Edge ≃ Fin (Nat.card D.Edge) := by
  classical
  let _ := D.instEdgeFintype
  exact Finite.equivFin D.Edge

noncomputable def AbstractFinePolygonalModel.faceEquiv
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractFinePolygonalModel boundary H) :
    D.Face ≃ Fin (Nat.card D.Face) := by
  classical
  let _ := D.instFaceFintype
  exact Finite.equivFin D.Face

/-- Every abstract finite-index polygonal model can be reindexed to the
concrete `Fin`-indexed interface. -/
noncomputable def AbstractFinePolygonalModel.toFinePolygonalModel
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {H : X → UnitAddCircle}
    (D : AbstractFinePolygonalModel boundary H) :
    FinePolygonalModel boundary H := by
  classical
  let _ := D.instVertexFintype
  let _ := D.instEdgeFintype
  let _ := D.instFaceFintype
  let _ := D.instVertexDecidableEq
  let _ := D.instEdgeDecidableEq
  let _ := D.instFaceDecidableEq
  let vertexEquiv := D.vertexEquiv
  let edgeEquiv := D.edgeEquiv
  let faceEquiv := D.faceEquiv
  let edgeEnds' : Fin (Nat.card D.Edge) → Fin (Nat.card D.Vertex) × Fin (Nat.card D.Vertex) :=
    fun e ↦
      (vertexEquiv (D.edgeEnds (edgeEquiv.symm e)).1,
        vertexEquiv (D.edgeEnds (edgeEquiv.symm e)).2)
  let faceEdges' : Fin (Nat.card D.Face) → Finset (Fin (Nat.card D.Edge)) :=
    fun f ↦ (D.faceEdges (faceEquiv.symm f)).image edgeEquiv
  let boundaryEdges' : Finset (Fin (Nat.card D.Edge)) :=
    D.boundaryEdges.image edgeEquiv
  let faceVertex' : Fin (Nat.card D.Face) → Fin (D.faceSize + 1) → Fin (Nat.card D.Vertex) :=
    fun f k ↦ vertexEquiv (D.faceVertex (faceEquiv.symm f) k)
  let faceEdge' : Fin (Nat.card D.Face) → Fin (D.faceSize + 1) → Fin (Nat.card D.Edge) :=
    fun f k ↦ edgeEquiv (D.faceEdge (faceEquiv.symm f) k)
  let boundaryEdge' : Fin (D.boundarySize + 1) → Fin (Nat.card D.Edge) :=
    fun k ↦ edgeEquiv (D.boundaryEdge k)
  let boundaryVertex' : Fin (D.boundarySize + 1) → Fin (Nat.card D.Vertex) :=
    fun k ↦ vertexEquiv (D.boundaryVertex k)
  let vertexPoint' : Fin (Nat.card D.Vertex) → X :=
    fun v ↦ D.vertexPoint (vertexEquiv.symm v)
  let edgeToX' : Fin (Nat.card D.Edge) → ClosedUnitInterval → X :=
    fun e ↦ D.edgeToX (edgeEquiv.symm e)
  let faceCenter' : Fin (Nat.card D.Face) → X :=
    fun f ↦ D.faceCenter (faceEquiv.symm f)
  refine
    { vertexCount := Nat.card D.Vertex
      edgeCount := Nat.card D.Edge
      faceCount := Nat.card D.Face
      faceSize := D.faceSize
      boundarySize := D.boundarySize
      edgeEnds := edgeEnds'
      faceEdges := faceEdges'
      boundaryEdges := boundaryEdges'
      edgeFaceCount := ?_
      faceVertex := faceVertex'
      faceEdge := faceEdge'
      faceVertex_injective := ?_
      faceEdge_injective := ?_
      faceEdges_eq := ?_
      faceEdge_ends := ?_
      boundaryEdge := boundaryEdge'
      boundaryEdge_injective := ?_
      boundaryVertex := boundaryVertex'
      boundaryEdge_ends := ?_
      boundaryEdges_eq := ?_
      vertexPoint := vertexPoint'
      edgeToX := edgeToX'
      edgeToX_continuous := ?_
      edgeToX_start := ?_
      edgeToX_finish := ?_
      faceCenter := faceCenter'
      halfTurn_mesh := ?_
      boundaryParameter := D.boundaryParameter
      boundaryParameter_continuous := D.boundaryParameter_continuous
      boundaryParameter_start := D.boundaryParameter_start
      boundaryParameter_finish := D.boundaryParameter_finish
      boundaryPath := ?_ }
  · intro e
    have hfilter :
        (Finset.univ.filter fun f : Fin (Nat.card D.Face) ↦ e ∈ faceEdges' f) =
          (Finset.univ.filter fun f : D.Face ↦ edgeEquiv.symm e ∈ D.faceEdges f).image faceEquiv := by
      ext f
      constructor
      · intro hf
        have hmem : e ∈ faceEdges' f := (Finset.mem_filter.mp hf).2
        have hmem' : edgeEquiv.symm e ∈ D.faceEdges (faceEquiv.symm f) := by
          unfold faceEdges' at hmem
          exact (mem_image_equiv_iff edgeEquiv (D.faceEdges (faceEquiv.symm f)) e).1 hmem
        exact Finset.mem_image.mpr ⟨faceEquiv.symm f,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem'⟩, by simp⟩
      · intro hf
        rcases Finset.mem_image.mp hf with ⟨a, ha, haf⟩
        have ha' : a = faceEquiv.symm f := by
          simpa using congrArg faceEquiv.symm haf
        have hmem' : edgeEquiv.symm e ∈ D.faceEdges (faceEquiv.symm f) := by
          simpa [ha'] using (Finset.mem_filter.mp ha).2
        have hmem : e ∈ faceEdges' f := by
          unfold faceEdges'
          exact (mem_image_equiv_iff edgeEquiv (D.faceEdges (faceEquiv.symm f)) e).2 hmem'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    have hboundaryMem : e ∈ boundaryEdges' ↔ edgeEquiv.symm e ∈ D.boundaryEdges := by
      unfold boundaryEdges'
      simpa using (mem_image_equiv_iff edgeEquiv D.boundaryEdges e)
    calc
      (Finset.univ.filter fun f : Fin (Nat.card D.Face) ↦ e ∈ faceEdges' f).card
          = ((Finset.univ.filter fun f : D.Face ↦ edgeEquiv.symm e ∈ D.faceEdges f).image faceEquiv).card := by
            rw [hfilter]
      _ = (Finset.univ.filter fun f : D.Face ↦ edgeEquiv.symm e ∈ D.faceEdges f).card := by
            rw [Finset.card_image_of_injective _ faceEquiv.injective]
      _ = if edgeEquiv.symm e ∈ D.boundaryEdges then 1 else 2 :=
            D.edgeFaceCount (edgeEquiv.symm e)
      _ = if e ∈ boundaryEdges' then 1 else 2 := by
            by_cases h : edgeEquiv.symm e ∈ D.boundaryEdges
            · have he : e ∈ boundaryEdges' := hboundaryMem.mpr h
              simp [h, he]
            · have he : e ∉ boundaryEdges' := by
                intro he
                exact h (hboundaryMem.mp he)
              simp [h, he]
  · intro f
    exact vertexEquiv.injective.comp (D.faceVertex_injective (faceEquiv.symm f))
  · intro f
    exact edgeEquiv.injective.comp (D.faceEdge_injective (faceEquiv.symm f))
  · intro f
    unfold faceEdges' faceEdge'
    simpa [Finset.image_image] using congrArg (Finset.image edgeEquiv) (D.faceEdges_eq (faceEquiv.symm f))
  · intro f k
    apply Prod.ext
    · change (edgeEnds' (faceEdge' f k)).1 = faceVertex' f k
      unfold edgeEnds' faceEdge' faceVertex'
      simpa using congrArg Prod.fst (D.faceEdge_ends (faceEquiv.symm f) k)
    · change (edgeEnds' (faceEdge' f k)).2 = faceVertex' f (cyclicSucc k)
      unfold edgeEnds' faceEdge' faceVertex'
      simpa using congrArg Prod.snd (D.faceEdge_ends (faceEquiv.symm f) k)
  · exact edgeEquiv.injective.comp D.boundaryEdge_injective
  · intro k
    apply Prod.ext
    · change (edgeEnds' (boundaryEdge' k)).1 = boundaryVertex' k
      unfold edgeEnds' boundaryEdge' boundaryVertex'
      simpa using congrArg Prod.fst (D.boundaryEdge_ends k)
    · change (edgeEnds' (boundaryEdge' k)).2 = boundaryVertex' (cyclicSucc k)
      unfold edgeEnds' boundaryEdge' boundaryVertex'
      simpa using congrArg Prod.snd (D.boundaryEdge_ends k)
  · unfold boundaryEdges' boundaryEdge'
    simpa [Finset.image_image] using congrArg (Finset.image edgeEquiv) D.boundaryEdges_eq
  · intro e
    simpa [edgeToX'] using D.edgeToX_continuous (edgeEquiv.symm e)
  · intro e
    unfold edgeToX' vertexPoint' edgeEnds'
    simpa using D.edgeToX_start (edgeEquiv.symm e)
  · intro e
    unfold edgeToX' vertexPoint' edgeEnds'
    simpa using D.edgeToX_finish (edgeEquiv.symm e)
  · intro f e he x
    have he' : edgeEquiv.symm e ∈ D.faceEdges (faceEquiv.symm f) := by
      unfold faceEdges' at he
      exact (mem_image_equiv_iff edgeEquiv (D.faceEdges (faceEquiv.symm f)) e).1 he
    exact D.halfTurn_mesh (faceEquiv.symm f) (edgeEquiv.symm e) he' x
  · intro k x
    unfold edgeToX' boundaryEdge'
    simpa using D.boundaryPath k x

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

/-- The abstract finite-index interface also yields the concrete `Fin`-indexed
one by reindexing all finite types by `Fin`. -/
theorem hasFinePolygonalModels_of_abstractFinePolygonalModels
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X}
    (hfine : HasAbstractFinePolygonalModels boundary) :
    HasFinePolygonalModels boundary := by
  intro H hH
  obtain ⟨D⟩ := hfine H hH
  exact ⟨D.toFinePolygonalModel⟩

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


/-- An abstract geometric polygonal model indexed by arbitrary finite types.  This is
convenient for explicit mesh constructions before choosing concrete `Fin` encodings of
vertices, edges, and faces. -/
structure AbstractGeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (ε : ℝ) where
  model : AbstractFinePolygonalModel boundary (fun _ ↦ (0 : UnitAddCircle))
  mesh : ∀ (f : model.Face) (e : model.Edge),
    e ∈ model.faceEdges f → ∀ x : ClosedUnitInterval,
      dist (model.faceCenter f) (model.edgeToX e x) < ε

/-- Replace the vacuous constant-map half-turn estimate in an abstract geometric
model by a supplied estimate for a particular circle-valued map. -/
def AbstractGeometricPolygonalModel.toAbstractFinePolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : AbstractGeometricPolygonalModel boundary ε)
    (H : X → UnitAddCircle)
    (hhalf : ∀ (f : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges f → ∀ x : ClosedUnitInterval,
        dist (H (D.model.faceCenter f)) (H (D.model.edgeToX e x)) < 1 / 2) :
    AbstractFinePolygonalModel boundary H :=
  { D.model with halfTurn_mesh := hhalf }

/-- Every abstract geometric polygonal model can be reindexed to the concrete
`Fin`-indexed geometric interface. -/
noncomputable def AbstractGeometricPolygonalModel.toGeometricPolygonalModel
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {ε : ℝ}
    (D : AbstractGeometricPolygonalModel boundary ε) :
    GeometricPolygonalModel boundary ε := by
  classical
  let _ := D.model.instVertexFintype
  let _ := D.model.instEdgeFintype
  let _ := D.model.instFaceFintype
  let _ := D.model.instVertexDecidableEq
  let _ := D.model.instEdgeDecidableEq
  let _ := D.model.instFaceDecidableEq
  let faceEquiv := D.model.faceEquiv
  let edgeEquiv := D.model.edgeEquiv
  refine
    { model := D.model.toFinePolygonalModel
      mesh := ?_ }
  intro f e he x
  have he' : edgeEquiv.symm e ∈ D.model.faceEdges (faceEquiv.symm f) := by
    change e ∈ (D.model.faceEdges (faceEquiv.symm f)).image edgeEquiv at he
    exact (mem_image_equiv_iff edgeEquiv (D.model.faceEdges (faceEquiv.symm f)) e).1 he
  exact D.mesh (faceEquiv.symm f) (edgeEquiv.symm e) he' x

/-- Push an abstract geometric polygonal model forward along a continuous map whose
restriction to the boundary agrees with a new parametrization. -/
def AbstractGeometricPolygonalModel.map
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    {δ ε : ℝ} (D : AbstractGeometricPolygonalModel boundary δ)
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmesh : ∀ (face : D.model.Face) (e : D.model.Edge),
      e ∈ D.model.faceEdges face → ∀ x : ClosedUnitInterval,
        dist (f (D.model.faceCenter face)) (f (D.model.edgeToX e x)) < ε) :
    AbstractGeometricPolygonalModel boundary' ε :=
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
          simp
        boundaryPath := by
          intro k x
          rw [hboundary]
          simpa using congrArg f (D.model.boundaryPath k x) }
    mesh := hmesh }

/-- The abstract map-independent surface input: compatible polygonal models exist
at every positive geometric mesh scale, with arbitrary finite index sets. -/
def HasAbstractArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (AbstractGeometricPolygonalModel boundary ε)

/-- Bundle explicit checkerboard-cylinder data into the ordinary abstract
geometric polygonal-model interface on the square-cylinder boundary. -/
def cylinderCoreAbstractGeometricModel_of_mesh
    {ε : ℝ} (n m : ℕ) (hm : 0 < m)
    (hedgeFaceCount : ∀ e : CylinderCoreEdge n m,
      (Finset.univ.filter fun f ↦ e ∈ cylinderCoreFaceEdges f).card =
        if e ∈ cylinderCoreBoundaryEdges (n := n) (m := m) then 1 else 2)
    (faceCenter : CylinderCoreFace n m → ClosedUnitInterval × UnitAddCircle)
    (hmesh : ∀ (f : CylinderCoreFace n m) (e : CylinderCoreEdge n m),
      e ∈ cylinderCoreFaceEdges f → ∀ x : ClosedUnitInterval,
        dist (faceCenter f) (cylinderCoreEdgePath n m e x) < ε) :
    AbstractGeometricPolygonalModel closedUnitSquareCylinderBoundary ε where
  model :=
    { Vertex := CylinderCoreVertex n m
      Edge := CylinderCoreEdge n m
      Face := CylinderCoreFace n m
      faceSize := 3
      boundarySize := m
      edgeEnds := cylinderCoreEdgeEnds
      faceEdges := cylinderCoreFaceEdges
      boundaryEdges := cylinderCoreBoundaryEdges (n := n) (m := m)
      edgeFaceCount := hedgeFaceCount
      faceVertex := cylinderCoreFaceVertex
      faceEdge := cylinderCoreFaceEdge
      faceVertex_injective := cylinderCoreFaceVertex_injective_of_pos hm
      faceEdge_injective := cylinderCoreFaceEdge_injective
      faceEdges_eq := cylinderCoreFaceEdges_eq
      faceEdge_ends := cylinderCoreFaceEdge_ends
      boundaryEdge := cylinderCoreBoundaryEdge (n := n) (m := m)
      boundaryEdge_injective := cylinderCoreBoundaryEdge_injective (n := n) (m := m)
      boundaryVertex := cylinderCoreBoundaryVertex (n := n) (m := m)
      boundaryEdge_ends := cylinderCoreBoundaryEdge_ends (n := n) (m := m)
      boundaryEdges_eq := cylinderCoreBoundaryEdges_eq (n := n) (m := m)
      vertexPoint := fun v ↦ cylinderSubdivisionPoint n m v.1 v.2
      edgeToX := cylinderCoreEdgePath n m
      edgeToX_continuous := continuous_cylinderCoreEdgePath n m
      edgeToX_start := by
        intro e
        simpa using cylinderCoreEdgePath_start (n := n) (m := m) e
      edgeToX_finish := by
        intro e
        simpa using cylinderCoreEdgePath_finish (n := n) (m := m) e
      faceCenter := faceCenter
      halfTurn_mesh := by
        intro f e he x
        simp
      boundaryParameter := fun k ↦ angularSubdivisionParameter m k
      boundaryParameter_continuous := continuous_angularSubdivisionParameter m
      boundaryParameter_start := by
        intro k
        simp [angularSubdivisionParameter, cyclicVertexParameter, closedUnitIntervalStart]
      boundaryParameter_finish := by
        intro k
        simp [angularSubdivisionParameter, cyclicEdgeFinishParameter, closedUnitIntervalFinish, add_comm]
      boundaryPath := by
        intro k x
        simpa [angularSubdivisionArc, angularSubdivisionParameter] using
          cylinderCoreBoundaryEdgePath_eq (n := n) (m := m) k x }
  mesh := hmesh

/-- A source-level wrapper reducing the ordinary abstract square-cylinder
existence theorem to explicit checkerboard-cylinder data. -/
theorem hasAbstractArbitrarilyFinePolygonalModels_of_cylinderCore_data
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ hm : 0 < m,
      ∃ hedgeFaceCount : ∀ e : CylinderCoreEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderCoreFaceEdges f).card =
          if e ∈ cylinderCoreBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderCoreFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderCoreFace n m) (e : CylinderCoreEdge n m),
        e ∈ cylinderCoreFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f) (cylinderCoreEdgePath n m e x) < ε) :
    HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareCylinderBoundary := by
  intro ε hε
  obtain ⟨n, m, hm, hedgeFaceCount, faceCenter, hmesh⟩ := hmodels ε hε
  exact ⟨cylinderCoreAbstractGeometricModel_of_mesh n m hm hedgeFaceCount faceCenter hmesh⟩


/-- Abstract arbitrarily fine polygonal models transport across continuous maps from a
compact source by uniform continuity. -/
theorem hasAbstractArbitrarilyFinePolygonalModels_of_compact_continuous
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (f : X → Y) (hf : Continuous f)
    (hboundary : boundary' = f ∘ boundary)
    (hmodels : HasAbstractArbitrarilyFinePolygonalModels boundary) :
    HasAbstractArbitrarilyFinePolygonalModels boundary' := by
  intro ε hε
  have hUniform : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.uniformContinuous_iff.mp hUniform ε hε
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.map f hf hboundary ?_⟩
  intro face e he x
  exact hδf (D.mesh face e he x)

/-- Homeomorphic compact images inherit abstract arbitrarily fine polygonal models. -/
theorem hasAbstractArbitrarilyFinePolygonalModels_of_homeomorph
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y}
    (e : X ≃ₜ Y)
    (hboundary : boundary' = e ∘ boundary)
    (hmodels : HasAbstractArbitrarilyFinePolygonalModels boundary) :
    HasAbstractArbitrarilyFinePolygonalModels boundary' :=
  hasAbstractArbitrarilyFinePolygonalModels_of_compact_continuous
    e e.continuous_toFun hboundary hmodels

/-- Abstract closed-square models transfer to abstract closed-disk models through the
radial square-to-disk map. -/
theorem hasAbstractArbitrarilyFinePolygonalModels_of_closedUnitSquare
    (hsquare : HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareBoundary) :
    HasAbstractArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasAbstractArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareToDisk continuous_closedUnitSquareToDisk
    closedUnitSquareToDisk_comp_boundary hsquare

/-- A sufficiently fine abstract polygonal model on the radial cylinder boundary
pushes forward directly to the closed unit square boundary.  This isolates the
remaining existence theorem to one explicit cone-mesh construction. -/
theorem hasAbstractArbitrarilyFinePolygonalModels_of_closedUnitSquareCylinderBoundary
    (hcyl : HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareCylinderBoundary) :
    HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareBoundary :=
  hasAbstractArbitrarilyFinePolygonalModels_of_compact_continuous
    closedUnitSquareRadial continuous_closedUnitSquareRadial
    closedUnitSquareRadial_comp_cylinderBoundary hcyl

/-- On a compact metric domain, abstract arbitrarily fine geometric polygonal models
provide the map-dependent abstract fine models needed by the mod-two argument. -/
theorem hasAbstractFinePolygonalModels_of_abstractArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractArbitrarilyFinePolygonalModels boundary) :
    HasAbstractFinePolygonalModels boundary := by
  intro H hH
  have hUniform : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hδH⟩ :=
    Metric.uniformContinuous_iff.mp hUniform (1 / 2) (by norm_num)
  obtain ⟨D⟩ := hmodels δ hδ
  refine ⟨D.toAbstractFinePolygonalModel H ?_⟩
  intro f e he x
  exact hδH (D.mesh f e he x)

/-- Abstract arbitrarily fine compatible geometric models imply the odd boundary-degree
obstruction. -/
theorem hasOddBoundaryDegreeObstruction_of_abstractArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractArbitrarilyFinePolygonalModels boundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_abstractFinePolygonalModels
    (hasAbstractFinePolygonalModels_of_abstractArbitrarilyFine hmodels)

/-- The map-independent surface input: compatible polygonal models exist
at every positive geometric mesh scale. -/
def HasArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (GeometricPolygonalModel boundary ε)

/-- Abstract arbitrarily fine geometric polygonal models also yield the
concrete `Fin`-indexed geometric interface by reindexing each finite model. -/
theorem hasArbitrarilyFinePolygonalModels_of_abstractArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X}
    (hmodels : HasAbstractArbitrarilyFinePolygonalModels boundary) :
    HasArbitrarilyFinePolygonalModels boundary := by
  intro ε hε
  obtain ⟨D⟩ := hmodels ε hε
  exact ⟨D.toGeometricPolygonalModel⟩

/-- Abstract closed-square models already imply the concrete closed-disk
geometric interface used downstream: first transfer abstractly across the
square-to-disk map, then reindex the finite types by `Fin`. -/
theorem hasArbitrarilyFinePolygonalModels_of_abstract_closedUnitSquare
    (hsquare : HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareBoundary) :
    HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasArbitrarilyFinePolygonalModels_of_abstractArbitrarilyFine
    (hasAbstractArbitrarilyFinePolygonalModels_of_closedUnitSquare hsquare)

/-- The same radial-cylinder input already yields the concrete closed-disk
polygonal-model interface used downstream, via the square transfer and finite
reindexing lemmas formalized above. -/
theorem hasArbitrarilyFinePolygonalModels_of_closedUnitSquareCylinderBoundary
    (hcyl : HasAbstractArbitrarilyFinePolygonalModels closedUnitSquareCylinderBoundary) :
    HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary :=
  hasArbitrarilyFinePolygonalModels_of_abstract_closedUnitSquare
    (hasAbstractArbitrarilyFinePolygonalModels_of_closedUnitSquareCylinderBoundary hcyl)

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

/-- Once the closed unit disk is proved to have arbitrarily fine polygonal
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
    (_hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundary

end

end GromovFilling
