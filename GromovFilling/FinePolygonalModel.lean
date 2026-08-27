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

@[simp] theorem radialSubdivisionUpper_last {n : ℕ} :
    radialSubdivisionUpper (Fin.last n) = Fin.last (n + 1) := by
  apply Fin.ext
  simp [radialSubdivisionUpper]

/-- Vertices of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskVertex (n m : ℕ)
  | center
  | ring (i : Fin (n + 1)) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Edges of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskEdge (n m : ℕ)
  | spoke (j : Fin (m + 1))
  | radial (i : Fin n) (j : Fin (m + 1))
  | angular (i : Fin (n + 1)) (j : Fin (m + 1))
  | diagonal (i : Fin n) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Faces of the disk-like radial mesh in the closed unit square. -/
inductive SquareDiskFace (n m : ℕ)
  | center (j : Fin (m + 1))
  | lower (i : Fin n) (j : Fin (m + 1))
  | upper (i : Fin n) (j : Fin (m + 1))
  deriving DecidableEq, Fintype

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
  | .spoke j => (.center, .ring 0 j)
  | .radial i j => (.ring (lowerSquareRingLevel i) j, .ring (upperSquareRingLevel i) j)
  | .angular i j => (.ring i j, .ring i (cyclicSucc j))
  | .diagonal i j => (.ring (lowerSquareRingLevel i) j, .ring (upperSquareRingLevel i) (cyclicSucc j))

/-- Edge paths in the closed unit square. -/
def squareDiskEdgePath (n m : ℕ) : SquareDiskEdge n m → ClosedUnitInterval → ClosedUnitSquare
  | .spoke j =>
      fun x ↦ closedUnitSquareRadial (radialSubdivisionArc n 0 x, angularSubdivisionPoint m j)
  | .radial i j =>
      fun x ↦ closedUnitSquareRadial (cylinderRadialEdgePath n m (upperSquareRingLevel i) j x)
  | .angular i j =>
      fun x ↦ closedUnitSquareRadial (cylinderAngularEdgePath n m (radialSubdivisionUpper i) j x)
  | .diagonal i j =>
      fun x ↦ closedUnitSquareRadial (cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j x)

theorem continuous_squareDiskEdgePath (n m : ℕ) (e : SquareDiskEdge n m) :
    Continuous (squareDiskEdgePath n m e) := by
  cases e with
  | spoke j =>
      exact continuous_closedUnitSquareRadial.comp <|
        (continuous_radialSubdivisionArc n 0).prodMk continuous_const
  | radial i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderRadialEdgePath n m (upperSquareRingLevel i) j
  | angular i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderAngularEdgePath n m (radialSubdivisionUpper i) j
  | diagonal i j =>
      exact continuous_closedUnitSquareRadial.comp <|
        continuous_cylinderDiagonalEdgePath n m (upperSquareRingLevel i) j

theorem squareDiskEdgePath_start {n m : ℕ} (e : SquareDiskEdge n m) :
    squareDiskEdgePath n m e closedUnitIntervalStart =
      squareDiskVertexPoint n m (squareDiskEdgeEnds e).1 := by
  cases e with
  | spoke j =>
      simpa [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        radialSubdivisionArc_start, radialSubdivisionPoint_zero,
        radialSubdivisionLower] using
        closedUnitSquareRadial_start (angularSubdivisionPoint m j)
  | radial i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderRadialEdgePath_start, cylinderSubdivisionPoint,
        radialSubdivisionLower_upperSquareRingLevel]
  | angular i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderAngularEdgePath_start, cylinderSubdivisionPoint]
  | diagonal i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderDiagonalEdgePath_start, cylinderSubdivisionPoint,
        radialSubdivisionLower_upperSquareRingLevel]

theorem squareDiskEdgePath_finish {n m : ℕ} (e : SquareDiskEdge n m) :
    squareDiskEdgePath n m e closedUnitIntervalFinish =
      squareDiskVertexPoint n m (squareDiskEdgeEnds e).2 := by
  cases e with
  | spoke j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        radialSubdivisionArc_finish]
  | radial i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderRadialEdgePath_finish, cylinderSubdivisionPoint]
  | angular i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderAngularEdgePath_finish, cylinderSubdivisionPoint]
  | diagonal i j =>
      simp [squareDiskEdgePath, squareDiskEdgeEnds, squareDiskVertexPoint,
        cylinderDiagonalEdgePath_finish, cylinderSubdivisionPoint]

/-- Boundary vertices of the disk-like radial mesh. -/
def squareDiskBoundaryVertex {n m : ℕ} (j : Fin (m + 1)) : SquareDiskVertex n m :=
  .ring (Fin.last n) j

/-- Boundary edges of the disk-like radial mesh. -/
def squareDiskBoundaryEdge {n m : ℕ} (j : Fin (m + 1)) : SquareDiskEdge n m :=
  .angular (Fin.last n) j

@[simp] theorem squareDiskBoundaryEdge_ends {n m : ℕ} (j : Fin (m + 1)) :
    squareDiskEdgeEnds (squareDiskBoundaryEdge (n := n) (m := m) j) =
      (squareDiskBoundaryVertex (n := n) (m := m) j,
        squareDiskBoundaryVertex (n := n) (m := m) (cyclicSucc j)) := by
  simp [squareDiskBoundaryEdge, squareDiskBoundaryVertex, squareDiskEdgeEnds]

@[simp] theorem squareDiskBoundaryEdgePath_eq {n m : ℕ} (j : Fin (m + 1)) :
    squareDiskEdgePath n m (squareDiskBoundaryEdge (n := n) (m := m) j) =
      fun x ↦ closedUnitSquareRadial
        (cylinderAngularEdgePath n m (Fin.last (n + 1)) j x) := by
  funext x
  simp [squareDiskBoundaryEdge, squareDiskEdgePath]


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
    (_hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    HasOddBoundaryDegreeObstruction boundary :=
  hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundary

end

end GromovFilling
