import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.AddCircle.Defs
import GromovFilling.FinePolygonalModel

/-!
# Closed one-forms and path homotopy

This file packages the homotopy invariance of curve integrals of closed
`1`-forms in the exact form useful for future oriented-surface arguments.
The underlying analytic result is already in Mathlib for continuous-map
homotopies; here we specialize it to path homotopies with fixed endpoints,
so the vertical boundary terms vanish automatically.
-/

open Set
open scoped unitInterval

namespace GromovFilling

noncomputable section

section PathHomotopy

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  {x₀ x₁ : E} {γ₀ γ₁ : Path x₀ x₁}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Path.Homotopy.curveIntegral_evalAt_zero_eq_zero
    {ω : E → E →L[𝕜] F} (φ : γ₀.Homotopy γ₁) :
    ∫ᶜ x in φ.evalAt (0 : I), ω x = 0 := by
  rw [show φ.evalAt (0 : I) = (Path.refl x₀).cast γ₀.source γ₁.source by
    ext t
    simp [ContinuousMap.Homotopy.evalAt]]
  simp

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma Path.Homotopy.curveIntegral_evalAt_one_eq_zero
    {ω : E → E →L[𝕜] F} (φ : γ₀.Homotopy γ₁) :
    ∫ᶜ x in φ.evalAt (1 : I), ω x = 0 := by
  rw [show φ.evalAt (1 : I) = (Path.refl x₁).cast γ₀.target γ₁.target by
    ext t
    simp [ContinuousMap.Homotopy.evalAt]]
  simp

/-- A closed `1`-form has the same curve integral along homotopic paths with
fixed endpoints. This is the path-level version of Mathlib's square-homotopy
identity, with the vertical edge integrals collapsing to zero because a path
homotopy fixes the endpoints. -/
theorem Path.Homotopy.curveIntegral_eq_of_hasFDerivWithinAt
    {t : Set E}
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : γ₀.Homotopy γ₁)
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
      (t := t) (ω := ω) (dω := dω) hφt hω hωc hdω_symm hcontdiff
  have h0 := Path.Homotopy.curveIntegral_evalAt_zero_eq_zero (ω := ω) φ
  have h1 := Path.Homotopy.curveIntegral_evalAt_one_eq_zero (ω := ω) φ
  calc
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x := by
      rw [h1, add_zero]
    _ = ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := h
    _ = ∫ᶜ x in γ₁, ω x := by
      rw [h0, add_zero]

/-- A closed `1`-form has the same curve integral along homotopic paths with
fixed endpoints. This `DiffContOnCl` version is convenient for chart-level
applications. -/
theorem Path.Homotopy.curveIntegral_eq_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    (φ : γ₀.Homotopy γ₁)
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h :=
    φ.toHomotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
      (t := t) (ω := ω) hφt hω hdω_symm hcontdiff
  have h0 := Path.Homotopy.curveIntegral_evalAt_zero_eq_zero (ω := ω) φ
  have h1 := Path.Homotopy.curveIntegral_evalAt_one_eq_zero (ω := ω) φ
  calc
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x := by
      rw [h1, add_zero]
    _ = ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := h
    _ = ∫ᶜ x in γ₁, ω x := by
      rw [h0, add_zero]

/-- If a loop is nullhomotopic through a square on which a closed `1`-form is
defined, then its curve integral vanishes. -/
theorem Path.Homotopy.curveIntegral_eq_zero_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    {γ : Path x₀ x₀}
    (φ : γ.Homotopy (Path.refl x₀))
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.toHomotopy.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ, ω x = 0 := by
  have h :=
    Path.Homotopy.curveIntegral_eq_of_diffContOnCl
      (γ₀ := γ) (γ₁ := Path.refl x₀) (t := t) (ω := ω)
      φ hφt hω hdω_symm hcontdiff
  simpa using h


end PathHomotopy

section CircleHomotopyOnUnitAddCircle

/-- The standard interval parametrization of `UnitAddCircle`. -/
def unitIntervalToUnitAddCircle : C(I, UnitAddCircle) :=
  ⟨fun t ↦ (((t : ℝ) : UnitAddCircle)),
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val⟩

@[simp] lemma unitIntervalToUnitAddCircle_zero :
    unitIntervalToUnitAddCircle 0 = (0 : UnitAddCircle) := rfl

lemma unitIntervalToUnitAddCircle_one :
    unitIntervalToUnitAddCircle 1 = (0 : UnitAddCircle) := by
  change (((1 : ℝ) : UnitAddCircle) = (0 : UnitAddCircle))
  norm_num

/-- A continuous map on `UnitAddCircle` gives a loop by restricting to the
standard interval parametrization. -/
def unitAddCirclePath {E : Type*} [TopologicalSpace E] (boundary : C(UnitAddCircle, E)) :
    Path (boundary 0) (boundary 0) where
  toFun t := boundary (unitIntervalToUnitAddCircle t)
  continuous_toFun := boundary.continuous.comp unitIntervalToUnitAddCircle.continuous
  source' := by simp [unitIntervalToUnitAddCircle]
  target' := by rw [unitIntervalToUnitAddCircle_one]

/-- Reinterpret a homotopy on `UnitAddCircle` as a square homotopy on the
interval using the standard quotient parametrization. -/
def circleHomotopyToUnitAddCirclePath
    {E : Type*} [TopologicalSpace E]
    {center : E} {boundary : C(UnitAddCircle, E)}
    (H : (ContinuousMap.const UnitAddCircle center).Homotopy boundary) :
    ((Path.refl center : Path center center) : C(I, E)).Homotopy
      (unitAddCirclePath boundary) where
  toFun p := H (p.1, unitIntervalToUnitAddCircle p.2)
  continuous_toFun :=
    H.continuous.comp ((continuous_fst).prodMk
      (unitIntervalToUnitAddCircle.continuous.comp continuous_snd))
  map_zero_left u := by
    change H (0, unitIntervalToUnitAddCircle u) = center
    exact H.map_zero_left (unitIntervalToUnitAddCircle u)
  map_one_left u := by
    change H (1, unitIntervalToUnitAddCircle u) = boundary (unitIntervalToUnitAddCircle u)
    exact H.map_one_left (unitIntervalToUnitAddCircle u)

lemma circleHomotopyToUnitAddCirclePath_evalAt_one_eq_evalAt_zero
    {E : Type*} [TopologicalSpace E]
    {center : E} {boundary : C(UnitAddCircle, E)}
    (H : (ContinuousMap.const UnitAddCircle center).Homotopy boundary) :
    (circleHomotopyToUnitAddCirclePath H).evalAt (1 : I) =
      ((circleHomotopyToUnitAddCirclePath H).evalAt (0 : I)).cast rfl
        (by
          change unitAddCirclePath boundary 1 = unitAddCirclePath boundary 0
          change boundary (unitIntervalToUnitAddCircle 1) = boundary (unitIntervalToUnitAddCircle 0)
          rw [unitIntervalToUnitAddCircle_one, unitIntervalToUnitAddCircle_zero]) := by
  apply Path.ext
  funext t
  change H (t, unitIntervalToUnitAddCircle 1) = H (t, unitIntervalToUnitAddCircle 0)
  rw [unitIntervalToUnitAddCircle_one, unitIntervalToUnitAddCircle_zero]

/-- A closed `1`-form has zero integral along the interval loop induced by a
nullhomotopy on `UnitAddCircle`, provided the induced square homotopy satisfies
the required `C²` hypothesis. -/
theorem curveIntegral_eq_zero_of_unitAddCircleHomotopy_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {center : E} {boundary : C(UnitAddCircle, E)}
    (H : (ContinuousMap.const UnitAddCircle center).Homotopy boundary)
    (hHt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      H (a, unitIntervalToUnitAddCircle b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one ((circleHomotopyToUnitAddCirclePath H).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath boundary, ω x = 0 := by
  have h := (circleHomotopyToUnitAddCirclePath H).curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    (t := t) (ω := ω) hHt hω hdω_symm hcontdiff
  have hside := circleHomotopyToUnitAddCirclePath_evalAt_one_eq_evalAt_zero H
  have h' : ∫ᶜ x in Path.refl center, ω x +
      ∫ᶜ x in (circleHomotopyToUnitAddCirclePath H).evalAt (0 : I), ω x =
      ∫ᶜ x in unitAddCirclePath boundary, ω x +
        ∫ᶜ x in (circleHomotopyToUnitAddCirclePath H).evalAt (0 : I), ω x := by
    simpa [hside] using h
  have h'' := add_right_cancel h'
  simpa using h''.symm

/-- Bundle a circle nullhomotopy presented as a continuous map on
`I × UnitAddCircle`. -/
def circleNullhomotopy
    {E : Type*} [TopologicalSpace E]
    {center : E} {boundary : C(UnitAddCircle, E)}
    (hom : C(I × UnitAddCircle, E))
    (h0 : ∀ u : UnitAddCircle, hom (0, u) = center)
    (h1 : ∀ u : UnitAddCircle, hom (1, u) = boundary u) :
    (ContinuousMap.const UnitAddCircle center).Homotopy boundary where
  toContinuousMap := hom
  map_zero_left := h0
  map_one_left := h1

/-- The same vanishing statement with the nullhomotopy given explicitly as a
continuous map on `I × UnitAddCircle`. -/
theorem curveIntegral_eq_zero_of_circleNullhomotopy_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {center : E} {boundary : C(UnitAddCircle, E)}
    (hom : C(I × UnitAddCircle, E))
    (h0 : ∀ u : UnitAddCircle, hom (0, u) = center)
    (h1 : ∀ u : UnitAddCircle, hom (1, u) = boundary u)
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      hom (a, unitIntervalToUnitAddCircle b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath (circleNullhomotopy hom h0 h1)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath boundary, ω x = 0 := by
  exact curveIntegral_eq_zero_of_unitAddCircleHomotopy_of_diffContOnCl
    (H := circleNullhomotopy hom h0 h1) ht hω hdω_symm hcontdiff

/-- The closed unit disk boundary as a bundled continuous map. -/
def closedUnitDiskBoundaryContinuousMap : C(UnitAddCircle, ClosedUnitDisk) :=
  ⟨closedUnitDiskBoundary, continuous_closedUnitDiskBoundary⟩

/-- Radial contraction of the standard circle into the closed unit disk. -/
def radialClosedUnitDiskPoint (r : I) (u : UnitAddCircle) : ClosedUnitDisk := by
  refine ⟨((r : ℝ) : ℂ) * (unitAddCircleEquivComplexUnitCircle u : ℂ), ?_⟩
  show dist (((r : ℝ) : ℂ) * (unitAddCircleEquivComplexUnitCircle u : ℂ)) 0 ≤ 1
  rw [dist_eq_norm, sub_zero, norm_mul]
  have hu : ‖(unitAddCircleEquivComplexUnitCircle u : ℂ)‖ = 1 := by
    simpa using (unitAddCircleEquivComplexUnitCircle u).property
  rw [hu, mul_one]
  have hr : 0 ≤ (r : ℝ) := r.2.1
  simpa [RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg hr] using r.2.2

@[simp] lemma radialClosedUnitDiskPoint_zero (u : UnitAddCircle) :
    radialClosedUnitDiskPoint 0 u = 0 := by
  ext
  simp [radialClosedUnitDiskPoint]

@[simp] lemma radialClosedUnitDiskPoint_one (u : UnitAddCircle) :
    radialClosedUnitDiskPoint 1 u = closedUnitDiskBoundary u := by
  ext
  simp [radialClosedUnitDiskPoint, closedUnitDiskBoundary_coe]

/-- The standard disk nullhomotopy of the boundary circle. -/
def radialClosedUnitDiskMap : C(I × UnitAddCircle, ClosedUnitDisk) where
  toFun p := radialClosedUnitDiskPoint p.1 p.2
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ ?_
    have hr : Continuous fun p : I × UnitAddCircle => ((p.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have hu : Continuous fun p : I × UnitAddCircle =>
        (unitAddCircleEquivComplexUnitCircle p.2 : ℂ) :=
      continuous_subtype_val.comp
        (unitAddCircleEquivComplexUnitCircle.continuous.comp continuous_snd)
    simpa using hr.mul hu

@[simp] lemma radialClosedUnitDiskMap_zero (u : UnitAddCircle) :
    radialClosedUnitDiskMap (0, u) = 0 :=
  radialClosedUnitDiskPoint_zero u

@[simp] lemma radialClosedUnitDiskMap_one (u : UnitAddCircle) :
    radialClosedUnitDiskMap (1, u) = closedUnitDiskBoundary u :=
  radialClosedUnitDiskPoint_one u

/-- Restrict a continuous disk map to the standard boundary circle. -/
def ContinuousMap.compClosedUnitDiskBoundary
    {E : Type*} [TopologicalSpace E] (F : C(ClosedUnitDisk, E)) :
    C(UnitAddCircle, E) :=
  F.comp closedUnitDiskBoundaryContinuousMap

/-- Every continuous disk map canonically gives a nullhomotopy of its boundary loop. -/
def ContinuousMap.closedUnitDiskBoundaryNullhomotopy
    {E : Type*} [TopologicalSpace E] (F : C(ClosedUnitDisk, E)) :
    (ContinuousMap.const UnitAddCircle (F 0)).Homotopy (ContinuousMap.compClosedUnitDiskBoundary F) :=
  circleNullhomotopy (F.comp radialClosedUnitDiskMap)
    (by intro u; simp)
    (by
      intro u
      change F (radialClosedUnitDiskMap (1, u)) = F (closedUnitDiskBoundary u)
      rw [radialClosedUnitDiskMap_one])

/-- A closed `1`-form has zero integral along the boundary loop of a continuous
map from the closed unit disk, provided the induced square homotopy satisfies
the required `C²` hypothesis. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskMap_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    (F : C(ClosedUnitDisk, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (ContinuousMap.compClosedUnitDiskBoundary F), ω x = 0 := by
  exact curveIntegral_eq_zero_of_unitAddCircleHomotopy_of_diffContOnCl
    (H := ContinuousMap.closedUnitDiskBoundaryNullhomotopy F) ht hω hdω_symm hcontdiff

/-- The same boundary-vanishing statement when the boundary circle map is given
separately together with a continuous closed-disk extension. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskBoundaryExtension_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : C(UnitAddCircle, E)}
    (F : C(ClosedUnitDisk, E))
    (hboundary : boundary = ContinuousMap.compClosedUnitDiskBoundary F)
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath boundary, ω x = 0 := by
  subst hboundary
  exact curveIntegral_eq_zero_of_closedUnitDiskMap_of_diffContOnCl
    (F := F) ht hω hdω_symm hcontdiff

/-- Unbundled boundary-function form of the closed-disk extension vanishing
statement. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskBoundaryExtension_unbundled_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → E}
    (hboundaryCont : Continuous boundary)
    (F : C(ClosedUnitDisk, E))
    (hboundary : boundary = F ∘ closedUnitDiskBoundary)
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath ⟨boundary, hboundaryCont⟩, ω x = 0 := by
  let boundaryMap : C(UnitAddCircle, E) := ⟨boundary, hboundaryCont⟩
  have hboundaryMap : boundaryMap = ContinuousMap.compClosedUnitDiskBoundary F := by
    ext u
    exact congrFun hboundary u
  simpa [boundaryMap] using
    (curveIntegral_eq_zero_of_closedUnitDiskBoundaryExtension_of_diffContOnCl
      (boundary := boundaryMap) (F := F) hboundaryMap ht hω hdω_symm hcontdiff)

/-- The same vanishing statement transports across a boundary-respecting
homeomorphism from the closed unit disk. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskHomeomorphMap_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    (e : ClosedUnitDisk ≃ₜ Y)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (ContinuousMap.compClosedUnitDiskBoundary (F.comp ⟨e, e.continuous_toFun⟩)), ω x = 0 := by
  exact curveIntegral_eq_zero_of_closedUnitDiskMap_of_diffContOnCl
    (F := F.comp ⟨e, e.continuous_toFun⟩) ht hω hdω_symm hcontdiff

/-- Boundary-map form of the closed-disk-homeomorphism vanishing statement. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskHomeomorphBoundaryExtension_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : C(UnitAddCircle, Y)}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = (⟨e, e.continuous_toFun⟩ : C(ClosedUnitDisk, Y)).comp
      closedUnitDiskBoundaryContinuousMap)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (F.comp boundary), ω x = 0 := by
  subst hboundary
  simpa [ContinuousMap.comp_assoc, ContinuousMap.compClosedUnitDiskBoundary] using
    (curveIntegral_eq_zero_of_closedUnitDiskHomeomorphMap_of_diffContOnCl
      (e := e) (F := F) (ht := ht) hω hdω_symm hcontdiff)

/-- Unbundled boundary-function form of the closed-disk-homeomorphism
vanishing statement. -/
theorem curveIntegral_eq_zero_of_closedUnitDiskHomeomorphBoundaryExtension_unbundled_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (hboundaryCont : Continuous boundary)
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitDiskBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (F.comp ⟨boundary, hboundaryCont⟩), ω x = 0 := by
  let boundaryMap : C(UnitAddCircle, Y) := ⟨boundary, hboundaryCont⟩
  have hboundaryMap : boundaryMap = (⟨e, e.continuous_toFun⟩ : C(ClosedUnitDisk, Y)).comp
      closedUnitDiskBoundaryContinuousMap := by
    ext u
    exact congrFun hboundary u
  simpa [boundaryMap, ContinuousMap.comp_assoc] using
    (curveIntegral_eq_zero_of_closedUnitDiskHomeomorphBoundaryExtension_of_diffContOnCl
      (boundary := boundaryMap) (e := e) hboundaryMap (F := F) (ht := ht)
      hω hdω_symm hcontdiff)

/-- The closed unit square boundary as a bundled continuous map. -/
def closedUnitSquareBoundaryContinuousMap : C(UnitAddCircle, ClosedUnitSquare) :=
  ⟨closedUnitSquareBoundary, continuous_closedUnitSquareBoundary⟩

/-- The standard radial nullhomotopy of the closed unit square boundary. -/
def radialClosedUnitSquareMap : C(I × UnitAddCircle, ClosedUnitSquare) :=
  ⟨closedUnitSquareRadial, continuous_closedUnitSquareRadial⟩

@[simp] lemma radialClosedUnitSquareMap_zero (u : UnitAddCircle) :
    radialClosedUnitSquareMap (0, u) = closedUnitSquareCenter :=
  closedUnitSquareRadial_start u

@[simp] lemma radialClosedUnitSquareMap_one (u : UnitAddCircle) :
    radialClosedUnitSquareMap (1, u) = closedUnitSquareBoundary u :=
  closedUnitSquareRadial_finish u

/-- Restrict a continuous closed-square map to the standard boundary circle. -/
def ContinuousMap.compClosedUnitSquareBoundary
    {E : Type*} [TopologicalSpace E] (F : C(ClosedUnitSquare, E)) :
    C(UnitAddCircle, E) :=
  F.comp closedUnitSquareBoundaryContinuousMap

/-- Every continuous closed-square map canonically gives a nullhomotopy of its
boundary loop. -/
def ContinuousMap.closedUnitSquareBoundaryNullhomotopy
    {E : Type*} [TopologicalSpace E] (F : C(ClosedUnitSquare, E)) :
    (ContinuousMap.const UnitAddCircle (F closedUnitSquareCenter)).Homotopy
      (ContinuousMap.compClosedUnitSquareBoundary F) :=
  circleNullhomotopy (F.comp radialClosedUnitSquareMap)
    (by intro u; simp)
    (by
      intro u
      change F (radialClosedUnitSquareMap (1, u)) = F (closedUnitSquareBoundary u)
      rw [radialClosedUnitSquareMap_one])

/-- A closed `1`-form has zero integral along the boundary loop of a continuous
map from the closed unit square, provided the induced square homotopy satisfies
the required `C²` hypothesis. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareMap_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    (F : C(ClosedUnitSquare, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (ContinuousMap.compClosedUnitSquareBoundary F), ω x = 0 := by
  exact curveIntegral_eq_zero_of_unitAddCircleHomotopy_of_diffContOnCl
    (H := ContinuousMap.closedUnitSquareBoundaryNullhomotopy F) ht hω hdω_symm hcontdiff

/-- The same boundary-vanishing statement when the boundary circle map is given
separately together with a continuous closed-square extension. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareBoundaryExtension_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : C(UnitAddCircle, E)}
    (F : C(ClosedUnitSquare, E))
    (hboundary : boundary = ContinuousMap.compClosedUnitSquareBoundary F)
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath boundary, ω x = 0 := by
  subst hboundary
  exact curveIntegral_eq_zero_of_closedUnitSquareMap_of_diffContOnCl
    (F := F) ht hω hdω_symm hcontdiff

/-- Unbundled boundary-function form of the closed-square extension vanishing
statement. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareBoundaryExtension_unbundled_of_diffContOnCl
    {𝕜 E G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → E}
    (hboundaryCont : Continuous boundary)
    (F : C(ClosedUnitSquare, E))
    (hboundary : boundary = F ∘ closedUnitSquareBoundary)
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b)) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy F)).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath ⟨boundary, hboundaryCont⟩, ω x = 0 := by
  let boundaryMap : C(UnitAddCircle, E) := ⟨boundary, hboundaryCont⟩
  have hboundaryMap : boundaryMap = ContinuousMap.compClosedUnitSquareBoundary F := by
    ext u
    exact congrFun hboundary u
  simpa [boundaryMap] using
    (curveIntegral_eq_zero_of_closedUnitSquareBoundaryExtension_of_diffContOnCl
      (boundary := boundaryMap) (F := F) hboundaryMap ht hω hdω_symm hcontdiff)

/-- The same vanishing statement transports across a boundary-respecting
homeomorphism from the closed unit square. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareHomeomorphMap_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    (e : ClosedUnitSquare ≃ₜ Y)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (ContinuousMap.compClosedUnitSquareBoundary (F.comp ⟨e, e.continuous_toFun⟩)), ω x = 0 := by
  exact curveIntegral_eq_zero_of_closedUnitSquareMap_of_diffContOnCl
    (F := F.comp ⟨e, e.continuous_toFun⟩) ht hω hdω_symm hcontdiff

/-- Boundary-map form of the closed-square-homeomorphism vanishing statement. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareHomeomorphBoundaryExtension_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : C(UnitAddCircle, Y)}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundary : boundary = (⟨e, e.continuous_toFun⟩ : C(ClosedUnitSquare, Y)).comp
      closedUnitSquareBoundaryContinuousMap)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (F.comp boundary), ω x = 0 := by
  subst hboundary
  simpa [ContinuousMap.comp_assoc, ContinuousMap.compClosedUnitSquareBoundary] using
    (curveIntegral_eq_zero_of_closedUnitSquareHomeomorphMap_of_diffContOnCl
      (e := e) (F := F) (ht := ht) hω hdω_symm hcontdiff)

/-- Unbundled boundary-function form of the closed-square-homeomorphism
vanishing statement. -/
theorem curveIntegral_eq_zero_of_closedUnitSquareHomeomorphBoundaryExtension_unbundled_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (hboundaryCont : Continuous boundary)
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundary : boundary = e ∘ closedUnitSquareBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (e (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy
              (F.comp ⟨e, e.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (F.comp ⟨boundary, hboundaryCont⟩), ω x = 0 := by
  let boundaryMap : C(UnitAddCircle, Y) := ⟨boundary, hboundaryCont⟩
  have hboundaryMap : boundaryMap = (⟨e, e.continuous_toFun⟩ : C(ClosedUnitSquare, Y)).comp
      closedUnitSquareBoundaryContinuousMap := by
    ext u
    exact congrFun hboundary u
  simpa [boundaryMap, ContinuousMap.comp_assoc] using
    (curveIntegral_eq_zero_of_closedUnitSquareHomeomorphBoundaryExtension_of_diffContOnCl
      (boundary := boundaryMap) (e := e) hboundaryMap (F := F) (ht := ht)
      hω hdω_symm hcontdiff)

/-- The bundled square-homeomorphism-plus-glued-strip interface already
implies the boundary vanishing statement needed on the oriented side.  Only the
homeomorphism and boundary identification are used here; the polygonal-model
data is carried to match the orientation-free geometric interface. -/
theorem curveIntegral_eq_zero_of_closedUnitSquare_homeomorphCylinderStripGluedArbitrarilyFineData_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [PseudoMetricSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (hboundaryCont : Continuous boundary)
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1,
      F (D.homeomorph (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy
              (F.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))).extend xy.1) xy.2)
      (Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath (F.comp ⟨boundary, hboundaryCont⟩), ω x = 0 := by
  exact curveIntegral_eq_zero_of_closedUnitSquareHomeomorphBoundaryExtension_unbundled_of_diffContOnCl
    hboundaryCont D.homeomorph D.boundaryHomeomorph F ht hω hdω_symm hcontdiff

end CircleHomotopyOnUnitAddCircle

section FreePathHomotopy

namespace ContinuousMap.Homotopy

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
  {a c x : E} {γ₀ : Path a a} {γ₁ : Path c c}

/-- If the two vertical side paths of a square homotopy between free loops
agree, then a closed `1`-form has the same integral along the two loops. This
is the free-loop variant needed for contractions through a disk. -/
theorem curveIntegral_eq_of_evalAt_eq_of_hasFDerivWithinAt
    {t : Set E}
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₀ : C(I, E)).Homotopy γ₁)
    (hside : φ.evalAt (1 : I) = (φ.evalAt (0 : I)).cast
      (γ₀.target.trans γ₀.source.symm) (γ₁.target.trans γ₁.source.symm))
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := t) (ω := ω) (dω := dω) hφt hω hωc hdω_symm hcontdiff
  have h' : ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x =
      ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := by
    simpa [hside] using h
  exact add_right_cancel h'

/-- If the two vertical side paths of a square homotopy between free loops
agree, then a closed `1`-form has the same integral along the two loops. This
is the `DiffContOnCl` version convenient for Euclidean chart calculations. -/
theorem curveIntegral_eq_of_evalAt_eq_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    (φ : (γ₀ : C(I, E)).Homotopy γ₁)
    (hside : φ.evalAt (1 : I) = (φ.evalAt (0 : I)).cast
      (γ₀.target.trans γ₀.source.symm) (γ₁.target.trans γ₁.source.symm))
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₀, ω x = ∫ᶜ x in γ₁, ω x := by
  have h := φ.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    (t := t) (ω := ω) hφt hω hdω_symm hcontdiff
  have h' : ∫ᶜ x in γ₀, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x =
      ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x := by
    simpa [hside] using h
  exact add_right_cancel h'

/-- In particular, a free loop has zero integral whenever it contracts through a
square homotopy whose two side paths agree. This matches the standard radial
contraction pattern coming from a disk filling. -/
theorem curveIntegral_eq_zero_of_evalAt_eq_of_diffContOnCl
    {t : Set E}
    {ω : E → E →L[𝕜] F}
    {γ : Path a a}
    (φ : (γ : C(I, E)).Homotopy (Path.refl x))
    (hside : φ.evalAt (1 : I) = (φ.evalAt (0 : I)).cast
      (γ.target.trans γ.source.symm) ((Path.refl x).target.trans (Path.refl x).source.symm))
    (hφt : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ, ω x = 0 := by
  have h := ContinuousMap.Homotopy.curveIntegral_eq_of_evalAt_eq_of_diffContOnCl
    (γ₀ := γ) (γ₁ := Path.refl x) (t := t) (ω := ω)
    φ hside hφt hω hdω_symm hcontdiff
  simpa using h

end ContinuousMap.Homotopy


section SquareStokes

namespace ContinuousMap.Homotopy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b c d : E} {γ₁ : Path a b} {γ₂ : Path c d}

/-- A `C¹` `1`-form satisfies the square Stokes formula along a `C²` homotopy:
the boundary curve integral equals the integral of the antisymmetrized
derivative over the unit square.  This is the non-closed precursor to the
homotopy-invariance statements formalized above. -/
theorem curveIntegral_add_curveIntegral_sub_eq_setIntegral_fderiv_skew_of_contDiff
    {ω : E → E →L[ℝ] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hω : ContDiff ℝ 1 ω)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (Icc 0 1)) :
    let ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦
      Set.IccExtend zero_le_one (φ.extend xy.1) xy.2
    let dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E :=
      fderivWithin ℝ ψ (Icc 0 1)
    (∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x) -
        (∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x) =
      ∫ x in (Icc (0 : ℝ × ℝ) 1),
        fderiv ℝ ω (ψ x) (dψ x (1, 0)) (dψ x (0, 1)) -
          fderiv ℝ ω (ψ x) (dψ x (0, 1)) (dψ x (1, 0)) := by
  dsimp
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hinterior : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq]
    simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hunique : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hU_subset : U ⊆ Icc 0 1 := hinterior ▸ interior_subset
  have hclosure : closure U = Icc 0 1 := by
    simp [hU, closure_prod_eq, Prod.mk_zero_zero, Prod.mk_one_one]
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦
    Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψ_cont : Continuous ψ := by
    fun_prop
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  have hdψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := by
    rintro a haU
    refine hcontdiff.differentiableOn (by decide) a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E :=
    fderivWithin ℝ dψ (Icc 0 1)
  have hd2ψ : ∀ a ∈ U, HasFDerivAt dψ (d2ψ a) a := by
    rintro a haU
    refine hcontdiff.fderivWithin hunique (by decide) |>.differentiableOn_one a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha
    exact (hcontdiff a ha).isSymmSndFDerivWithinAt (by simp) hunique
      (by simp [hinterior, hclosure, ha]) ha
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  have hf : ∀ a ∈ Icc 0 1,
      f a = ω (ψ a) (derivWithin (ψ ∘ (a.1, ·)) I a.2) := by
    intro a ha
    simp only [f, η, dψ, ContinuousLinearMap.comp_apply]
    congr 1
    have : HasDerivWithinAt (a.1, ·) (0, 1) I a.2 :=
      .prodMk (hasDerivWithinAt_const ..) (hasDerivWithinAt_id ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ha.1.1, ht.1⟩, ⟨ha.2.1, ht.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.2, ha.2.2⟩
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  have hg : ∀ a ∈ Icc 0 1,
      g a = ω (ψ a) (-derivWithin (ψ ∘ (·, a.2)) I a.1) := by
    intro a ha
    simp only [g, η, dψ, ContinuousLinearMap.comp_apply, map_neg]
    congr 2
    have : HasDerivWithinAt (·, a.2) (1, 0) I a.1 :=
      .prodMk (hasDerivWithinAt_id ..) (hasDerivWithinAt_const ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ht.1, ha.1.2⟩, ⟨ht.2, ha.2.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.1, ha.2.1⟩
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a +
      (fderiv ℝ ω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hdη : ∀ a ∈ U, HasFDerivAt η (dη a) a := by
    rintro a haU
    refine HasFDerivWithinAt.comp_hasFDerivAt (t := (Set.univ : Set E)) a ?_ ?_ ?_ |>.clm_comp
      (hd2ψ a haU)
    · exact ((hω.contDiffAt (x := ψ a)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    · exact hdψ a haU
    · exact Filter.Eventually.of_forall fun x ↦ by simp
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦
    ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  have hf' : ∀ a ∈ U, HasFDerivAt f (f' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hdη a ha)
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦
    -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hg' : ∀ a ∈ U, HasFDerivAt g (g' a) a := by
    intro a ha
    exact ((ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hdη a ha)).neg
  have hdiv_formula :
      ∀ a ∈ Icc (0 : ℝ × ℝ) 1,
        f' a (1, 0) + g' a (0, 1) =
          fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
            fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) := by
    intro a ha
    change
      (ω (ψ a)) (((d2ψ a) (1, 0)) (0, 1)) +
          ((fderiv ℝ ω (ψ a)) ((dψ a) (1, 0))) ((dψ a) (0, 1)) +
        -((ω (ψ a)) (((d2ψ a) (0, 1)) (1, 0)) +
          ((fderiv ℝ ω (ψ a)) ((dψ a) (0, 1))) ((dψ a) (1, 0))) =
      ((fderiv ℝ ω (ψ a)) ((dψ a) (1, 0))) ((dψ a) (0, 1)) -
        ((fderiv ℝ ω (ψ a)) ((dψ a) (0, 1))) ((dψ a) (1, 0))
    rw [hd2ψ_symm a ha (1, 0) (0, 1)]
    abel
  have hdψ_cont : ContinuousOn dψ (Icc (0 : ℝ × ℝ) 1) := by
    exact hcontdiff.continuousOn_fderivWithin hunique (by decide)
  have hterm1_cont : ContinuousOn
      (fun a : ℝ × ℝ ↦
        fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)))
      (Icc (0 : ℝ × ℝ) 1) := by
    have hωf : Continuous (fderiv ℝ ω) := hω.continuous_fderiv (by simp)
    have hA : ContinuousOn (fun a : ℝ × ℝ ↦ fderiv ℝ ω (ψ a))
        (Icc (0 : ℝ × ℝ) 1) :=
      (hωf.comp hψ_cont).continuousOn
    have hB : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (1, 0))
        (Icc (0 : ℝ × ℝ) 1) :=
      hdψ_cont.clm_apply continuousOn_const
    have hC : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (0, 1))
        (Icc (0 : ℝ × ℝ) 1) :=
      hdψ_cont.clm_apply continuousOn_const
    exact (hA.clm_apply hB).clm_apply hC
  have hterm2_cont : ContinuousOn
      (fun a : ℝ × ℝ ↦
        fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)))
      (Icc (0 : ℝ × ℝ) 1) := by
    have hωf : Continuous (fderiv ℝ ω) := hω.continuous_fderiv (by simp)
    have hA : ContinuousOn (fun a : ℝ × ℝ ↦ fderiv ℝ ω (ψ a))
        (Icc (0 : ℝ × ℝ) 1) :=
      (hωf.comp hψ_cont).continuousOn
    have hB : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (0, 1))
        (Icc (0 : ℝ × ℝ) 1) :=
      hdψ_cont.clm_apply continuousOn_const
    have hC : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (1, 0))
        (Icc (0 : ℝ × ℝ) 1) :=
      hdψ_cont.clm_apply continuousOn_const
    exact (hA.clm_apply hB).clm_apply hC
  have hint : MeasureTheory.IntegrableOn
      (fun a : ℝ × ℝ ↦
        fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
          fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)))
      (Icc (0 : ℝ × ℝ) 1) := by
    exact (hterm1_cont.sub hterm2_cont).integrableOn_compact isCompact_Icc
  have hdiv_ae :
      (fun a : ℝ × ℝ ↦
        fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
          fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0))) =ᵐ[MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)]
      (fun a : ℝ × ℝ ↦ f' a (1, 0) + g' a (0, 1)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ × ℝ) 1))] with a ha
    symm
    exact hdiv_formula a ha
  have hdiv_eq :
      ∫ a in Icc (0 : ℝ × ℝ) 1,
        fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
          fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) =
        ∫ a in Icc (0 : ℝ × ℝ) 1, f' a (1, 0) + g' a (0, 1) := by
    exact MeasureTheory.integral_congr_ae hdiv_ae
  have hA0 : ContinuousOn (fun a : ℝ × ℝ ↦ ω (ψ a)) (Icc (0 : ℝ × ℝ) 1) :=
    (hω.continuous.comp hψ_cont).continuousOn
  have hB0 : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (0, 1)) (Icc (0 : ℝ × ℝ) 1) :=
    hdψ_cont.clm_apply continuousOn_const
  have hB1 : ContinuousOn (fun a : ℝ × ℝ ↦ dψ a (1, 0)) (Icc (0 : ℝ × ℝ) 1) :=
    hdψ_cont.clm_apply continuousOn_const
  have hf_cont : ContinuousOn f (Icc (0 : ℝ × ℝ) 1) := by
    simpa [f, η] using hA0.clm_apply hB0
  have hg_cont : ContinuousOn g (Icc (0 : ℝ × ℝ) 1) := by
    simpa [g, η] using (hA0.clm_apply hB1).neg
  have hmain :
      ∫ a in Icc (0 : ℝ × ℝ) 1,
          fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
            fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) =
        (((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
            ∫ y in (0 : ℝ)..1, f (1, y)) -
          ∫ y in (0 : ℝ)..1, f (0, y) := by
    calc
      ∫ a in Icc (0 : ℝ × ℝ) 1,
          fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
            fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) =
        ∫ a in Icc (0 : ℝ × ℝ) 1, f' a (1, 0) + g' a (0, 1) := hdiv_eq
      _ = (((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
            ∫ y in (0 : ℝ)..1, f (1, y)) -
          ∫ y in (0 : ℝ)..1, f (0, y) := by
        exact MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
          f g f' g' (0, 0) (1, 1) (by simp [Prod.le_def])
          hf_cont hg_cont
          (fun a ha ↦ hf' a ha)
          (fun a ha ↦ hg' a ha)
          (hint.congr_fun_ae hdiv_ae)
  have h_extend_curry (s : I) : φ.extend s = φ.curry s := by
    ext u
    rw [ContinuousMap.Homotopy.extend_apply_coe]
    rfl
  have hψ_curry_eqOn (s : I) :
      EqOn (fun t : ℝ ↦ ψ (s, t)) (⟨φ.curry s, rfl, rfl⟩ : Path _ _).extend I := by
    intro t ht
    change Set.IccExtend zero_le_one (φ.extend s) t =
      Set.IccExtend zero_le_one (φ.curry s) t
    simpa using congrArg (fun f : C(I, E) ↦ Set.IccExtend zero_le_one f t) (h_extend_curry s)
  have hψ_eval_eqOn (t : I) : EqOn (fun s : ℝ ↦ ψ (s, t)) (φ.evalAt t).extend I := by
    intro s hs
    rw [Path.extend_apply _ hs]
    change ψ (s, t) = φ (⟨s, hs⟩, t)
    simpa [ψ, hψ, ContinuousMap.Homotopy.evalAt_apply] using
      ContinuousMap.Homotopy.extend_apply_coe φ ⟨s, hs⟩ t
  have hfi (s : I) :
      ∫ t in (0 : ℝ)..1, f (s, t) = ∫ᶜ x in ⟨φ.curry s, rfl, rfl⟩, ω x := by
    simp only [curveIntegral_def, curveIntegralFun_def]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hEq := hψ_curry_eqOn s ht
    simp [hf (s, t), hEq, derivWithin_congr (hψ_curry_eqOn s) hEq,
      Prod.le_def, s.2.1, s.2.2, ht.1, ht.2, Function.comp_def]
  have hf₀ : ∫ t in (0 : ℝ)..1, f (0, t) = ∫ᶜ x in γ₁, ω x := by
    simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 0
  have hf₁ : ∫ t in (0 : ℝ)..1, f (1, t) = ∫ᶜ x in γ₂, ω x := by
    simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 1
  have hgi (t : I) : ∫ᶜ x in φ.evalAt t, ω x = -∫ s in (0 : ℝ)..1, g (s, t) := by
    simp only [curveIntegral_def, curveIntegralFun_def, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro s hs
    have hEq := hψ_eval_eqOn t hs
    simp [hg (s, t), hEq, derivWithin_congr (hψ_eval_eqOn t) hEq,
      Prod.le_def, hs.1, hs.2, t.2.1, t.2.2, Function.comp_def]
  have hmain' :
      ∫ a in Icc (0 : ℝ × ℝ) 1,
          fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
            fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) =
        ((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
          ∫ᶜ x in γ₂, ω x - ∫ᶜ x in γ₁, ω x := by
    calc
      ∫ a in Icc (0 : ℝ × ℝ) 1,
          fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
            fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) =
        (((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
            ∫ y in (0 : ℝ)..1, f (1, y)) -
          ∫ y in (0 : ℝ)..1, f (0, y) := hmain
      _ = ((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
          ∫ᶜ x in γ₂, ω x - ∫ᶜ x in γ₁, ω x := by
        rw [hf₀, hf₁]
  calc
    (∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt (0 : I), ω x) -
        (∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt (1 : I), ω x) =
      ((∫ x in (0 : ℝ)..1, g (x, 1)) - ∫ x in (0 : ℝ)..1, g (x, 0)) +
        ∫ᶜ x in γ₂, ω x - ∫ᶜ x in γ₁, ω x := by
      rw [hgi (0 : I), hgi (1 : I)]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ∫ a in Icc (0 : ℝ × ℝ) 1,
        fderiv ℝ ω (ψ a) (dψ a (1, 0)) (dψ a (0, 1)) -
          fderiv ℝ ω (ψ a) (dψ a (0, 1)) (dψ a (1, 0)) := by
      exact hmain'.symm

end ContinuousMap.Homotopy

end SquareStokes

end FreePathHomotopy

end

end GromovFilling
