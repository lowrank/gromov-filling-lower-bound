import GromovFilling.ClosedOneForm

/-!
# Geometric closed-form boundary endpoints

This file exposes the currently formalized oriented-side boundary-vanishing
and Stokes/norm statements at the closed-disk, closed-square-extension, and
square-homeomorphism interfaces used elsewhere in the development.
-/

open Set
open scoped unitInterval

namespace GromovFilling

noncomputable section

/-- Oriented boundary vanishing when the boundary admits a continuous extension
across the closed unit disk. The boundary continuity is inferred from the
extension map. -/
theorem curveIntegral_eq_zero_of_closedUnitDisk_extension_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk → Y) (he : Continuous e)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
      F (e (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy
              (F.comp ⟨e, he⟩))).extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [hboundaryMap]
        exact he.comp continuous_closedUnitDiskBoundary⟩), ω x = 0 := by
  have hboundaryCont : Continuous (F ∘ boundary) := by
    exact F.continuous.comp (by
      rw [hboundaryMap]
      exact he.comp continuous_closedUnitDiskBoundary)
  simpa using
    (curveIntegral_eq_zero_of_closedUnitDiskBoundaryExtension_unbundled_of_diffContOnCl
      (boundary := F ∘ boundary) (hboundaryCont := hboundaryCont) (F := F.comp ⟨e, he⟩)
      (by ext t; simp [hboundaryMap]) (ht := ht) hω hdω_symm hcontdiff)


/-- Direct closed-disk extension interface for the Stokes package. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_extension_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitDisk → Y) (he : Continuous e)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp (Fmap.comp ⟨e, he⟩)) :
    ClosedUnitDiskMapStokesProp (Fmap.comp ⟨e, he⟩) ω := by
  simpa using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDiskMap_of_contDiff
      (Fmap := Fmap.comp ⟨e, he⟩) hω hcontdiff)

/-- Direct closed-disk extension interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitDisk_extension_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitDisk → Y) (he : Continuous e)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp (Fmap.comp ⟨e, he⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitDiskMapSkewIntegrand (Fmap.comp ⟨e, he⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitDiskMapSkewIntegrand (Fmap.comp ⟨e, he⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitDiskBoundaryIntegral (Fmap.comp ⟨e, he⟩) ω‖ ≤ B * area := by
  exact norm_closedUnitDiskBoundaryIntegral_le_of_contDiff
    (Fmap := Fmap.comp ⟨e, he⟩) hω hcontdiff hB hintegrand hJ hbound harea

/-- Oriented boundary vanishing when the boundary is identified with the
closed-unit-disk boundary by a homeomorphism. The boundary continuity is
inferred automatically from the homeomorphism data. -/
theorem curveIntegral_eq_zero_of_closedUnitDisk_homeomorph_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
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
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [hboundaryMap]
        exact e.continuous_toFun.comp continuous_closedUnitDiskBoundary⟩), ω x = 0 := by
  have hboundaryCont : Continuous boundary := by
    rw [hboundaryMap]
    exact e.continuous_toFun.comp continuous_closedUnitDiskBoundary
  simpa using
    (curveIntegral_eq_zero_of_closedUnitDiskHomeomorphBoundaryExtension_unbundled_of_diffContOnCl
      (hboundaryCont := hboundaryCont) (e := e) (hboundary := hboundaryMap)
      (F := F) (ht := ht) hω hdω_symm hcontdiff)

/-- Direct closed-disk homeomorphism interface for the Stokes package. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_homeomorph_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitDisk ≃ₜ Y)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩)) :
    ClosedUnitDiskMapStokesProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩) ω := by
  simpa using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDiskMap_of_contDiff
      (Fmap := Fmap.comp ⟨e, e.continuous_toFun⟩) hω hcontdiff)

/-- Direct closed-disk homeomorphism interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitDisk_homeomorph_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitDisk ≃ₜ Y)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitDiskMapSkewIntegrand
        (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitDiskMapSkewIntegrand
          (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitDiskBoundaryIntegral (Fmap.comp ⟨e, e.continuous_toFun⟩) ω‖ ≤ B * area := by
  exact norm_closedUnitDiskBoundaryIntegral_le_of_contDiff
    (Fmap := Fmap.comp ⟨e, e.continuous_toFun⟩)
    hω hcontdiff hB hintegrand hJ hbound harea

/-- Oriented boundary vanishing at the bundled disk-homeomorphism plus
glued-strip interface. The boundary continuity is inferred automatically from
the bundled homeomorphism data. -/
theorem curveIntegral_eq_zero_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [PseudoMetricSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
      F (D.homeomorph (radialClosedUnitDiskPoint a (unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitDiskBoundaryNullhomotopy
              (F.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))).extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [D.boundaryHomeomorph]
        exact D.homeomorph.continuous_toFun.comp continuous_closedUnitDiskBoundary⟩), ω x = 0 := by
  simpa using
    (curveIntegral_eq_zero_of_closedUnitDisk_homeomorph_of_diffContOnCl
      (e := D.homeomorph) (hboundaryMap := D.boundaryHomeomorph)
      (F := F) (ht := ht) hω hdω_symm hcontdiff)

/-- Oriented boundary vanishing at the direct disk-homeomorphism plus
glued-strip interface furnished by the explicit disk strip data. -/
theorem curveIntegral_eq_zero_of_closedUnitDisk_homeomorph_cylinderStripGlued_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
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
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [hboundaryMap]
        exact e.continuous_toFun.comp continuous_closedUnitDiskBoundary⟩), ω x = 0 := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitDiskBoundary }
  simpa [D] using
    (curveIntegral_eq_zero_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_diffContOnCl
      (D := D) (F := F) (ht := ht) hω hdω_symm hcontdiff)

/-- The bundled disk-homeomorphism-plus-glued-strip interface also yields
its Stokes package, expressed through the closed-disk wrapper theorem. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩)) :
    ClosedUnitDiskMapStokesProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω := by
  simpa using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_homeomorph_of_contDiff
      (e := D.homeomorph) (Fmap := Fmap) hω hcontdiff)

/-- Direct disk-homeomorphism interface for the Stokes package. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_homeomorph_cylinderStripGlued_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩)) :
    ClosedUnitDiskMapStokesProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩) ω := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitDiskBoundary }
  simpa [D] using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
      (D := D) (Fmap := Fmap) hω hcontdiff)

/-- Bundled disk-homeomorphism interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitDiskMapSkewIntegrand
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitDiskMapSkewIntegrand
          (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitDiskBoundaryIntegral
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω‖ ≤ B * area := by
  simpa using
    (norm_curveIntegral_le_of_closedUnitDisk_homeomorph_of_contDiff
      (e := D.homeomorph) (Fmap := Fmap) hω hcontdiff hB hintegrand hJ hbound harea)

/-- Direct disk-homeomorphism interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitDisk_homeomorph_cylinderStripGlued_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitDisk ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitDiskMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitDiskMapSkewIntegrand
        (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitDiskMapSkewIntegrand
          (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitDiskBoundaryIntegral (Fmap.comp ⟨e, e.continuous_toFun⟩) ω‖ ≤ B * area := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitDiskBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitDiskBoundary }
  simpa [D] using
    (norm_curveIntegral_le_of_closedUnitDisk_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
      (D := D) (Fmap := Fmap) hω hcontdiff hB hintegrand hJ hbound harea)


/-- Oriented boundary vanishing when the boundary admits a continuous extension
across the closed unit square. The boundary continuity is inferred from the
extension map. -/
theorem curveIntegral_eq_zero_of_closedUnitSquare_extension_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [TopologicalSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare → Y) (he : Continuous e)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
      F (e (closedUnitSquareRadial (a, unitIntervalToUnitAddCircle b))) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦
        Set.IccExtend zero_le_one
          ((circleHomotopyToUnitAddCirclePath
            (ContinuousMap.closedUnitSquareBoundaryNullhomotopy
              (F.comp ⟨e, he⟩))).extend xy.1) xy.2)
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [hboundaryMap]
        exact he.comp continuous_closedUnitSquareBoundary⟩), ω x = 0 := by
  have hboundaryCont : Continuous (F ∘ boundary) := by
    exact F.continuous.comp (by
      rw [hboundaryMap]
      exact he.comp continuous_closedUnitSquareBoundary)
  simpa using
    (curveIntegral_eq_zero_of_closedUnitSquareBoundaryExtension_unbundled_of_diffContOnCl
      (boundary := F ∘ boundary) (hboundaryCont := hboundaryCont) (F := F.comp ⟨e, he⟩)
      (by ext t; simp [hboundaryMap]) (ht := ht) hω hdω_symm hcontdiff)

/-- Direct closed-square extension interface for the Stokes package. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquare_extension_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitSquare → Y) (he : Continuous e)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp (Fmap.comp ⟨e, he⟩)) :
    ClosedUnitSquareMapStokesProp (Fmap.comp ⟨e, he⟩) ω := by
  simpa using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquareMap_of_contDiff
      (Fmap := Fmap.comp ⟨e, he⟩) hω hcontdiff)

/-- Direct closed-square extension interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitSquare_extension_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace Y]
    (e : ClosedUnitSquare → Y) (he : Continuous e)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp (Fmap.comp ⟨e, he⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, he⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand (Fmap.comp ⟨e, he⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitSquareBoundaryIntegral (Fmap.comp ⟨e, he⟩) ω‖ ≤ B * area := by
  exact norm_closedUnitSquareBoundaryIntegral_le_of_contDiff
    (Fmap := Fmap.comp ⟨e, he⟩) hω hcontdiff hB hintegrand hJ hbound harea

/-- Oriented boundary vanishing at the bundled square-homeomorphism plus
glued-strip interface. The boundary continuity is inferred automatically from
the bundled homeomorphism data. -/
theorem curveIntegral_eq_zero_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [PseudoMetricSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
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
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [D.boundaryHomeomorph]
        exact D.homeomorph.continuous_toFun.comp continuous_closedUnitSquareBoundary⟩), ω x = 0 := by
  have hboundaryCont : Continuous boundary := by
    rw [D.boundaryHomeomorph]
    exact D.homeomorph.continuous_toFun.comp continuous_closedUnitSquareBoundary
  simpa using
    (curveIntegral_eq_zero_of_closedUnitSquare_homeomorphCylinderStripGluedArbitrarilyFineData_of_diffContOnCl
      (hboundaryCont := hboundaryCont) (D := D) (F := F) (ht := ht)
      hω hdω_symm hcontdiff)

/-- Oriented boundary vanishing at the direct square-homeomorphism plus
glued-strip interface furnished by the explicit square strip data. -/
theorem curveIntegral_eq_zero_of_closedUnitSquare_homeomorph_cylinderStripGlued_of_diffContOnCl
    {𝕜 E G Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {t : Set E} {ω : E → E →L[𝕜] G}
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (F : C(Y, E))
    (ht : ∀ a ∈ Set.Ioo (0 : I) 1, ∀ b ∈ Set.Ioo (0 : I) 1,
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
      (Set.Icc 0 1)) :
    ∫ᶜ x in unitAddCirclePath
      (F.comp ⟨boundary, by
        rw [hboundaryMap]
        exact e.continuous_toFun.comp continuous_closedUnitSquareBoundary⟩), ω x = 0 := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitSquareBoundary }
  simpa [D] using
    (curveIntegral_eq_zero_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_diffContOnCl
      (D := D) (F := F) (ht := ht) hω hdω_symm hcontdiff)


/-- The bundled square-homeomorphism-plus-glued-strip interface also yields
its Stokes package, expressed through the closed-square wrapper theorem. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩)) :
    ClosedUnitSquareMapStokesProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω := by
  simpa using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquareMap_of_contDiff
      (Fmap := Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) hω hcontdiff)

/-- Direct square-homeomorphism interface for the Stokes package. -/
theorem curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquare_homeomorph_cylinderStripGlued_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩)) :
    ClosedUnitSquareMapStokesProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩) ω := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitSquareBoundary }
  simpa [D] using
    (curveIntegral_eq_setIntegral_fderiv_skew_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
      (D := D) (Fmap := Fmap) hω hcontdiff)

/-- Bundled square-homeomorphism interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → Y}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand
          (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitSquareBoundaryIntegral
        (Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩) ω‖ ≤ B * area := by
  exact norm_closedUnitSquareBoundaryIntegral_le_of_contDiff
    (Fmap := Fmap.comp ⟨D.homeomorph, D.homeomorph.continuous_toFun⟩)
    hω hcontdiff hB hintegrand hJ hbound harea

/-- Direct square-homeomorphism interface for the calibrated Stokes norm bound. -/
theorem norm_curveIntegral_le_of_closedUnitSquare_homeomorph_cylinderStripGlued_of_contDiff
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [PseudoMetricSpace Y] [CompactSpace Y]
    {boundary : UnitAddCircle → Y}
    (e : ClosedUnitSquare ≃ₜ Y)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (Fmap : C(Y, E))
    {ω : E → E →L[ℝ] F}
    {B area : ℝ} {J : ℝ × ℝ → ℝ}
    (hω : closedOneFormContDiffProp ω)
    (hcontdiff : closedUnitSquareMapSquareContDiffProp
      (Fmap.comp ⟨e, e.continuous_toFun⟩))
    (hB : 0 ≤ B)
    (hintegrand : MeasureTheory.Integrable
      (fun x ↦ closedUnitSquareMapSkewIntegrand
        (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x)
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hJ : MeasureTheory.Integrable J
      (MeasureTheory.volume.restrict (Icc (0 : ℝ × ℝ) 1)))
    (hbound : ∀ x ∈ Icc (0 : ℝ × ℝ) 1,
      ‖closedUnitSquareMapSkewIntegrand
          (Fmap.comp ⟨e, e.continuous_toFun⟩) ω x‖ ≤ B * J x)
    (harea : ∫ x in Icc (0 : ℝ × ℝ) 1, J x ≤ area) :
    ‖closedUnitSquareBoundaryIntegral (Fmap.comp ⟨e, e.continuous_toFun⟩) ω‖ ≤ B * area := by
  let D : HomeomorphCylinderStripGluedArbitrarilyFineData closedUnitSquareBoundary boundary :=
    { homeomorph := e
      boundaryHomeomorph := hboundaryMap
      models := hasCylinderStripGluedArbitrarilyFineData_closedUnitSquareBoundary }
  simpa [D] using
    (norm_curveIntegral_le_of_closedUnitSquare_homeomorph_cylinderStripGluedArbitrarilyFineData_of_contDiff
      (D := D) (Fmap := Fmap) hω hcontdiff hB hintegrand hJ hbound harea)

end

end GromovFilling
