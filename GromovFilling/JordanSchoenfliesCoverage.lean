import GromovFilling.JordanSchoenfliesFoundation
import GromovFilling.Lemma54
import GromovFilling.SurfaceCoverage

/-!
# Jordan–Schönflies coverage for compact surfaces

This file turns the relative Jordan–Schönflies theorem into the missing
manuscript-facing coverage bridge.  An arbitrary parametrized Jordan curve is
straightened to the boundary of the model square.  Radial projection of that
square boundary has odd degree, and degree is constant throughout the bounded
complementary component.
-/

namespace GromovFilling

noncomputable section

open Set

/-- The standard isometric identification of the complex plane with the
Euclidean plane used by the vendored Schönflies theorem. -/
def complexPlaneHomeomorph : ℂ ≃ₜ Schoenflies.Plane :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph

@[simp]
theorem complexPlaneHomeomorph_apply_zero :
    complexPlaneHomeomorph 0 = 0 := by
  simp [complexPlaneHomeomorph]

@[simp]
theorem complexPlaneHomeomorph_symm_apply_zero :
    complexPlaneHomeomorph.symm 0 = 0 := by
  simp [complexPlaneHomeomorph]

/-- A continuous injective additive-circle parametrization is a Jordan curve
in the interval-parametrized sense used by the vendored Schönflies theorem. -/
theorem schoenflies_isJordanCurve_range_of_continuous_injective_circle
    (curve : UnitAddCircle → Schoenflies.Plane)
    (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    Schoenflies.IsJordanCurve (Set.range curve) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let f : ℝ → Schoenflies.Plane := fun t ↦ curve (t : UnitAddCircle)
  refine ⟨f, ?_, ?_⟩
  · refine
      { continuousOn :=
          (hcurve.comp (AddCircle.continuous_mk' (1 : ℝ))).continuousOn
        closes := ?_
        injOn := ?_ }
    · change curve ((0 : ℝ) : UnitAddCircle) =
        curve ((1 : ℝ) : UnitAddCircle)
      congr 1
      simp [AddCircle.coe_period]
    · intro a ha b hb hab
      have habCircle :
          ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) :=
        hinjective hab
      have ha' : a ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using ha
      have hb' : b ∈ Set.Ico (0 : ℝ) (0 + 1) := by simpa using hb
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (p := (1 : ℝ)) (a := (0 : ℝ)) ha' hb').mp habCircle
  · apply Set.Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨(t : UnitAddCircle), rfl⟩
    · rintro _ ⟨q, rfl⟩
      have hq := (AddCircle.equivIco (1 : ℝ) 0 q).2
      refine ⟨(AddCircle.equivIco (1 : ℝ) 0 q).1,
        Set.Ico_subset_Icc_self (by simpa using hq), ?_⟩
      change curve
          (((AddCircle.equivIco (1 : ℝ) 0 q).1 : ℝ) :
            UnitAddCircle) = curve q
      congr 1
      apply (AddCircle.equivIco (1 : ℝ) 0).injective
      exact AddCircle.equivIco_coe_eq hq

/-- The canonical homeomorphism from a continuously embedded circle to its
range. -/
def circleHomeomorphRange
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    UnitAddCircle ≃ₜ Set.range curve := by
  let toRange : UnitAddCircle → Set.range curve := fun x ↦
    ⟨curve x, ⟨x, rfl⟩⟩
  have hbijective : Function.Bijective toRange := by
    constructor
    · intro x y hxy
      exact hinjective (congrArg Subtype.val hxy)
    · rintro ⟨_y, x, rfl⟩
      exact ⟨x, rfl⟩
  let e : UnitAddCircle ≃ Set.range curve :=
    Equiv.ofBijective toRange hbijective
  have heContinuous : Continuous e := by
    change Continuous toRange
    exact hcurve.subtype_mk (fun x ↦ ⟨x, rfl⟩)
  exact Continuous.homeoOfEquivCompactToT2 heContinuous

@[simp]
theorem circleHomeomorphRange_coe
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (curve : UnitAddCircle → Y) (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) (t : UnitAddCircle) :
    ((circleHomeomorphRange curve hcurve hinjective t :
      Set.range curve) : Y) = curve t :=
  rfl

/-- The complex coordinates of a point on the model square have complex
sup norm one. -/
theorem complexSupNorm_complexPlaneHomeomorph_symm_of_mem_modelCurve
    (z : Schoenflies.Plane) (hz : z ∈ Schoenflies.modelCurve) :
    complexSupNorm (complexPlaneHomeomorph.symm z) = 1 := by
  change max |(complexPlaneHomeomorph.symm z).re|
      |(complexPlaneHomeomorph.symm z).im| = 1
  rw [show (complexPlaneHomeomorph.symm z).re = z 0 by
      simp [complexPlaneHomeomorph,
        Complex.orthonormalBasisOneI_repr_symm_apply],
    show (complexPlaneHomeomorph.symm z).im = z 1 by
      simp [complexPlaneHomeomorph,
        Complex.orthonormalBasisOneI_repr_symm_apply]]
  exact hz

/-- Radial projection identifies the model square boundary with the complex
unit circle. -/
def modelCurveRadialMap (z : Schoenflies.modelCurve) : ComplexUnitCircle :=
  radialProjection 0 ⟨complexPlaneHomeomorph.symm z, by
    intro hzero
    have hzzero : (z : Schoenflies.Plane) = 0 := by
      apply complexPlaneHomeomorph.symm.injective
      simpa using hzero
    have hz := z.property
    rw [hzzero] at hz
    norm_num [Schoenflies.modelCurve, Schoenflies.Plane.supNorm] at hz⟩

theorem continuous_modelCurveRadialMap :
    Continuous modelCurveRadialMap := by
  apply (continuous_radialProjection 0).comp
  exact (complexPlaneHomeomorph.symm.continuous.comp
    continuous_subtype_val).subtype_mk _

private theorem complexPlaneHomeomorph_symm_modelCurve_ne_zero
    (z : Schoenflies.modelCurve) :
    complexPlaneHomeomorph.symm (z : Schoenflies.Plane) ≠ 0 := by
  intro hzero
  have hzzero : (z : Schoenflies.Plane) = 0 := by
    apply complexPlaneHomeomorph.symm.injective
    simpa using hzero
  have hz := z.property
  rw [hzzero] at hz
  norm_num [Schoenflies.modelCurve, Schoenflies.Plane.supNorm] at hz

private theorem complexSupNorm_normalize
    (z : ℂ) (hz : z ≠ 0) :
    complexSupNorm (z / (‖z‖ : ℂ)) =
      ‖z‖⁻¹ * complexSupNorm z := by
  rw [show z / (‖z‖ : ℂ) =
      Complex.ofReal (‖z‖⁻¹) * z by
    simp [div_eq_mul_inv, mul_comm]]
  rw [complexSupNorm_ofReal_mul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz))]

theorem modelCurveRadialMap_injective :
    Function.Injective modelCurveRadialMap := by
  intro z w hzw
  let v : ℂ := complexPlaneHomeomorph.symm (z : Schoenflies.Plane)
  let u : ℂ := complexPlaneHomeomorph.symm (w : Schoenflies.Plane)
  have hv0 : v ≠ 0 :=
    complexPlaneHomeomorph_symm_modelCurve_ne_zero z
  have hu0 : u ≠ 0 :=
    complexPlaneHomeomorph_symm_modelCurve_ne_zero w
  have hvSup : complexSupNorm v = 1 :=
    complexSupNorm_complexPlaneHomeomorph_symm_of_mem_modelCurve z z.property
  have huSup : complexSupNorm u = 1 :=
    complexSupNorm_complexPlaneHomeomorph_symm_of_mem_modelCurve w w.property
  have hval : v / (‖v‖ : ℂ) = u / (‖u‖ : ℂ) := by
    simpa [modelCurveRadialMap, radialProjection, v, u] using
      congrArg Subtype.val hzw
  have hInvNorm : ‖v‖⁻¹ = ‖u‖⁻¹ := by
    have hsup := congrArg complexSupNorm hval
    rw [complexSupNorm_normalize v hv0,
      complexSupNorm_normalize u hu0, hvSup, huSup, mul_one, mul_one] at hsup
    exact hsup
  have hNorm : ‖v‖ = ‖u‖ := inv_injective hInvNorm
  have hval' : v / (‖u‖ : ℂ) = u / (‖u‖ : ℂ) := by
    simpa [hNorm] using hval
  have hvu : v = u := by
    apply (div_left_inj' ?_).mp hval'
    exact_mod_cast norm_ne_zero_iff.mpr hu0
  apply Subtype.ext
  apply complexPlaneHomeomorph.symm.injective
  exact hvu

theorem modelCurveRadialMap_surjective :
    Function.Surjective modelCurveRadialMap := by
  intro u
  let s : ℝ := complexSupNorm (u : ℂ)
  have hu0 : (u : ℂ) ≠ 0 := by
    intro hzero
    have : ‖(u : ℂ)‖ = 0 := by rw [hzero, norm_zero]
    rw [u.property] at this
    norm_num at this
  have hs0 : s ≠ 0 :=
    (complexSupNorm_ne_zero_iff (u : ℂ)).2 hu0
  have hspos : 0 < s := lt_of_le_of_ne
    (complexSupNorm_nonneg (u : ℂ)) (Ne.symm hs0)
  let v : ℂ := (s⁻¹ : ℝ) • (u : ℂ)
  have hvSup : complexSupNorm v = 1 := by
    rw [show v = (s⁻¹ : ℝ) • (u : ℂ) by rfl,
      complexSupNorm_real_smul,
      abs_of_pos (inv_pos.mpr hspos)]
    change s⁻¹ * s = 1
    exact inv_mul_cancel₀ hs0
  let z : Schoenflies.modelCurve :=
    ⟨complexPlaneHomeomorph v, by
      change Schoenflies.Plane.supNorm (complexPlaneHomeomorph v) = 1
      change max |(complexPlaneHomeomorph v) 0|
          |(complexPlaneHomeomorph v) 1| = 1
      simpa [complexPlaneHomeomorph,
        Complex.orthonormalBasisOneI_repr_apply,
        complexSupNorm] using hvSup⟩
  refine ⟨z, Subtype.ext ?_⟩
  have hvnorm : ‖v‖ = s⁻¹ := by
    rw [show v = Complex.ofReal s⁻¹ * (u : ℂ) by
        simp [v],
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hspos), u.property, mul_one]
  change ((modelCurveRadialMap z : ComplexUnitCircle) : ℂ) = (u : ℂ)
  rw [show ((modelCurveRadialMap z : ComplexUnitCircle) : ℂ) =
      v / (‖v‖ : ℂ) by
    simp [modelCurveRadialMap, radialProjection, z, v]]
  rw [hvnorm]
  change ((s⁻¹ : ℝ) : ℂ) * (u : ℂ) /
      (((s⁻¹ : ℝ) : ℂ)) = (u : ℂ)
  exact mul_div_cancel_left₀ (u : ℂ) (by exact_mod_cast inv_ne_zero hs0)

/-- Radial projection is a homeomorphism from the model square boundary
to the complex unit circle. -/
def modelCurveRadialHomeomorph :
    Schoenflies.modelCurve ≃ₜ ComplexUnitCircle := by
  letI : CompactSpace Schoenflies.modelCurve :=
    isCompact_iff_compactSpace.mp Schoenflies.isCompact_modelCurve
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective modelCurveRadialMap
      ⟨modelCurveRadialMap_injective, modelCurveRadialMap_surjective⟩)
    continuous_modelCurveRadialMap

@[simp]
theorem modelCurveRadialHomeomorph_apply
    (z : Schoenflies.modelCurve) :
    modelCurveRadialHomeomorph z = modelCurveRadialMap z :=
  by
    change (Equiv.ofBijective modelCurveRadialMap
      ⟨modelCurveRadialMap_injective, modelCurveRadialMap_surjective⟩) z = _
    rfl

/-- The canonical bounded Jordan region determined by a continuously
embedded complex circle. -/
def schoenfliesJordanInterior
    (curve : UnitAddCircle → ℂ) : Set ℂ :=
  complexPlaneHomeomorph.symm ''
    Schoenflies.inside
      (Set.range (complexPlaneHomeomorph ∘ curve))

/-- The canonical Jordan interior is open, connected, bounded, and is the
connected component of each of its points in the curve complement.  Thus it
is precisely the bounded component meant by `Ω_C` in Lemma 5.4. -/
theorem schoenfliesJordanInterior_is_bounded_component
    (curve : UnitAddCircle → ℂ)
    (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    IsOpen (schoenfliesJordanInterior curve) ∧
      IsConnected (schoenfliesJordanInterior curve) ∧
      Bornology.IsBounded (schoenfliesJordanInterior curve) ∧
      ∀ y ∈ schoenfliesJordanInterior curve,
        connectedComponentIn (Set.range curve)ᶜ y =
          schoenfliesJordanInterior curve := by
  let curveP : UnitAddCircle → Schoenflies.Plane :=
    complexPlaneHomeomorph ∘ curve
  have hcurveP : Continuous curveP :=
    complexPlaneHomeomorph.continuous.comp hcurve
  have hinjectiveP : Function.Injective curveP :=
    complexPlaneHomeomorph.injective.comp hinjective
  have hC : Schoenflies.IsJordanCurve (Set.range curveP) :=
    schoenflies_isJordanCurve_range_of_continuous_injective_circle
      curveP hcurveP hinjectiveP
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hRangeImage :
      complexPlaneHomeomorph.symm '' Set.range curveP =
        Set.range curve := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, ⟨t, ht⟩, hy⟩
      subst z
      subst y
      exact ⟨t, by simp [curveP]⟩
    · rintro y ⟨t, rfl⟩
      refine ⟨complexPlaneHomeomorph (curve t), ⟨t, rfl⟩, ?_⟩
      simp
  change IsOpen (complexPlaneHomeomorph.symm ''
      Schoenflies.inside (Set.range curveP)) ∧
    IsConnected (complexPlaneHomeomorph.symm ''
      Schoenflies.inside (Set.range curveP)) ∧
    Bornology.IsBounded (complexPlaneHomeomorph.symm ''
      Schoenflies.inside (Set.range curveP)) ∧ _
  refine ⟨complexPlaneHomeomorph.symm.isOpenMap _ hsep.isOpen_inside,
    (complexPlaneHomeomorph.symm.isConnected_image).2
      hsep.isConnected_inside, ?_, ?_⟩
  · have hcompactClosure :
        IsCompact (closure (Schoenflies.inside (Set.range curveP))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure
        hsep.isBounded_inside.closure
    exact (hcompactClosure.image
      complexPlaneHomeomorph.symm.continuous).isBounded.subset
        (Set.image_mono subset_closure)
  · rintro y ⟨x, hx, rfl⟩
    have hxCompl : x ∈ (Set.range curveP)ᶜ := hx.1
    have hcomponent :=
      complexPlaneHomeomorph.symm.image_connectedComponentIn hxCompl
    rw [complexPlaneHomeomorph.symm.image_compl, hRangeImage,
      hsep.connectedComponentIn_eq_inside hx] at hcomponent
    exact hcomponent.symm

/-- The canonical bounded Jordan interior is disjoint from its boundary
curve. -/
theorem schoenfliesJordanInterior_disjoint_range
    (curve : UnitAddCircle → ℂ) :
    Disjoint (schoenfliesJordanInterior curve) (Set.range curve) := by
  let curveP : UnitAddCircle → Schoenflies.Plane :=
    complexPlaneHomeomorph ∘ curve
  have hRangeImage :
      complexPlaneHomeomorph.symm '' Set.range curveP =
        Set.range curve := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, ⟨t, ht⟩, hy⟩
      subst z
      subst y
      exact ⟨t, by simp [curveP]⟩
    · rintro y ⟨t, rfl⟩
      refine ⟨complexPlaneHomeomorph (curve t), ⟨t, rfl⟩, ?_⟩
      simp
  have hsource : Disjoint
      (Schoenflies.inside (Set.range curveP)) (Set.range curveP) := by
    rw [Set.disjoint_left]
    exact fun _ hxInside hxCurve ↦ hxInside.1 hxCurve
  have himage := Set.disjoint_image_of_injective
    complexPlaneHomeomorph.symm.injective hsource
  rw [hRangeImage] at himage
  exact himage

/-- A parametrization of the model square boundary, read in complex
coordinates. -/
def modelCurveComplexParam
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve) :
    UnitAddCircle → ℂ := fun t ↦
  complexPlaneHomeomorph.symm (k t)

theorem continuous_modelCurveComplexParam
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve) :
    Continuous (modelCurveComplexParam k) :=
  complexPlaneHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp k.continuous)

theorem modelCurveComplexParam_ne_zero
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve)
    (t : UnitAddCircle) :
    modelCurveComplexParam k t ≠ 0 :=
  complexPlaneHomeomorph_symm_modelCurve_ne_zero (k t)

theorem range_modelCurveComplexParam
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve) :
    Set.range (modelCurveComplexParam k) =
      complexPlaneHomeomorph.symm '' Schoenflies.modelCurve := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨k t, (k t).property, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    let z' : Schoenflies.modelCurve := ⟨z, hz⟩
    exact ⟨k.symm z', by
      simp [modelCurveComplexParam, z']⟩

/-- Every homeomorphic parametrization of the model square has odd radial
degree about the origin. -/
theorem exists_odd_hasComplexCircleDegree_modelCurve_at_zero
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve) :
    ∃ d : ℤ,
      HasComplexCircleDegree
        (radialMap (modelCurveComplexParam k) 0
          (modelCurveComplexParam_ne_zero k)) d ∧
      Odd d := by
  let r : UnitAddCircle ≃ₜ UnitAddCircle :=
    (k.trans modelCurveRadialHomeomorph).trans
      unitAddCircleEquivComplexUnitCircle.symm
  obtain ⟨d, hd, hodd⟩ :=
    exists_odd_hasCircleDegree_circleHomeomorph r
  refine ⟨d, ?_, hodd⟩
  change HasCircleDegree
    (fun t ↦ unitAddCircleEquivComplexUnitCircle.symm
      (radialMap (modelCurveComplexParam k) 0
        (modelCurveComplexParam_ne_zero k) t)) d
  convert hd using 1

/-- The complex image of the model-square interior lies in the complement
component of the origin. -/
theorem complex_modelCurve_inside_subset_component
    (k : UnitAddCircle ≃ₜ Schoenflies.modelCurve) :
    complexPlaneHomeomorph.symm ''
        Schoenflies.inside Schoenflies.modelCurve ⊆
      connectedComponentIn
        (Set.range (modelCurveComplexParam k))ᶜ 0 := by
  let D : Set ℂ := complexPlaneHomeomorph.symm ''
    Schoenflies.inside Schoenflies.modelCurve
  have hsep := Schoenflies.jordan_curve_theorem
    Schoenflies.isJordanCurve_modelCurve
  have hDConnected : IsConnected D :=
    (complexPlaneHomeomorph.symm.isConnected_image).2
      hsep.isConnected_inside
  have hzeroInside : (0 : Schoenflies.Plane) ∈
      Schoenflies.inside Schoenflies.modelCurve := by
    rw [Schoenflies.inside_modelCurve]
    change Schoenflies.Plane.supDist 0 0 < 1
    simp
  have hzeroD : (0 : ℂ) ∈ D := by
    exact ⟨0, hzeroInside, by simp⟩
  have hDCompl : D ⊆ (Set.range (modelCurveComplexParam k))ᶜ := by
    rw [range_modelCurveComplexParam k]
    rintro _ ⟨z, hzInside, rfl⟩ ⟨w, hwCurve, hw⟩
    have hzw : z = w := complexPlaneHomeomorph.symm.injective hw.symm
    exact hzInside.1 (hzw ▸ hwCurve)
  exact hDConnected.isPreconnected.subset_connectedComponentIn
    hzeroD hDCompl

/-- Jordan–Schönflies straightens an arbitrary parametrized complex Jordan
curve to the model square boundary and carries its bounded complementary
region into the model square interior. -/
theorem exists_jordanSchoenflies_straightening
    (curve : UnitAddCircle → ℂ)
    (hcurve : Continuous curve)
    (hinjective : Function.Injective curve) :
    ∃ Φ : ℂ ≃ₜ ℂ, ∃ k : UnitAddCircle ≃ₜ Schoenflies.modelCurve,
      (∀ t, Φ (curve t) = complexPlaneHomeomorph.symm (k t)) ∧
      Set.MapsTo Φ (schoenfliesJordanInterior curve)
        (complexPlaneHomeomorph.symm ''
          Schoenflies.inside Schoenflies.modelCurve) := by
  let curveP : UnitAddCircle → Schoenflies.Plane :=
    complexPlaneHomeomorph ∘ curve
  have hcurveP : Continuous curveP :=
    complexPlaneHomeomorph.continuous.comp hcurve
  have hinjectiveP : Function.Injective curveP :=
    complexPlaneHomeomorph.injective.comp hinjective
  have hC : Schoenflies.IsJordanCurve (Set.range curveP) :=
    schoenflies_isJordanCurve_range_of_continuous_injective_circle
      curveP hcurveP hinjectiveP
  let p : UnitAddCircle ≃ₜ Set.range curveP :=
    circleHomeomorphRange curveP hcurveP hinjectiveP
  obtain ⟨q⟩ := hC.homeomorph_modelCurve
  let k : UnitAddCircle ≃ₜ Schoenflies.modelCurve := p.trans q
  obtain ⟨F, hF⟩ := planeJordanSchoenflies_of_homeomorph
    hC Schoenflies.isJordanCurve_modelCurve q
  let Φ : ℂ ≃ₜ ℂ :=
    complexPlaneHomeomorph.trans (F.trans complexPlaneHomeomorph.symm)
  have hFC : F '' Set.range curveP = Schoenflies.modelCurve := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hFx := hF ⟨x, hx⟩
      rw [hFx]
      exact (q ⟨x, hx⟩).property
    · intro y hy
      let y' : Schoenflies.modelCurve := ⟨y, hy⟩
      refine ⟨q.symm y', (q.symm y').property, ?_⟩
      have hFq := hF (q.symm y')
      rw [hFq]
      exact congrArg Subtype.val (q.apply_symm_apply y')
  have hmapsInside : Set.MapsTo F
      (Schoenflies.inside (Set.range curveP))
      (Schoenflies.inside Schoenflies.modelCurve) := by
    intro x hx
    have hsepC := Schoenflies.jordan_curve_theorem hC
    have hxCompl : x ∈ (Set.range curveP)ᶜ := hx.1
    have hcomponent := F.image_connectedComponentIn hxCompl
    rw [F.image_compl, hFC,
      hsepC.connectedComponentIn_eq_inside hx] at hcomponent
    have hcompactClosure :
        IsCompact (closure (Schoenflies.inside (Set.range curveP))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure
        hsepC.isBounded_inside.closure
    have hboundedImage :
        Bornology.IsBounded
          (F '' Schoenflies.inside (Set.range curveP)) :=
      (hcompactClosure.image F.continuous).isBounded.subset
        (Set.image_mono subset_closure)
    refine ⟨?_, ?_⟩
    · intro hFx
      rw [← hFC] at hFx
      obtain ⟨z, hz, hzF⟩ := hFx
      have hzx : z = x := F.injective hzF
      exact hx.1 (hzx ▸ hz)
    · rw [← hcomponent]
      exact hboundedImage
  refine ⟨Φ, k, ?_, ?_⟩
  · intro t
    change complexPlaneHomeomorph.symm
        (F (complexPlaneHomeomorph (curve t))) =
      complexPlaneHomeomorph.symm (k t)
    congr 1
    change F (curveP t) = (k t : Schoenflies.Plane)
    simpa [k, p] using hF (p t)
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨F x, hmapsInside hx, ?_⟩
    simp [Φ]

/-- The bounded component of an arbitrary complex Jordan curve is covered
by every continuous extension whose source boundary has the odd-degree
obstruction.  Jordan–Schönflies supplies the odd radial degree internally. -/
theorem schoenfliesJordanInterior_subset_range_of_oddBoundaryDegreeObstruction
    {X : Type*} [TopologicalSpace X]
    (boundary : UnitAddCircle → X)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : X → ℂ) (hG : Continuous G)
    (curve : UnitAddCircle → ℂ)
    (hcurve : Continuous curve)
    (hinjective : Function.Injective curve)
    (hboundary : ∀ t, G (boundary t) = curve t) :
    schoenfliesJordanInterior curve ⊆ Set.range G := by
  obtain ⟨Φ, k, hstraight, hmapsInside⟩ :=
    exists_jordanSchoenflies_straightening curve hcurve hinjective
  intro y hy
  have hΦyInside : Φ y ∈ complexPlaneHomeomorph.symm ''
      Schoenflies.inside Schoenflies.modelCurve :=
    hmapsInside hy
  have hΦyComponent : Φ y ∈ connectedComponentIn
      (Set.range (modelCurveComplexParam k))ᶜ 0 :=
    complex_modelCurve_inside_subset_component k hΦyInside
  obtain ⟨d, hdegreeZero, hodd⟩ :=
    exists_odd_hasComplexCircleDegree_modelCurve_at_zero k
  have hdegreeΦy : HasComplexCircleDegree
      (radialMap (modelCurveComplexParam k) (Φ y)
        (curve_ne_of_mem_complement_component
          (modelCurveComplexParam k) 0 (Φ y) hΦyComponent)) d :=
    radialMap_degree_constant_on_complement_component
      (modelCurveComplexParam k)
      (continuous_modelCurveComplexParam k)
      0 (modelCurveComplexParam_ne_zero k) hdegreeZero
      (Φ y) hΦyComponent
  let G' : X → ℂ := Φ ∘ G
  have hG' : Continuous G' := Φ.continuous.comp hG
  have hboundary' : ∀ t, G' (boundary t) =
      modelCurveComplexParam k t := by
    intro t
    rw [show G' (boundary t) = Φ (G (boundary t)) by rfl,
      hboundary t, hstraight t]
    rfl
  have hboundaryAvoid : ∀ t, G' (boundary t) ≠ Φ y := by
    intro t
    rw [hboundary' t]
    exact curve_ne_of_mem_complement_component
      (modelCurveComplexParam k) 0 (Φ y) hΦyComponent t
  have hdegreeBoundary : HasComplexCircleDegree
      (radialMap (G' ∘ boundary) (Φ y) hboundaryAvoid) d := by
    convert hdegreeΦy using 1
    funext t
    apply Subtype.ext
    simp only [radialMap, radialProjection, Function.comp_apply,
      hboundary']
  have hΦyRange : Φ y ∈ Set.range G' :=
    mem_range_of_odd_boundary_radial_degree boundary hobstruction
      G' hG' (Φ y) hboundaryAvoid d hdegreeBoundary hodd
  obtain ⟨x, hx⟩ := hΦyRange
  refine ⟨x, ?_⟩
  apply Φ.injective
  exact hx

/-- **Lemma 5.4, coverage.**  A continuous map from a compact connected
surface with exactly one parametrized boundary component covers the canonical
bounded component enclosed by its embedded boundary trace. -/
theorem lemma54_schoenfliesJordanInterior_subset_range
    (S : Type*) [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] [CompactSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 S]
    (boundary : UnitAddCircle → S)
    (hboundaryContinuous : Continuous boundary)
    (hboundaryInjective : Function.Injective boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary S)
    (G : S → ℂ) (hG : Continuous G)
    (htraceInjective : Function.Injective (G ∘ boundary)) :
    schoenfliesJordanInterior (G ∘ boundary) ⊆ Set.range G := by
  apply
    schoenfliesJordanInterior_subset_range_of_oddBoundaryDegreeObstruction
      boundary
      (hasOddBoundaryDegreeObstruction_of_compact_connected_surface_boundary
        S boundary hboundaryContinuous hboundaryInjective hboundaryRange)
      G hG (G ∘ boundary) (hG.comp hboundaryContinuous)
      htraceInjective
  intro t
  rfl

end

end GromovFilling
