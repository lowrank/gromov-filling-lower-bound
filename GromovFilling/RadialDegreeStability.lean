import GromovFilling.DominantHarmonicDegree

/-!
# Stability of radial degree

The radial degree of a closed curve is locally constant as the omitted
point moves in the curve complement.  This is the key componentwise step
in the degree argument of Lemma 5.4.
-/

namespace GromovFilling

noncomputable section

lemma ne_zero_of_norm_sub_one_lt_one {c : ℂ} (hc : ‖c - 1‖ < 1) : c ≠ 0 := by
  intro h
  rw [h] at hc
  norm_num at hc

/-- A complex number in the open unit ball centered at `1` cannot point
in the negative-real direction after radial normalization. -/
lemma radialProjection_zero_ne_neg_one_of_norm_sub_one_lt_one
    {c : ℂ} (hc : ‖c - 1‖ < 1) :
    radialProjection 0 ⟨c, ne_zero_of_norm_sub_one_lt_one hc⟩ ≠
      (⟨(-1 : ℂ), by norm_num⟩ : ComplexUnitCircle) := by
  intro hneg
  have hcne : c ≠ 0 := ne_zero_of_norm_sub_one_lt_one hc
  have hval : c / (‖c‖ : ℂ) = -1 := by
    simpa [radialProjection] using congrArg Subtype.val hneg
  have hnormne : (‖c‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hcne)
  have hcreal : c = -(‖c‖ : ℂ) := by
    calc
      c = (c / (‖c‖ : ℂ)) * (‖c‖ : ℂ) :=
        (div_mul_cancel₀ c hnormne).symm
      _ = (-1 : ℂ) * (‖c‖ : ℂ) := by rw [hval]
      _ = -(‖c‖ : ℂ) := by ring
  have hnorm : ‖c - 1‖ = ‖c‖ + 1 := by
    have hdiff : c - 1 = -((‖c‖ + 1 : ℝ) : ℂ) := by
      calc
        c - 1 = -(‖c‖ : ℂ) - 1 :=
          congrArg (fun z : ℂ ↦ z - 1) hcreal
        _ = -((‖c‖ + 1 : ℝ) : ℂ) := by
          push_cast
          ring
    rw [hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hnorm] at hc
  linarith [norm_nonneg c]

/-- Pointwise multiplication of nonzero complex maps adds the degrees of
their radial normalizations. -/
theorem HasComplexCircleDegree.radialMap_mul
    (f g : UnitAddCircle → ℂ)
    (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    {d e : ℤ}
    (hfd : HasComplexCircleDegree (radialMap f 0 hf) d)
    (hgd : HasComplexCircleDegree (radialMap g 0 hg) e) :
    HasComplexCircleDegree
      (radialMap (fun x ↦ f x * g x) 0 (fun x ↦ mul_ne_zero (hf x) (hg x)))
      (d + e) := by
  have hproduct := hfd.mul hgd
  convert hproduct using 1
  funext x
  simp only [radialMap]
  exact radialProjection_zero_mul (f x) (g x) (hf x) (hg x)

/-- Quantitative local constancy of radial degree.  If the puncture moves
less than its distance to every point of the curve, the radial degree is
unchanged. -/
theorem radialMap_degree_stable
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (y₀ y : ℂ)
    (havoid₀ : ∀ x, curve x ≠ y₀) (havoid : ∀ x, curve x ≠ y)
    (hclose : ∀ x, ‖y - y₀‖ < ‖curve x - y₀‖)
    {d : ℤ}
    (hdegree : HasComplexCircleDegree (radialMap curve y₀ havoid₀) d) :
    HasComplexCircleDegree (radialMap curve y havoid) d := by
  let base : UnitAddCircle → ℂ := fun x ↦ curve x - y₀
  have hbase : ∀ x, base x ≠ 0 := fun x ↦
    sub_ne_zero.mpr (havoid₀ x)
  let correction : UnitAddCircle → ℂ := fun x ↦
    1 - (y - y₀) / base x
  have hcorrectionBound (x : UnitAddCircle) :
      ‖correction x - 1‖ < 1 := by
    have hbaseNorm : 0 < ‖base x‖ := norm_pos_iff.mpr (hbase x)
    change ‖(1 - (y - y₀) / base x) - 1‖ < 1
    rw [show (1 : ℂ) - (y - y₀) / base x - 1 =
      -((y - y₀) / base x) by ring, norm_neg, norm_div]
    exact (div_lt_one hbaseNorm).mpr (hclose x)
  have hcorrectionNe : ∀ x, correction x ≠ 0 := fun x ↦
    ne_zero_of_norm_sub_one_lt_one (hcorrectionBound x)
  have hcorrectionContinuous : Continuous correction := by
    dsimp only [correction, base]
    exact continuous_const.sub (continuous_const.div
      (hcurve.sub continuous_const) (fun x ↦ sub_ne_zero.mpr (havoid₀ x)))
  have hcorrectionDegree :
      HasComplexCircleDegree (radialMap correction 0 hcorrectionNe) 0 := by
    apply hasComplexCircleDegree_zero_of_avoids_cut
      (radialMap correction 0 hcorrectionNe)
      (continuous_radialMap correction 0 hcorrectionNe hcorrectionContinuous)
      (1 / 2)
    intro x hx
    have hx' : radialMap correction 0 hcorrectionNe x =
        (⟨(-1 : ℂ), by norm_num⟩ : ComplexUnitCircle) := by
      rw [unitAddCircleEquivComplexUnitCircle_half] at hx
      exact hx
    exact radialProjection_zero_ne_neg_one_of_norm_sub_one_lt_one
      (hcorrectionBound x) hx'
  have hbaseDegree :
      HasComplexCircleDegree (radialMap base 0 hbase) d := by
    convert hdegree using 1
    funext x
    apply Subtype.ext
    simp [base, radialMap, radialProjection]
  have hproductDegree := hbaseDegree.radialMap_mul
    base correction hbase hcorrectionNe hcorrectionDegree
  have hproductDegree' :
      HasComplexCircleDegree
        (radialMap (fun x ↦ base x * correction x) 0
          (fun x ↦ mul_ne_zero (hbase x) (hcorrectionNe x))) d := by
    simpa using hproductDegree
  convert hproductDegree' using 1
  funext x
  apply Subtype.ext
  simp only [radialMap, radialProjection, sub_zero]
  have hfactor : curve x - y = base x * correction x := by
    dsimp only [base, correction]
    field_simp [sub_ne_zero.mpr (havoid₀ x)]
  rw [hfactor]

/-- On a preconnected family of punctures which stays uniformly away
from the curve at each parameter, radial degree is constant.  The
`clearance` hypotheses are exactly what compactness of the boundary image
supplies in geometric applications. -/
theorem radialMap_degree_constant_on_preconnected
    {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    (p : Y → ℂ) (hp : Continuous p)
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (havoid : ∀ y x, curve x ≠ p y)
    (clearance : Y → ℝ) (hclearancePos : ∀ y, 0 < clearance y)
    (hclearance : ∀ y x, clearance y ≤ ‖curve x - p y‖)
    (y₀ : Y) {d : ℤ}
    (hdegree₀ :
      HasComplexCircleDegree (radialMap curve (p y₀) (havoid y₀)) d) :
    ∀ y : Y,
      HasComplexCircleDegree (radialMap curve (p y) (havoid y)) d := by
  let A : Set Y := {y | HasComplexCircleDegree
    (radialMap curve (p y) (havoid y)) d}
  have hAOpen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    let U : Set Y := {z | ‖p z - p y‖ < clearance y}
    have hUOpen : IsOpen U := by
      exact isOpen_lt (hp.sub continuous_const).norm continuous_const
    have hyU : y ∈ U := by
      change ‖p y - p y‖ < clearance y
      simpa using hclearancePos y
    have hUA : U ⊆ A := by
      intro z hz
      apply radialMap_degree_stable curve hcurve (p y) (p z)
        (havoid y) (havoid z)
      · intro x
        exact hz.trans_le (hclearance y x)
      · exact hy
    exact mem_nhds_iff.mpr ⟨U, hUA, hUOpen, hyU⟩
  have hAComplOpen : IsOpen Aᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    let U : Set Y := {z | ‖p z - p y‖ < clearance y / 2}
    have hUOpen : IsOpen U := by
      exact isOpen_lt (hp.sub continuous_const).norm continuous_const
    have hyU : y ∈ U := by
      change ‖p y - p y‖ < clearance y / 2
      simp [hclearancePos y]
    have hUCompl : U ⊆ Aᶜ := by
      intro z hz hzA
      change ‖p z - p y‖ < clearance y / 2 at hz
      apply hy
      apply radialMap_degree_stable curve hcurve (p z) (p y)
        (havoid z) (havoid y)
      · intro x
        have hdistSymm : ‖p y - p z‖ = ‖p z - p y‖ := by
          rw [← norm_neg, neg_sub]
        have htriangle : ‖curve x - p y‖ ≤
            ‖curve x - p z‖ + ‖p z - p y‖ := by
          calc
            ‖curve x - p y‖ = ‖(curve x - p z) + (p z - p y)‖ := by
              congr 1
              ring
            _ ≤ ‖curve x - p z‖ + ‖p z - p y‖ := norm_add_le _ _
        rw [hdistSymm]
        have hlower := hclearance y x
        linarith
      · exact hzA
    exact mem_nhds_iff.mpr ⟨U, hUCompl, hUOpen, hyU⟩
  have hAClosed : IsClosed A := by
    have hclosed : IsClosed (Aᶜ)ᶜ := isClosed_compl_iff.mpr hAComplOpen
    simpa using hclosed
  have hAClopen : IsClopen A := ⟨hAClosed, hAOpen⟩
  have hAUniv : A = Set.univ := hAClopen.eq_univ ⟨y₀, hdegree₀⟩
  intro y
  have hy : y ∈ A := by rw [hAUniv]; exact Set.mem_univ y
  exact hy

/-- Compactness of the additive circle supplies a positive lower bound
for the distance from each omitted point to the entire curve. -/
theorem exists_positive_curve_clearance
    {Y : Type*} (p : Y → ℂ)
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (havoid : ∀ y x, curve x ≠ p y) :
    ∃ clearance : Y → ℝ,
      (∀ y, 0 < clearance y) ∧
      ∀ y x, clearance y ≤ ‖curve x - p y‖ := by
  have hexists (y : Y) :
      ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ ‖curve x - p y‖ := by
    obtain ⟨c, hcpos, hc⟩ := isCompact_univ.exists_forall_le'
      ((hcurve.sub continuous_const).norm.continuousOn)
      (fun x _hx ↦ norm_pos_iff.mpr (sub_ne_zero.mpr (havoid y x)))
    exact ⟨c, hcpos, fun x ↦ hc x (Set.mem_univ x)⟩
  choose clearance hpos hbound using hexists
  exact ⟨clearance, hpos, hbound⟩

/-- Componentwise constancy with the clearance discharged automatically
by compactness of the boundary circle. -/
theorem radialMap_degree_constant_on_preconnected_of_compact_circle
    {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    (p : Y → ℂ) (hp : Continuous p)
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (havoid : ∀ y x, curve x ≠ p y)
    (y₀ : Y) {d : ℤ}
    (hdegree₀ :
      HasComplexCircleDegree (radialMap curve (p y₀) (havoid y₀)) d) :
    ∀ y : Y,
      HasComplexCircleDegree (radialMap curve (p y) (havoid y)) d := by
  obtain ⟨clearance, hpos, hbound⟩ :=
    exists_positive_curve_clearance p curve hcurve havoid
  exact radialMap_degree_constant_on_preconnected p hp curve hcurve havoid
    clearance hpos hbound y₀ hdegree₀

lemma curve_ne_of_mem_complement_component
    (curve : UnitAddCircle → ℂ) (y₀ y : ℂ)
    (hy : y ∈ connectedComponentIn (Set.range curve)ᶜ y₀)
    (x : UnitAddCircle) : curve x ≠ y := by
  intro hxy
  have hyCompl : y ∈ (Set.range curve)ᶜ :=
    connectedComponentIn_subset (Set.range curve)ᶜ y₀ hy
  exact hyCompl ⟨x, hxy⟩

/-- Radial degree is constant on the connected component of any omitted
point in the complement of a continuous closed curve. -/
theorem radialMap_degree_constant_on_complement_component
    (curve : UnitAddCircle → ℂ) (hcurve : Continuous curve)
    (y₀ : ℂ) (havoid₀ : ∀ x, curve x ≠ y₀) {d : ℤ}
    (hdegree₀ : HasComplexCircleDegree
      (radialMap curve y₀ havoid₀) d) :
    ∀ (y : ℂ)
      (hy : y ∈ connectedComponentIn (Set.range curve)ᶜ y₀),
      HasComplexCircleDegree
        (radialMap curve y
          (curve_ne_of_mem_complement_component curve y₀ y hy)) d := by
  let component : Set ℂ :=
    connectedComponentIn (Set.range curve)ᶜ y₀
  have hy₀Compl : y₀ ∈ (Set.range curve)ᶜ := by
    intro hy₀Range
    obtain ⟨x, hx⟩ := hy₀Range
    exact havoid₀ x hx
  let y₀Component : component :=
    ⟨y₀, mem_connectedComponentIn hy₀Compl⟩
  letI : PreconnectedSpace component :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have havoidComponent : ∀ (y : component) x, curve x ≠ (y : ℂ) := by
    intro y x
    exact curve_ne_of_mem_complement_component curve y₀ y y.property x
  have hdegreeComponent : HasComplexCircleDegree
      (radialMap curve ((y₀Component : component) : ℂ)
        (havoidComponent y₀Component)) d := by
    simpa [y₀Component] using hdegree₀
  have hconstant :=
    radialMap_degree_constant_on_preconnected_of_compact_circle
      (fun y : component ↦ (y : ℂ)) continuous_subtype_val
      curve hcurve havoidComponent y₀Component hdegreeComponent
  intro y hy
  exact hconstant ⟨y, hy⟩

end

end GromovFilling
