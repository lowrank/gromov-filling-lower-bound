import GromovFilling.RadialProjection

/-!
# Circle degree through real lifts

For the circle maps used in Lemma 5.4, an explicit lift to `ℝ` is both
more useful and lighter than a general homology-based definition of degree.
The integer by which the lift changes after one turn is the degree.
-/

namespace GromovFilling

noncomputable section

/-- Multiplication on the unit-norm complex subtype used by the Fourier
modules. -/
def complexUnitCircleMul (x y : ComplexUnitCircle) : ComplexUnitCircle :=
  ⟨(x : ℂ) * (y : ℂ), by rw [norm_mul, x.property, y.property, one_mul]⟩

/-- The chosen identification of the additive and complex unit circles
turns addition into complex multiplication. -/
theorem unitAddCircleEquivComplexUnitCircle_add (x y : UnitAddCircle) :
    unitAddCircleEquivComplexUnitCircle (x + y) =
      complexUnitCircleMul (unitAddCircleEquivComplexUnitCircle x)
        (unitAddCircleEquivComplexUnitCircle y) := by
  apply Subtype.ext
  change ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero (x + y) :
      Circle) : ℂ) =
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero x : Circle) *
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero y : Circle)
  rw [AddCircle.homeomorphCircle_apply, AddCircle.homeomorphCircle_apply,
    AddCircle.homeomorphCircle_apply]
  exact congrArg Subtype.val (AddCircle.toCircle_add x y)

/-- Half a turn corresponds to `-1` on the complex unit circle. -/
theorem unitAddCircleEquivComplexUnitCircle_half :
    unitAddCircleEquivComplexUnitCircle ((1 / 2 : ℝ) : UnitAddCircle) =
      (⟨(-1 : ℂ), by norm_num⟩ : ComplexUnitCircle) := by
  apply Subtype.ext
  change ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
      ((1 / 2 : ℝ) : UnitAddCircle) : Circle) : ℂ) = -1
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    Circle.coe_exp]
  rw [show (2 * Real.pi / (1 : ℝ)) * (1 / 2) = Real.pi by ring]
  exact Complex.exp_pi_mul_I

/-- A circle map has degree `d` if it admits a continuous real lift whose
change under one period is the integer `d`. -/
def HasCircleDegree (H : UnitAddCircle → UnitAddCircle) (d : ℤ) : Prop :=
  ∃ lift : ℝ → ℝ, Continuous lift ∧
    (∀ t : ℝ, (lift t : UnitAddCircle) = H (t : UnitAddCircle)) ∧
    ∀ t : ℝ, lift (t + 1) = lift t + (d : ℝ)

/-- The identity circle map has degree one. -/
theorem hasCircleDegree_id : HasCircleDegree id 1 := by
  refine ⟨id, continuous_id, ?_, ?_⟩
  · intro t
    rfl
  · intro t
    simp

/-- Any continuous circle map avoiding a point has degree zero.  The
canonical phase away from that point is a periodic real lift. -/
theorem hasCircleDegree_zero_of_avoids_cut
    (H : UnitAddCircle → UnitAddCircle) (hH : Continuous H)
    (cut : ℝ) (havoid : ∀ x, H x ≠ (cut : UnitAddCircle)) :
    HasCircleDegree H 0 := by
  refine ⟨circlePhaseAway cut H ∘ (fun t : ℝ ↦ (t : UnitAddCircle)), ?_, ?_, ?_⟩
  · exact (continuous_circlePhaseAway cut H hH havoid).comp
      (AddCircle.continuous_mk' (1 : ℝ))
  · intro t
    exact circlePhaseAway_projects cut H (t : UnitAddCircle)
  · intro t
    change circlePhaseAway cut H ((t + 1 : ℝ) : UnitAddCircle) =
      circlePhaseAway cut H (t : UnitAddCircle) + (0 : ℤ)
    simp

/-- Degrees add under pointwise addition of additive-circle maps. -/
theorem HasCircleDegree.add
    {H K : UnitAddCircle → UnitAddCircle} {d e : ℤ}
    (hH : HasCircleDegree H d) (hK : HasCircleDegree K e) :
    HasCircleDegree (fun x ↦ H x + K x) (d + e) := by
  obtain ⟨liftH, hliftH, hprojectH, hperiodH⟩ := hH
  obtain ⟨liftK, hliftK, hprojectK, hperiodK⟩ := hK
  refine ⟨fun t ↦ liftH t + liftK t, hliftH.add hliftK, ?_, ?_⟩
  · intro t
    rw [AddCircle.coe_add, hprojectH, hprojectK]
  · intro t
    change liftH (t + 1) + liftK (t + 1) =
      liftH t + liftK t + ((d + e : ℤ) : ℝ)
    rw [hperiodH, hperiodK]
    push_cast
    ring

/-- A map obtained by adding a continuous, single-valued circle phase to
the identity still has degree one. -/
theorem hasCircleDegree_one_add_of_avoids_cut
    (K : UnitAddCircle → UnitAddCircle) (hK : Continuous K)
    (cut : ℝ) (havoid : ∀ x, K x ≠ (cut : UnitAddCircle)) :
    HasCircleDegree (fun x ↦ x + K x) 1 := by
  simpa using hasCircleDegree_id.add
    (hasCircleDegree_zero_of_avoids_cut K hK cut havoid)

/-- The integer in the real-lift definition is unique. -/
theorem HasCircleDegree.unique
    {H : UnitAddCircle → UnitAddCircle} {d e : ℤ}
    (hd : HasCircleDegree H d) (he : HasCircleDegree H e) : d = e := by
  obtain ⟨liftD, hliftD, hprojectD, hperiodD⟩ := hd
  obtain ⟨liftE, hliftE, hprojectE, hperiodE⟩ := he
  have hconstant := real_circle_lifts_difference_eq liftD liftE
    hliftD hliftE (fun t ↦ (hprojectD t).trans (hprojectE t).symm)
    0 1
  have hperiodD0 : liftD 1 = liftD 0 + (d : ℝ) := by
    simpa using hperiodD 0
  have hperiodE0 : liftE 1 = liftE 0 + (e : ℝ) := by
    simpa using hperiodE 0
  rw [hperiodD0, hperiodE0] at hconstant
  have hcast : (d : ℝ) = (e : ℝ) := by linarith
  exact_mod_cast hcast

/-- Degree for a unit-complex-valued circle map, transported through the
fixed homeomorphism from the additive circle. -/
def HasComplexCircleDegree
    (H : UnitAddCircle → ComplexUnitCircle) (d : ℤ) : Prop :=
  HasCircleDegree (fun x ↦ unitAddCircleEquivComplexUnitCircle.symm (H x)) d

theorem HasComplexCircleDegree.unique
    {H : UnitAddCircle → ComplexUnitCircle} {d e : ℤ}
    (hd : HasComplexCircleDegree H d)
    (he : HasComplexCircleDegree H e) : d = e :=
  HasCircleDegree.unique hd he

/-- The standard additive-circle parametrization of the complex unit
circle has degree one. -/
theorem hasComplexCircleDegree_standard :
    HasComplexCircleDegree unitAddCircleEquivComplexUnitCircle 1 := by
  simpa [HasComplexCircleDegree] using hasCircleDegree_id

/-- Every constant unit-complex-valued circle map has degree zero. -/
theorem hasComplexCircleDegree_const (u : ComplexUnitCircle) :
    HasComplexCircleDegree (fun _ : UnitAddCircle ↦ u) 0 := by
  obtain ⟨r, _hrIco, hr⟩ := AddCircle.eq_coe_Ico
    (unitAddCircleEquivComplexUnitCircle.symm u)
  refine ⟨fun _ : ℝ ↦ r, continuous_const, ?_, ?_⟩
  · intro _t
    exact hr
  · intro _t
    norm_num

/-- Complex multiplication adds degrees. -/
theorem HasComplexCircleDegree.mul
    {H K : UnitAddCircle → ComplexUnitCircle} {d e : ℤ}
    (hH : HasComplexCircleDegree H d)
    (hK : HasComplexCircleDegree K e) :
    HasComplexCircleDegree
      (fun x ↦ complexUnitCircleMul (H x) (K x)) (d + e) := by
  unfold HasComplexCircleDegree at hH hK ⊢
  convert hH.add hK using 1
  funext x
  apply unitAddCircleEquivComplexUnitCircle.injective
  rw [unitAddCircleEquivComplexUnitCircle.apply_symm_apply,
    unitAddCircleEquivComplexUnitCircle_add,
    unitAddCircleEquivComplexUnitCircle.apply_symm_apply,
    unitAddCircleEquivComplexUnitCircle.apply_symm_apply]

/-- A continuous unit-complex-valued map which omits the image of a real
cut has degree zero. -/
theorem hasComplexCircleDegree_zero_of_avoids_cut
    (H : UnitAddCircle → ComplexUnitCircle) (hH : Continuous H)
    (cut : ℝ)
    (havoid : ∀ x,
      H x ≠ unitAddCircleEquivComplexUnitCircle (cut : UnitAddCircle)) :
    HasComplexCircleDegree H 0 := by
  apply hasCircleDegree_zero_of_avoids_cut
  · exact unitAddCircleEquivComplexUnitCircle.symm.continuous.comp hH
  · intro x hx
    apply havoid x
    rw [← hx]
    exact (unitAddCircleEquivComplexUnitCircle.apply_symm_apply (H x)).symm

end

end GromovFilling
