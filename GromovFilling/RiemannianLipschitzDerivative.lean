import GromovFilling.DistanceProfile
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Lipschitz bounds for Riemannian manifold derivatives

This file supplies the local metric-to-differential bridge needed for the
Riemannian distance-profile argument.  The first lemma is a one-dimensional
bounded-derivative criterion: a `C¹` curve in a Riemannian manifold is
Lipschitz on an open convex parameter set whenever its manifold derivative
has a uniform bound there.
-/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- A `C¹` curve with uniformly bounded Riemannian derivative is Lipschitz
on an open convex parameter set. -/
theorem lipschitzOnWith_of_contMDiffOn_of_enorm_mfderiv_le
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (F : ℝ → M) (s : Set ℝ) (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    {C : ℝ≥0}
    (hF : ContMDiffOn 𝓘(ℝ, ℝ) I 1 F s)
    (hD : ∀ t ∈ s, ‖mfderiv 𝓘(ℝ, ℝ) I F t‖ₑ ≤ C) :
    LipschitzOnWith C F s := by
  intro a ha b hb
  rw [IsRiemannianManifold.out (I := I)]
  let η := ContinuousAffineMap.lineMap (R := ℝ) a b
  let γ := F ∘ η
  have hη : Icc (0 : ℝ) 1 ⊆ ⇑η ⁻¹' s := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact hsConvex.segment_subset ha hb
  have η_smooth : CMDiff[Icc (0 : ℝ) 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have γ_smooth : CMDiff[Icc (0 : ℝ) 1] 1 γ :=
    hF.comp η_smooth hη
  have hpath : riemannianEDist I (F a) (F b) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength γ_smooth
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · exact zero_le_one
  apply hpath.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,
    pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hηdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) η t := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (ContinuousAffineMap.contDiff η).differentiable one_ne_zero t
  have hFdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I F (η t) :=
    ((hF (η t) (hη ht)).contMDiffAt
      (hsOpen.mem_nhds (hη ht))).mdifferentiableAt one_ne_zero
  have hcomp : mfderiv[Icc (0 : ℝ) 1] γ t =
      (mfderiv 𝓘(ℝ, ℝ) I F (η t)) ∘L
        (mfderiv[Icc (0 : ℝ) 1] η t) := by
    simpa only [mfderivWithin_univ] using
      (mfderivWithin_comp (x := t) (u := Set.univ)
        hFdiff.mdifferentiableWithinAt
        (η_smooth.mdifferentiableOn one_ne_zero t ht)
        (by simp)
        (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr
          (uniqueDiffOn_Icc zero_lt_one t ht)))
  have happly : mfderiv[Icc (0 : ℝ) 1] γ t 1 =
      (mfderiv 𝓘(ℝ, ℝ) I F (η t))
        (mfderiv[Icc (0 : ℝ) 1] η t 1) :=
    congr($hcomp 1)
  rw [happly]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact hD (η t) (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    simp only [η]
    exact le_of_eq rfl

/-- The inverse-chart line through an interior point with prescribed
intrinsic tangent velocity.  Its coordinate velocity is obtained by applying
the derivative of the extended chart at the base point. -/
def riemannianTangentChartLine
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (x : M) (v : TangentSpace I x) : ℝ → M :=
  fun t ↦ (extChartAt I x).symm
    (extChartAt I x x + t •
      NormedSpace.fromTangentSpace (extChartAt I x x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v))

@[simp]
theorem riemannianTangentChartLine_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (x : M) (v : TangentSpace I x) :
    riemannianTangentChartLine I x v 0 = x := by
  simp [riemannianTangentChartLine]

private theorem mfderiv_riemannianTangentChartLine
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (x : M) (v : TangentSpace I x) {t : ℝ}
    (ht : extChartAt I x x + t •
      NormedSpace.fromTangentSpace (extChartAt I x x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v) ∈
        interior (extChartAt I x).target) :
    mfderiv 𝓘(ℝ, ℝ) I (riemannianTangentChartLine I x v) t =
      (((trivializationAt E (TangentSpace I) x).symmL ℝ
          (riemannianTangentChartLine I x v t)) ∘L
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x)) ∘L
      ContinuousLinearMap.toSpanSingleton ℝ v := by
  let y₀ : E := extChartAt I x x
  let A : TangentSpace I x →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
  let w : E := NormedSpace.fromTangentSpace (extChartAt I x x)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v)
  let η : ℝ → E := fun s ↦ y₀ + s • w
  let γ : ℝ → M := (extChartAt I x).symm ∘ η
  have ht' : η t ∈ interior (extChartAt I x).target := by
    simpa only [η, y₀, w] using ht
  have htarget : η t ∈ (extChartAt I x).target := interior_subset ht'
  have hsourceExt : γ t ∈ (extChartAt I x).source := by
    exact (extChartAt I x).map_target htarget
  have hsource : γ t ∈ (chartAt H x).source := by
    simpa only [extChartAt_source] using hsourceExt
  have hround : extChartAt I x (γ t) = η t := by
    exact (extChartAt I x).right_inv htarget
  have hηdiff : DifferentiableAt ℝ η t := by
    dsimp only [η]
    fun_prop
  have hsymmdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (extChartAt I x).symm (η t) := by
    exact (((contMDiffOn_extChartAt_symm x).mono interior_subset
      (η t) ht').contMDiffAt
        (isOpen_interior.mem_nhds ht')).mdifferentiableAt one_ne_zero
  have houter : mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (η t) =
      (trivializationAt E (TangentSpace I) x).symmL ℝ (γ t) := by
    calc
      mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (η t) =
          mfderiv[range I] (extChartAt I x).symm (η t) := by
            symm
            apply mfderivWithin_of_mem_nhds
            exact mem_interior_iff_mem_nhds.mp
              (interior_mono (extChartAt_target_subset_range x) ht')
      _ = (trivializationAt E (TangentSpace I) x).symmL ℝ (γ t) := by
        rw [← hround]
        exact (TangentBundle.symmL_trivializationAt hsource).symm
  have hA : A = mfderiv I 𝓘(ℝ, E) (extChartAt I x) x := by
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (mem_chart_source H x)
  have hw : w = A v := by
    dsimp only [w]
    rw [← hA]
    rfl
  have hηderiv : fderiv ℝ η t =
      A ∘L ContinuousLinearMap.toSpanSingleton ℝ v := by
    have hhas : HasDerivAt η w t := by
      simpa only [η, one_smul] using
        (((hasDerivAt_id t).smul_const w).const_add y₀)
    rw [hhas.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro q
    simp [hw]
  have hfinal : mfderiv 𝓘(ℝ, ℝ) I γ t =
      (((trivializationAt E (TangentSpace I) x).symmL ℝ (γ t)) ∘L A) ∘L
        ContinuousLinearMap.toSpanSingleton ℝ v := by
    rw [mfderiv_comp t hsymmdiff hηdiff.mdifferentiableAt,
      mfderiv_eq_fderiv, houter, hηderiv]
    simp only [ContinuousLinearMap.comp_assoc]
    rfl
  simpa only [γ, η, y₀, w, A, riemannianTangentChartLine] using hfinal

/-- At the base point, the inverse-chart line has exactly the prescribed
intrinsic tangent velocity. -/
theorem mfderiv_riemannianTangentChartLine_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x) :
    mfderiv 𝓘(ℝ, ℝ) I (riemannianTangentChartLine I x v) 0 =
      ContinuousLinearMap.toSpanSingleton ℝ v := by
  rw [mfderiv_riemannianTangentChartLine I x v
    (by simpa using I.isInteriorPoint_iff.mp hx)]
  apply ContinuousLinearMap.ext
  intro t
  simp only [ContinuousLinearMap.comp_apply]
  rw [riemannianTangentChartLine_zero]
  exact Trivialization.symmL_continuousLinearMapAt
    (R := ℝ) (trivializationAt E (TangentSpace I) x)
    (FiberBundle.mem_baseSet_trivializationAt' x) _

/-- On a sufficiently small interval, the inverse-chart line with intrinsic
velocity `v` is Lipschitz with constant arbitrarily close to `‖v‖`. -/
theorem exists_lipschitzOnWith_riemannianTangentChartLine
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x)
    {r : ℝ} (hr : 1 < r) :
    ∃ ε > 0, LipschitzOnWith (Real.toNNReal (r * ‖v‖))
      (riemannianTangentChartLine I x v) (ball (0 : ℝ) ε) := by
  let y₀ : E := extChartAt I x x
  let A : TangentSpace I x →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x
  let w : E := NormedSpace.fromTangentSpace (extChartAt I x x)
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v)
  let η : ℝ → E := fun t ↦ y₀ + t • w
  let γ : ℝ → M := riemannianTangentChartLine I x v
  have hηcontinuous : Continuous η := by
    dsimp only [η]
    fun_prop
  have hηcont : Tendsto η (𝓝 0) (𝓝 y₀) := by
    exact hηcontinuous.tendsto' 0 y₀ (by simp [η])
  have hγeq : γ = (extChartAt I x).symm ∘ η := by
    rfl
  have hγcontinuousAt : ContinuousAt γ 0 := by
    rw [hγeq]
    exact (continuousAt_extChartAt_symm x).comp_of_eq
      hηcontinuous.continuousAt (by simp [η, y₀])
  have hγcont : Tendsto γ (𝓝 0) (𝓝 x) := by
    rw [← show γ 0 = x by simp [γ]]
    exact hγcontinuousAt
  have hcoord : ∀ᶠ t in 𝓝 (0 : ℝ),
      η t ∈ interior (extChartAt I x).target :=
    hηcont (isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hx))
  have hnorm : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖((trivializationAt E (TangentSpace I) x).symmL ℝ (γ t)) ∘L A‖ < r := by
    exact hγcont
      (eventually_norm_symmL_trivializationAt_comp_self_lt
        E (fun y : M ↦ TangentSpace I y) x hr)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcoord.and hnorm)
  refine ⟨ε, hε, lipschitzOnWith_of_contMDiffOn_of_enorm_mfderiv_le
    I γ (ball (0 : ℝ) ε) isOpen_ball (convex_ball 0 ε) ?_ ?_⟩
  · rw [hγeq]
    have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η := by
      rw [contMDiff_iff_contDiff]
      dsimp only [η]
      fun_prop
    exact (contMDiffOn_extChartAt_symm x).comp hηsmooth.contMDiffOn
      (fun t ht ↦ show η t ∈ (extChartAt I x).target from
        interior_subset (hball ht).1)
  · intro t ht
    have htTarget : extChartAt I x x + t •
        NormedSpace.fromTangentSpace (extChartAt I x x)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v) ∈
          interior (extChartAt I x).target := by
      simpa only [η, y₀, w] using (hball ht).1
    have hD : ‖mfderiv 𝓘(ℝ, ℝ) I γ t‖ ≤ r * ‖v‖ := by
      rw [show γ = riemannianTangentChartLine I x v from rfl,
        mfderiv_riemannianTangentChartLine I x v htTarget]
      calc
        _ ≤ ‖((trivializationAt E (TangentSpace I) x).symmL ℝ
                (riemannianTangentChartLine I x v t)) ∘L A‖ *
              ‖ContinuousLinearMap.toSpanSingleton ℝ v‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ r * ‖v‖ := by
          rw [ContinuousLinearMap.norm_toSpanSingleton]
          gcongr
          exact (hball ht).2.le
    simp only [enorm, nnnorm]
    rw [ENNReal.coe_le_coe]
    apply (NNReal.coe_le_coe).mp
    rw [Real.coe_toNNReal]
    · exact hD
    · positivity

/-- The inverse-chart line is manifold differentiable at its base point. -/
theorem mdifferentiableAt_riemannianTangentChartLine_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (x : M) (hx : I.IsInteriorPoint x) (v : TangentSpace I x) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I
      (riemannianTangentChartLine I x v) 0 := by
  let η : ℝ → E := fun t ↦ extChartAt I x x + t •
    NormedSpace.fromTangentSpace (extChartAt I x x)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v)
  have hηdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η 0 := by
    rw [mdifferentiableAt_iff_differentiableAt]
    dsimp only [η]
    fun_prop
  have hsymmdiff : MDifferentiableAt 𝓘(ℝ, E) I
      (extChartAt I x).symm (η 0) := by
    have htarget : η 0 ∈ interior (extChartAt I x).target := by
      simpa only [η, zero_smul, add_zero] using I.isInteriorPoint_iff.mp hx
    exact (((contMDiffOn_extChartAt_symm x).mono interior_subset
      (η 0) htarget).contMDiffAt
        (isOpen_interior.mem_nhds htarget)).mdifferentiableAt one_ne_zero
  simpa only [η, riemannianTangentChartLine, Function.comp_def] using
    hsymmdiff.comp 0 hηdiff

/-- At every interior differentiability point, the intrinsic derivative of a
globally Lipschitz real-valued function is bounded by its Lipschitz constant. -/
theorem norm_mfderiv_real_le_of_lipschitzWith
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : M) (hx : I.IsInteriorPoint x)
    (hfdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    ‖mfderiv I 𝓘(ℝ, ℝ) f x‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg fun v ↦ ?_
  apply (le_iff_forall_one_lt_le_mul₀
    (mul_nonneg K.coe_nonneg (norm_nonneg v))).mpr
  intro r hr
  obtain ⟨ε, hε, hlineLip⟩ :=
    exists_lipschitzOnWith_riemannianTangentChartLine I x hx v hr
  let γ : ℝ → M := riemannianTangentChartLine I x v
  have hcompLip : LipschitzOnWith
      (K * Real.toNNReal (r * ‖v‖)) (f ∘ γ) (ball (0 : ℝ) ε) :=
    hf.comp_lipschitzOnWith hlineLip
  have hderivBound : ‖fderiv ℝ (f ∘ γ) 0‖ ≤
      (K * Real.toNNReal (r * ‖v‖) : ℝ≥0) :=
    norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds 0 hε) hcompLip
  have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := by
    exact mdifferentiableAt_riemannianTangentChartLine_zero I x hx v
  have hfdiff' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ 0) := by
    simpa only [γ, riemannianTangentChartLine_zero] using hfdiff
  have hchainM := mfderiv_comp 0 hfdiff' hγdiff
  rw [show γ = riemannianTangentChartLine I x v from rfl,
    mfderiv_riemannianTangentChartLine_zero I x hx v,
    riemannianTangentChartLine_zero] at hchainM
  have hchain : fderiv ℝ (f ∘ γ) 0 =
      (mfderiv I 𝓘(ℝ, ℝ) f x) ∘L
        ContinuousLinearMap.toSpanSingleton ℝ v := by
    simpa only [mfderiv_eq_fderiv, γ,
      riemannianTangentChartLine_zero] using hchainM
  have happly : fderiv ℝ (f ∘ γ) 0 1 =
      mfderiv I 𝓘(ℝ, ℝ) f x v := by
    rw [hchain]
    change mfderiv I 𝓘(ℝ, ℝ) f x
      (ContinuousLinearMap.toSpanSingleton ℝ v 1) = _
    rw [ContinuousLinearMap.toSpanSingleton_apply_one]
  calc
    ‖mfderiv I 𝓘(ℝ, ℝ) f x v‖ = ‖fderiv ℝ (f ∘ γ) 0 1‖ :=
      congrArg norm happly.symm
    _ ≤ ‖fderiv ℝ (f ∘ γ) 0‖ := by
      simpa using ContinuousLinearMap.le_opNorm (fderiv ℝ (f ∘ γ) 0) 1
    _ ≤ ((K * Real.toNNReal (r * ‖v‖) : ℝ≥0) : ℝ) := hderivBound
    _ = ((K : ℝ) * ‖v‖) * r := by
      rw [NNReal.coe_mul, Real.coe_toNNReal]
      · ring
      · positivity

/-- The intrinsic derivative of a boundary-distance function has norm at
most one at every interior differentiability point. -/
theorem norm_mfderiv_boundaryDistance_le_one
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (boundary : UnitAddCircle → M) (θ : UnitAddCircle)
    (x : M) (hx : I.IsInteriorPoint x)
    (hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (boundaryDistance boundary θ) x) :
    ‖mfderiv I 𝓘(ℝ, ℝ) (boundaryDistance boundary θ) x‖ ≤ 1 :=
  norm_mfderiv_real_le_of_lipschitzWith I
    (boundaryDistance_lipschitzWith boundary θ) x hx hdiff

/-- The intrinsic derivative of the odd distance profile has norm at most
one at every interior differentiability point. -/
theorem norm_mfderiv_oddDistanceProfile_le_one
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (boundary : UnitAddCircle → M) (θ : UnitAddCircle)
    (x : M) (hx : I.IsInteriorPoint x)
    (hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (oddDistanceProfile boundary θ) x) :
    ‖mfderiv I 𝓘(ℝ, ℝ) (oddDistanceProfile boundary θ) x‖ ≤ 1 :=
  norm_mfderiv_real_le_of_lipschitzWith I
    (oddDistanceProfile_lipschitzWith boundary θ) x hx hdiff

/-- The intrinsic derivative of the antipodal slack has norm at most one at
every interior differentiability point. -/
theorem norm_mfderiv_distanceSlack_le_one
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M]
    (boundary : UnitAddCircle → M) (θ : UnitAddCircle)
    (x : M) (hx : I.IsInteriorPoint x)
    (hdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (distanceSlack boundary θ) x) :
    ‖mfderiv I 𝓘(ℝ, ℝ) (distanceSlack boundary θ) x‖ ≤ 1 :=
  norm_mfderiv_real_le_of_lipschitzWith I
    (distanceSlack_lipschitzWith boundary θ) x hx hdiff

end

end GromovFilling

#print axioms GromovFilling.norm_mfderiv_real_le_of_lipschitzWith
#print axioms GromovFilling.norm_mfderiv_boundaryDistance_le_one
#print axioms GromovFilling.norm_mfderiv_oddDistanceProfile_le_one
#print axioms GromovFilling.norm_mfderiv_distanceSlack_le_one
