import GromovFilling.RiemannianHalfSpaceChartTransitionAxis
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Local monotonicity of half-space chart transitions on the boundary axis

On a short boundary-axis interval inside an extended-chart transition source,
the tangential coordinate transition is continuous and injective.  It is
therefore strictly monotone or strictly antitone, and its derivative at the
center is the tangential component of the ambient transition derivative.
-/

open Manifold Set
open scoped Manifold Topology

namespace GromovFilling

noncomputable section

/-- On a sufficiently short boundary-axis interval, the tangential component
of an extended half-space chart transition is strictly monotone or strictly
antitone.  Its derivative at the center is the tangential component of the
ambient transition derivative. -/
theorem exists_axis_interval_strictMonoOn_or_strictAntiOn_with_deriv
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0) :
    ∃ r : ℝ, 0 < r ∧
      (StrictMonoOn
        (fun t : ℝ ↦
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
            (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
        (Set.Icc (-r) r) ∨
      StrictAntiOn
        (fun t : ℝ ↦
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
            (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
        (Set.Icc (-r) r)) ∧
      derivWithin
        (fun t : ℝ ↦
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
            (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
        (Set.Icc (-r) r) 0 =
        (fderivWithin ℝ
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
          (EuclideanSpace.single 1 (1 : ℝ))) 1 := by
  let I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanHalfSpace 2) := modelWithCornersEuclideanHalfSpace 2
  let φ : PartialEquiv (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2)) :=
    (extChartAt I a).symm ≫ extChartAt I b
  let s : Set (EuclideanSpace ℝ (Fin 2)) := φ.source
  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    extChartAt I b ∘ (extChartAt I a).symm
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fderivWithin ℝ T s z
  let e1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1 : ℝ)
  change z ∈ s at hz
  change ∃ r : ℝ, 0 < r ∧
    (StrictMonoOn (fun t : ℝ ↦ (T (z + t • e1)) 1) (Set.Icc (-r) r) ∨
      StrictAntiOn (fun t : ℝ ↦ (T (z + t • e1)) 1) (Set.Icc (-r) r)) ∧
    derivWithin (fun t : ℝ ↦ (T (z + t • e1)) 1) (Set.Icc (-r) r) 0 =
      (D e1) 1
  obtain ⟨r, hr, hinterval⟩ :=
    exists_axis_interval_subset_extChartAt_transition_source a b hz hzAxis
  let J : Set ℝ := Set.Icc (-r) r
  let η : ℝ → EuclideanSpace ℝ (Fin 2) := fun t ↦ z + t • e1
  let g : ℝ → ℝ := fun t ↦ (T (η t)) 1
  have hηmaps : Set.MapsTo η J s := by
    intro t ht
    exact (hinterval t (by simpa only [J] using ht)).1
  have haxis : ∀ t ∈ J, (T (η t)) 0 = 0 := by
    intro t ht
    exact (hinterval t (by simpa only [J] using ht)).2
  have hηcont : Continuous η := by
    simpa only [η] using
      continuous_const.add (continuous_id.smul continuous_const)
  have hTcont : ContinuousOn T s := by
    simpa only [I, T, s, φ, Function.comp_def] using
      (contDiffOn_ext_coord_change b a).continuousOn
  let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hgcont : ContinuousOn g J := by
    simpa only [g, p, Function.comp_def] using
      p.continuous.continuousOn.comp
        (hTcont.comp hηcont.continuousOn hηmaps)
        (by intro t ht; simp)
  have hTinj : Set.InjOn T s := by
    simpa only [T, s, φ, Function.comp_def] using φ.injOn
  have hginj : Set.InjOn g J := by
    intro x hx y hy hxy
    have hTxy : T (η x) = T (η y) := by
      apply PiLp.ext
      rw [Fin.forall_fin_two]
      exact ⟨(haxis x hx).trans (haxis y hy).symm,
        by simpa only [g] using hxy⟩
    have hηxy : η x = η y :=
      hTinj (hηmaps hx) (hηmaps hy) hTxy
    have hcoord := congrArg
      (fun q : EuclideanSpace ℝ (Fin 2) ↦ q (1 : Fin 2)) hηxy
    have hscalar : z 1 + x = z 1 + y := by
      simpa [η, e1, PiLp.add_apply, PiLp.smul_apply] using hcoord
    linarith
  have hdir : StrictMonoOn g J ∨ StrictAntiOn g J :=
    hgcont.strictMonoOn_of_injOn_Icc'
      (by dsimp only [J]; linarith) hginj
  have hTderiv : HasFDerivWithinAt T D s z := by
    simpa only [I, T, s, φ, Function.comp_apply] using
      ((contDiffOn_ext_coord_change b a z hz).differentiableWithinAt
        one_ne_zero).hasFDerivWithinAt
  have hη : HasDerivWithinAt η e1 J 0 := by
    simpa only [η, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const e1).const_add z).hasDerivWithinAt
  have hvec : HasDerivWithinAt (T ∘ η) (D e1) J 0 :=
    hTderiv.comp_hasDerivWithinAt_of_eq 0 hη hηmaps (by simp [η])
  have hgderiv : HasDerivWithinAt g ((D e1) 1) J 0 := by
    simpa [g, p, Function.comp_apply] using
      p.hasFDerivAt.comp_hasDerivWithinAt 0 hvec
  have hUD : UniqueDiffWithinAt ℝ J 0 := by
    simpa only [J] using
      (uniqueDiffOn_Icc (by linarith : -r < r)) 0
        (by constructor <;> linarith)
  have hderiv : derivWithin g J 0 = (D e1) 1 :=
    hgderiv.derivWithin hUD
  exact ⟨r, hr, by simpa only [g, J, η] using hdir,
    by simpa only [g, J, η] using hderiv⟩

/-- A positive tangential transition derivative selects the strictly
increasing alternative on a short boundary-axis interval. -/
theorem exists_axis_interval_strictMonoOn_of_tangent_pos
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (hpos :
      0 < (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1) :
    ∃ r : ℝ, 0 < r ∧ StrictMonoOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  obtain ⟨r, hr, hdir, hderiv⟩ :=
    exists_axis_interval_strictMonoOn_or_strictAntiOn_with_deriv a b hz hzAxis
  rcases hdir with hmono | hanti
  · exact ⟨r, hr, hmono⟩
  · exfalso
    have hnonpos :
        (fderivWithin ℝ
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
          (EuclideanSpace.single 1 (1 : ℝ))) 1 ≤ 0 := by
      rw [← hderiv]
      exact hanti.antitoneOn.derivWithin_nonpos
    exact (not_le_of_gt hpos) hnonpos

/-- A negative tangential transition derivative selects the strictly
decreasing alternative on a short boundary-axis interval. -/
theorem exists_axis_interval_strictAntiOn_of_tangent_neg
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace 2) 1 M]
    (a b : M) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
      extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source)
    (hzAxis : z 0 = 0)
    (hneg :
      (fderivWithin ℝ
        (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
          extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
        (EuclideanSpace.single 1 (1 : ℝ))) 1 < 0) :
    ∃ r : ℝ, 0 < r ∧ StrictAntiOn
      (fun t : ℝ ↦
        ((extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          (z + t • EuclideanSpace.single 1 (1 : ℝ))) 1)
      (Set.Icc (-r) r) := by
  obtain ⟨r, hr, hdir, hderiv⟩ :=
    exists_axis_interval_strictMonoOn_or_strictAntiOn_with_deriv a b hz hzAxis
  rcases hdir with hmono | hanti
  · exfalso
    have hnonneg :
        0 ≤ (fderivWithin ℝ
          (extChartAt (modelWithCornersEuclideanHalfSpace 2) b ∘
            (extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm)
          ((extChartAt (modelWithCornersEuclideanHalfSpace 2) a).symm ≫
            extChartAt (modelWithCornersEuclideanHalfSpace 2) b).source z
          (EuclideanSpace.single 1 (1 : ℝ))) 1 := by
      rw [← hderiv]
      exact hmono.monotoneOn.derivWithin_nonneg
    exact (not_le_of_gt hneg) hnonneg
  · exact ⟨r, hr, hanti⟩

#print axioms exists_axis_interval_strictMonoOn_or_strictAntiOn_with_deriv
#print axioms exists_axis_interval_strictMonoOn_of_tangent_pos
#print axioms exists_axis_interval_strictAntiOn_of_tangent_neg

end

end GromovFilling
