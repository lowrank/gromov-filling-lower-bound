import GromovFilling.RiemannianControlledBoundaryParameterLipschitz

/-!
# Boundary parameters on controlled chart-axis domains

The cutoff-nonzero locus is enough for pointwise trace identities, but its
endpoints need not themselves have nonzero cutoff.  For change of variables
we instead lift the canonical boundary parameter on any whole axis interval
contained in the quantitative controlled chart domain.  This keeps the
annular margin around the cutoff support available without imposing false
endpoint regularity.
-/

open Bundle Function Manifold Metric Set
open scoped Bundle Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM

local instance controlledBoundaryAxisDomainEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoMetricSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) (⊤ : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Every controlled imaginary-axis coordinate maps back from its canonical
circle parameter, whether or not the partition cutoff is nonzero there. -/
theorem boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyDomain : (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    boundary (controlledBoundaryChartParameter boundary P i y) =
      halfSpaceComplexExtChart (P.center i) (y * Complex.I) := by
  unfold controlledBoundaryChartParameter
  apply Function.invFun_eq
  rw [← Set.mem_range, hboundaryRange]
  exact halfSpaceComplexExtChart_real_mul_I_mem_boundary
    (P.center i) y
    (controlledHalfSpaceComplexChartDomain_subset_domain
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) (P.center i)) hyDomain)

/-- Throughout a controlled axis domain, the coordinate cutoff is exactly
the manifold partition pulled back by the canonical circle parameter. -/
theorem controlledBoundaryChartCutoff_eq_boundary_partition_parameter_of_mem_controlledDomain
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι) (y : ℝ)
    (hyDomain : (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    controlledBoundaryChartCutoff P i (y * Complex.I) =
      P.partition i
        (boundary (controlledBoundaryChartParameter boundary P i y)) := by
  rw [controlledBoundaryChartCutoff_eq_of_mem P i
      (controlledHalfSpaceComplexChartDomain_subset_domain
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) (P.center i)) hyDomain),
    boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i y hyDomain]

/-- On any real set whose imaginary-axis coordinates remain in the
controlled chart domain, the canonical circle parameter is continuous. -/
theorem continuousOn_controlledBoundaryChartParameter_of_mem_controlledDomain
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (s : Set ℝ)
    (hdomain : ∀ y ∈ s, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    ContinuousOn (controlledBoundaryChartParameter boundary P i) s := by
  have hboundaryEmbedding : Topology.IsClosedEmbedding boundary :=
    hboundary.lipschitzWith.continuous.isClosedEmbedding hboundary.injective
  apply hboundaryEmbedding.isInducing.continuousOn_iff.mpr
  have haxis : ContinuousOn
      (fun y : ℝ ↦ halfSpaceComplexExtChart (P.center i)
        (y * Complex.I)) s := by
    apply (continuousOn_halfSpaceComplexExtChart (P.center i)).comp
      (show Continuous (fun y : ℝ ↦ (y * Complex.I : ℂ)) by
        fun_prop).continuousOn
    intro y hy
    exact controlledHalfSpaceComplexChartDomain_subset_domain
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) (P.center i))
      (hdomain y hy)
  apply haxis.congr
  intro y hy
  exact boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
    boundary hboundaryRange P i y (hdomain y hy)

/-- The canonical circle parameter is injective on every controlled
imaginary-axis set. -/
theorem injOn_controlledBoundaryChartParameter_of_mem_controlledDomain
    (boundary : UnitAddCircle → M)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (s : Set ℝ)
    (hdomain : ∀ y ∈ s, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    Set.InjOn (controlledBoundaryChartParameter boundary P i) s := by
  intro y hy z hz hyz
  have hyDomain := hdomain y hy
  have hzDomain := hdomain z hz
  have haxis :
      halfSpaceComplexExtChart (P.center i) (y * Complex.I) =
        halfSpaceComplexExtChart (P.center i) (z * Complex.I) := by
    calc
      halfSpaceComplexExtChart (P.center i) (y * Complex.I) =
          boundary (controlledBoundaryChartParameter boundary P i y) :=
        (boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
          boundary hboundaryRange P i y hyDomain).symm
      _ = boundary (controlledBoundaryChartParameter boundary P i z) :=
        congrArg boundary hyz
      _ = halfSpaceComplexExtChart (P.center i) (z * Complex.I) :=
        boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
          boundary hboundaryRange P i z hzDomain
  have hcoord : (y * Complex.I : ℂ) = z * Complex.I :=
    injOn_halfSpaceComplexExtChart (P.center i)
      (controlledHalfSpaceComplexChartDomain_subset_domain
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) (P.center i)) hyDomain)
      (controlledHalfSpaceComplexChartDomain_subset_domain
        (chosenInteriorChartControl
          (modelWithCornersEuclideanHalfSpace 2) (P.center i)) hzDomain)
      haxis
  have him := congrArg Complex.im hcoord
  simpa only [Complex.mul_I_im, Complex.ofReal_re] using him

/-- The canonical circle parameter is quantitatively Lipschitz on every
controlled imaginary-axis set. -/
theorem exists_lipschitzOnWith_controlledBoundaryChartParameter_of_mem_controlledDomain
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (s : Set ℝ)
    (hdomain : ∀ y ∈ s, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (controlledBoundaryChartParameter boundary P i) s := by
  let c := chosenInteriorChartControl
    (modelWithCornersEuclideanHalfSpace 2) (P.center i)
  let K : ℝ := (c.C : ℝ) / (2 * Real.pi)
  refine ⟨Real.toNNReal K, LipschitzOnWith.of_dist_le' ?_⟩
  intro y hy z hz
  have hyDomain := hdomain y hy
  have hzDomain := hdomain z hz
  have hchartBound :
      dist
          (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
          (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) ≤
        (c.C : ℝ) * dist (y * Complex.I : ℂ) (z * Complex.I) :=
    (lipschitzOnWith_controlledHalfSpaceComplexChart c).dist_le_mul
      (y * Complex.I) (by simpa only [c,
        chosenControlledHalfSpaceComplexChartDomain] using hyDomain)
      (z * Complex.I) (by simpa only [c,
        chosenControlledHalfSpaceComplexChartDomain] using hzDomain)
  have hmetric := hboundary
    (controlledBoundaryChartParameter boundary P i y)
    (controlledBoundaryChartParameter boundary P i z)
  rw [boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i y hyDomain,
    boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i z hzDomain] at hmetric
  have hpi : 0 < (2 * Real.pi : ℝ) :=
    mul_pos (by norm_num) Real.pi_pos
  have hparameterEq :
      dist (controlledBoundaryChartParameter boundary P i y)
          (controlledBoundaryChartParameter boundary P i z) =
        dist
            (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
            (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) /
          (2 * Real.pi) := by
    apply (eq_div_iff hpi.ne').2
    calc
      dist (controlledBoundaryChartParameter boundary P i y)
            (controlledBoundaryChartParameter boundary P i z) *
          (2 * Real.pi) =
          (2 * Real.pi) *
            dist (controlledBoundaryChartParameter boundary P i y)
              (controlledBoundaryChartParameter boundary P i z) := by ring
      _ = dist
          (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
          (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) :=
        hmetric.symm
  have haxisDist :
      dist (y * Complex.I : ℂ) (z * Complex.I) = dist y z := by
    rw [Complex.dist_of_re_eq (by simp)]
    simp only [Complex.mul_I_im, Complex.ofReal_re]
  calc
    dist (controlledBoundaryChartParameter boundary P i y)
        (controlledBoundaryChartParameter boundary P i z) =
        dist
            (halfSpaceComplexExtChart (P.center i) (y * Complex.I))
            (halfSpaceComplexExtChart (P.center i) (z * Complex.I)) /
          (2 * Real.pi) := hparameterEq
    _ ≤ ((c.C : ℝ) * dist (y * Complex.I : ℂ) (z * Complex.I)) /
          (2 * Real.pi) :=
      div_le_div_of_nonneg_right hchartBound hpi.le
    _ = K * dist y z := by
      rw [haxisDist]
      dsimp only [K]
      ring

/-- A continuous lift of a Lipschitz circle map is locally Lipschitz wherever
the lift projects to that map. -/
private theorem locallyLipschitzOn_real_lift_of_lipschitzOnWith_projection_axisDomain
    {s : Set ℝ} {parameter : ℝ → UnitAddCircle} {lift : ℝ → ℝ}
    {K : ℝ≥0}
    (hliftContinuous : Continuous lift)
    (hliftProject : ∀ y ∈ s, ((lift y : ℝ) : UnitAddCircle) = parameter y)
    (hparameter : LipschitzOnWith K parameter s) :
    LocallyLipschitzOn s lift := by
  intro x hx
  have hquarter : 0 < (1 / 4 : ℝ) := by norm_num
  let t : Set ℝ :=
    s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ)
  refine ⟨K, t, ?_, ?_⟩
  · exact inter_mem_nhdsWithin s
      (hliftContinuous.continuousAt
        (Metric.ball_mem_nhds (lift x) hquarter))
  · apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    change y ∈ s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ) at hy
    change z ∈ s ∩ lift ⁻¹' Metric.ball (lift x) (1 / 4 : ℝ) at hz
    have hyDist : dist (lift y) (lift x) < (1 / 4 : ℝ) :=
      Metric.mem_ball.mp hy.2
    have hzDist : dist (lift z) (lift x) < (1 / 4 : ℝ) :=
      Metric.mem_ball.mp hz.2
    have hyzDist : dist (lift y) (lift z) < (1 / 2 : ℝ) := by
      calc
        dist (lift y) (lift z) ≤
            dist (lift y) (lift x) + dist (lift x) (lift z) :=
          dist_triangle _ _ _
        _ < (1 / 4 : ℝ) + 1 / 4 := by
          apply add_lt_add hyDist
          simpa only [dist_comm] using hzDist
        _ = 1 / 2 := by norm_num
    have hhalf : |lift y - lift z| ≤ (1 / 2 : ℝ) := by
      rw [← Real.dist_eq]
      exact hyzDist.le
    calc
      dist (lift y) (lift z) = |lift y - lift z| := Real.dist_eq _ _
      _ = ‖((lift y - lift z : ℝ) : UnitAddCircle)‖ :=
        ((AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2
          (by simpa only [abs_one] using hhalf)).symm
      _ = dist (((lift y : ℝ) : UnitAddCircle))
          (((lift z : ℝ) : UnitAddCircle)) := by
        rw [dist_eq_norm, ← AddCircle.coe_sub]
      _ = dist (parameter y) (parameter z) := by
        rw [hliftProject y hy.1, hliftProject z hz.1]
      _ ≤ (K : ℝ) * dist y z :=
        hparameter.dist_le_mul y hy.1 z hz.1

/-- Every compact imaginary-axis interval contained in a controlled chart
domain has a globally Lipschitz, absolutely continuous real lift of its
canonical circle parameter. -/
theorem exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_of_mem_controlledDomain_on_Icc
    (boundary : UnitAddCircle → M)
    (hboundary : IsometricCircleBoundary boundary)
    (hboundaryRange : Set.range boundary =
      (modelWithCornersEuclideanHalfSpace 2).boundary M)
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (a b : ℝ) (hab : a ≤ b)
    (hdomain : ∀ y ∈ Set.Icc a b, (y * Complex.I : ℂ) ∈
      chosenControlledHalfSpaceComplexChartDomain (P.center i)) :
    ∃ C : ℝ≥0, ∃ lift : ℝ → ℝ,
      Continuous lift ∧
      LipschitzOnWith C lift (Set.Icc a b) ∧
      AbsolutelyContinuousOnInterval lift a b ∧
      (∀ y ∈ Set.Icc a b,
        ((lift y : ℝ) : UnitAddCircle) =
          controlledBoundaryChartParameter boundary P i y) ∧
      (StrictMonoOn lift (Set.Icc a b) ∨
        StrictAntiOn lift (Set.Icc a b)) := by
  have hparameterContinuousOn :=
    continuousOn_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundary hboundaryRange P i (Set.Icc a b) hdomain
  let parameterIcc : C(Set.Icc a b, UnitAddCircle) :=
    ⟨fun y ↦ controlledBoundaryChartParameter boundary P i y,
      hparameterContinuousOn.restrict⟩
  let base : C(ℝ, UnitAddCircle) :=
    ⟨Set.IccExtend hab parameterIcc,
      parameterIcc.continuous.Icc_extend'⟩
  let cov : IsCoveringMap ((↑) : ℝ → UnitAddCircle) :=
    AddCircle.isCoveringMap_coe (p := (1 : ℝ))
  obtain ⟨r, _hr, hr⟩ := AddCircle.eq_coe_Ico (base 0)
  have hbase : ((r : ℝ) : UnitAddCircle) = base 0 := by
    simpa [base] using hr
  obtain ⟨lift, hlift, _hunique⟩ :=
    cov.existsUnique_continuousMap_lifts base 0 r hbase
  have hliftProject : ∀ y ∈ Set.Icc a b,
      ((lift y : ℝ) : UnitAddCircle) =
        controlledBoundaryChartParameter boundary P i y := by
    intro y hy
    have hproject := congrFun hlift.2 y
    calc
      ((lift y : ℝ) : UnitAddCircle) = base y := by
        simpa [base] using hproject
      _ = controlledBoundaryChartParameter boundary P i y := by
        change Set.IccExtend hab parameterIcc y =
          controlledBoundaryChartParameter boundary P i y
        rw [Set.IccExtend_of_mem hab parameterIcc hy]
        rfl
  obtain ⟨Kparameter, hparameter⟩ :=
    exists_lipschitzOnWith_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundary hboundaryRange P i (Set.Icc a b) hdomain
  have hliftLocallyLipschitz : LocallyLipschitzOn (Set.Icc a b) lift :=
    locallyLipschitzOn_real_lift_of_lipschitzOnWith_projection_axisDomain
      lift.continuous hliftProject hparameter
  obtain ⟨Klift, hliftLipschitz⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc hliftLocallyLipschitz
  have hliftAbsolutelyContinuous :
      AbsolutelyContinuousOnInterval lift a b := by
    have hliftLipschitzUIcc :
        LipschitzOnWith Klift lift (Set.uIcc a b) := by
      simpa only [Set.uIcc_of_le hab] using hliftLipschitz
    exact hliftLipschitzUIcc.absolutelyContinuousOnInterval
  have hparameterInjective : Set.InjOn
      (controlledBoundaryChartParameter boundary P i) (Set.Icc a b) :=
    injOn_controlledBoundaryChartParameter_of_mem_controlledDomain
      boundary hboundaryRange P i (Set.Icc a b) hdomain
  have hliftInjective : Set.InjOn lift (Set.Icc a b) := by
    intro y hy z hz hyz
    apply hparameterInjective hy hz
    calc
      controlledBoundaryChartParameter boundary P i y =
          ((lift y : ℝ) : UnitAddCircle) := (hliftProject y hy).symm
      _ = ((lift z : ℝ) : UnitAddCircle) :=
        congrArg (fun q : ℝ ↦ (q : UnitAddCircle)) hyz
      _ = controlledBoundaryChartParameter boundary P i z :=
        hliftProject z hz
  refine ⟨Klift, lift, lift.continuous, hliftLipschitz,
    hliftAbsolutelyContinuous, hliftProject, ?_⟩
  exact lift.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
    hab hliftInjective

#print axioms
  boundary_controlledBoundaryChartParameter_of_mem_controlledDomain
#print axioms
  controlledBoundaryChartCutoff_eq_boundary_partition_parameter_of_mem_controlledDomain
#print axioms
  continuousOn_controlledBoundaryChartParameter_of_mem_controlledDomain
#print axioms
  injOn_controlledBoundaryChartParameter_of_mem_controlledDomain
#print axioms
  exists_lipschitzOnWith_controlledBoundaryChartParameter_of_mem_controlledDomain
#print axioms
  exists_lipschitzOnWith_real_lift_controlledBoundaryChartParameter_of_mem_controlledDomain_on_Icc

end

end GromovFilling
