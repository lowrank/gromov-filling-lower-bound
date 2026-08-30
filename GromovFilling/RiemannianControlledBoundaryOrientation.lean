import GromovFilling.RiemannianControlledBoundaryPrimitive
import GromovFilling.RiemannianControlledBoundaryInteriorAtlas

/-!
# Orientation signs for controlled boundary charts

An oriented surface atlas may contain charts whose coordinate orientation is
positive or negative relative to the chosen tangent-plane orientation.  This
module records that geometric compatibility by one constant sign in each
controlled half-space chart.  Multiplying the chartwise weak-Stokes identity
by that sign replaces the signed chart Jacobian by the canonical Riemannian
area density.

The datum below does not assume a global Stokes theorem.  In particular, it
does not identify the signed imaginary-axis traces with a parametrization of
the oriented manifold boundary, and it does not assume cancellation of the
partition-of-unity primitive errors after integration.  Those are subsequent
globalization obligations.
-/

open Bundle Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace GromovFilling

noncomputable section

universe uM uι

local instance controlledBoundaryOrientationEuclideanFinrankTwo :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨by simp⟩

variable {M : Type uM} [PseudoEMetricSpace M]
  [ChartedSpace (EuclideanHalfSpace 2) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 2) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
    (fun x : M ↦ TangentSpace
      (modelWithCornersEuclideanHalfSpace 2) x)]
  [IsRiemannianManifold (modelWithCornersEuclideanHalfSpace 2) M]

/-- Orientation compatibility for one finite controlled boundary atlas.
Each inverse half-space chart is either positive or negative relative to the
chosen tangent-plane orientation, with a sign that is constant throughout
its interior coordinate domain. -/
structure ControlledBoundaryAtlasOrientation
    (P : FiniteControlledBoundaryChartPartition M) where
  tangentOrientation : RiemannianTangentPlaneOrientation
    (modelWithCornersEuclideanHalfSpace 2) M
  chartSign : P.ι → ℝ
  chartSign_eq_one_or_neg_one :
    ∀ i, chartSign i = 1 ∨ chartSign i = -1
  chartSign_mul_jacobian_eq_abs :
    ∀ i z,
      z ∈ halfSpaceComplexExtChartDomain (P.center i) ∩
          complexRightOpenHalfPlane →
        chartSign i *
            orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z =
          |orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z|

/-- Every chart-orientation sign squares to one. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_sq
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι) :
    O.chartSign i * O.chartSign i = 1 := by
  rcases O.chartSign_eq_one_or_neg_one i with hi | hi
  · rw [hi]
    norm_num
  · rw [hi]
    norm_num

/-- The real value of the Riemannian chart density is the absolute value of
the signed chart Jacobian. -/
theorem toReal_riemannianChartDensity_eq_abs_orientedRiemannianChartJacobian
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace N] [ChartedSpace H N]
    [RiemannianBundle (fun x : N ↦ TangentSpace I x)]
    [Fact (Module.finrank ℝ E = 2)]
    (o : RiemannianTangentPlaneOrientation I N)
    (F : ℂ → N) (z : ℂ) :
    (riemannianChartDensity I F z).toReal =
      |orientedRiemannianChartJacobian I o F z| := by
  have h := congrArg ENNReal.toReal
    (ofReal_abs_orientedRiemannianChartJacobian_eq_chartDensity
      I o F z)
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h.symm

/-- The chart-area form of a localized oriented symplectic density.  It is
extended by zero only outside the actual inverse-chart domain. -/
def controlledBoundaryChartAreaSymplecticDensity
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P)
    (i : P.ι) {ι : Type uι} [Fintype ι]
    (G : M → ι → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ halfSpaceComplexExtChartDomain (P.center i) then
      (riemannianChartDensity
          (modelWithCornersEuclideanHalfSpace 2)
          (halfSpaceComplexExtChart (P.center i)) z).toReal *
        (P.partition i (halfSpaceComplexExtChart (P.center i) z) *
          orientedFiniteComplexRiemannianSymplecticDensity
            (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation G
            (halfSpaceComplexExtChart (P.center i) z))
    else 0

/-- The chart-area form of the intrinsic partition-of-unity primitive error.
It is extended by zero only outside the actual inverse-chart domain. -/
def controlledBoundaryChartAreaPrimitiveErrorDensity
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P)
    (i : P.ι) {ι : Type uι} [Fintype ι]
    (G : M → ι → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ halfSpaceComplexExtChartDomain (P.center i) then
      (riemannianChartDensity
          (modelWithCornersEuclideanHalfSpace 2)
          (halfSpaceComplexExtChart (P.center i)) z).toReal *
        orientedFiniteComplexRiemannianPrimitiveErrorDensity
          (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
          (P.partition i) G
          (halfSpaceComplexExtChart (P.center i) z)
    else 0

/-- At a differentiability point, multiplying a genuine chart symplectic
density by its chart-orientation sign converts it to the canonical chart-area
density. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_symplecticDensity_eq_area_of_mdifferentiableAt
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hG : ∀ j : ι, MDifferentiableAt
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)
      (halfSpaceComplexExtChart (P.center i) z))
    (hzRight : z ∈ complexRightOpenHalfPlane) :
    O.chartSign i * controlledBoundaryChartSymplecticDensity P i G z =
      controlledBoundaryChartAreaSymplecticDensity P O i G z := by
  classical
  by_cases hzDomain :
      z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · have hfactor :
        finiteSymplecticFDerivDensity
            (G ∘ halfSpaceComplexExtChart (P.center i)) z =
          orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z *
            orientedFiniteComplexRiemannianSymplecticDensity
              (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation G
              (halfSpaceComplexExtChart (P.center i) z) :=
      finiteSymplecticFDerivDensity_comp_parametrization_eq_jacobian_mul
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation G
        (halfSpaceComplexExtChart (P.center i)) z
        (mdifferentiableAt_halfSpaceComplexExtChart
          (P.center i) ⟨hzDomain, hzRight⟩)
        hG
    have hsign := O.chartSign_mul_jacobian_eq_abs i z
      ⟨hzDomain, hzRight⟩
    have hdensity :=
      toReal_riemannianChartDensity_eq_abs_orientedRiemannianChartJacobian
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (halfSpaceComplexExtChart (P.center i)) z
    rw [controlledBoundaryChartSymplecticDensity,
      controlledBoundaryChartCutoff_eq_of_mem P i hzDomain, hfactor,
      controlledBoundaryChartAreaSymplecticDensity, if_pos hzDomain,
      hdensity]
    calc
      O.chartSign i *
          (P.partition i (halfSpaceComplexExtChart (P.center i) z) *
            (orientedRiemannianChartJacobian
                (modelWithCornersEuclideanHalfSpace 2)
                O.tangentOrientation
                (halfSpaceComplexExtChart (P.center i)) z *
              orientedFiniteComplexRiemannianSymplecticDensity
                (modelWithCornersEuclideanHalfSpace 2)
                O.tangentOrientation G
                (halfSpaceComplexExtChart (P.center i) z))) =
        (O.chartSign i *
            orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2)
              O.tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z) *
          (P.partition i (halfSpaceComplexExtChart (P.center i) z) *
            orientedFiniteComplexRiemannianSymplecticDensity
              (modelWithCornersEuclideanHalfSpace 2)
              O.tangentOrientation G
              (halfSpaceComplexExtChart (P.center i) z)) := by ring
      _ =
        |orientedRiemannianChartJacobian
            (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
            (halfSpaceComplexExtChart (P.center i)) z| *
          (P.partition i (halfSpaceComplexExtChart (P.center i) z) *
            orientedFiniteComplexRiemannianSymplecticDensity
              (modelWithCornersEuclideanHalfSpace 2)
              O.tangentOrientation G
              (halfSpaceComplexExtChart (P.center i) z)) := by
        rw [hsign]
  · rw [controlledBoundaryChartSymplecticDensity,
      controlledBoundaryChartCutoff_eq_zero_of_not_mem P i hzDomain,
      controlledBoundaryChartAreaSymplecticDensity, if_neg hzDomain]
    simp

/-- Everywhere manifold differentiability is a convenience wrapper around
the pointwise chart-sign identity. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_symplecticDensity_eq_area
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane) :
    O.chartSign i * controlledBoundaryChartSymplecticDensity P i G z =
      controlledBoundaryChartAreaSymplecticDensity P O i G z := by
  exact O.chartSign_mul_symplecticDensity_eq_area_of_mdifferentiableAt
    i G (fun j ↦ (hG j) _) hzRight

/-- The same sign converts the genuine chart primitive error to its canonical
chart-area form. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_primitiveErrorDensity_eq_area
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane) :
    O.chartSign i *
        controlledBoundaryChartPrimitiveErrorDensity
          P O.tangentOrientation i G z =
      controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z := by
  classical
  by_cases hzDomain :
      z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · have hsign := O.chartSign_mul_jacobian_eq_abs i z
      ⟨hzDomain, hzRight⟩
    have hdensity :=
      toReal_riemannianChartDensity_eq_abs_orientedRiemannianChartJacobian
        (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
        (halfSpaceComplexExtChart (P.center i)) z
    rw [controlledBoundaryChartPrimitiveErrorDensity,
      controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_pos hzDomain, if_pos hzDomain, hdensity]
    calc
      O.chartSign i *
          (orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z *
            orientedFiniteComplexRiemannianPrimitiveErrorDensity
              (modelWithCornersEuclideanHalfSpace 2)
              O.tangentOrientation (P.partition i) G
              (halfSpaceComplexExtChart (P.center i) z)) =
        (O.chartSign i *
            orientedRiemannianChartJacobian
              (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
              (halfSpaceComplexExtChart (P.center i)) z) *
          orientedFiniteComplexRiemannianPrimitiveErrorDensity
            (modelWithCornersEuclideanHalfSpace 2)
            O.tangentOrientation (P.partition i) G
            (halfSpaceComplexExtChart (P.center i) z) := by ring
      _ =
        |orientedRiemannianChartJacobian
            (modelWithCornersEuclideanHalfSpace 2) O.tangentOrientation
            (halfSpaceComplexExtChart (P.center i)) z| *
          orientedFiniteComplexRiemannianPrimitiveErrorDensity
            (modelWithCornersEuclideanHalfSpace 2)
            O.tangentOrientation (P.partition i) G
            (halfSpaceComplexExtChart (P.center i) z) := by
        rw [hsign]
  · rw [controlledBoundaryChartPrimitiveErrorDensity,
      controlledBoundaryChartAreaPrimitiveErrorDensity,
      if_neg hzDomain, if_neg hzDomain]
    simp

/-- Integral form of the chart-sign conversion for the localized
symplectic density. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_integral_symplecticDensity_eq_area
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) :
    O.chartSign i *
        (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartSymplecticDensity P i G z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards
      [ae_restrict_mem isOpen_complexRightOpenHalfPlane.measurableSet] with z hz
  exact O.chartSign_mul_symplecticDensity_eq_area i G hG hz

/-- The genuine weighted symplectic density vanishes in the open half-plane
outside the controlled interior domain containing the cutoff support. -/
theorem controlledBoundaryChartSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzDomain : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    controlledBoundaryChartSymplecticDensity P i G z = 0 := by
  rw [controlledBoundaryChartSymplecticDensity,
    controlledBoundaryChartCutoff_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
      P i hzRight hzDomain, zero_mul]

/-- The corresponding canonical chart-area density has the same support. -/
theorem controlledBoundaryChartAreaSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
    {ι : Type uι} [Fintype ι]
    (P : FiniteControlledBoundaryChartPartition M)
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) {z : ℂ}
    (hzRight : z ∈ complexRightOpenHalfPlane)
    (hzControlled : z ∉ chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)) :
    controlledBoundaryChartAreaSymplecticDensity P O i G z = 0 := by
  classical
  by_cases hzDomain : z ∈ halfSpaceComplexExtChartDomain (P.center i)
  · have hcutoff :=
      controlledBoundaryChartCutoff_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P i hzRight hzControlled
    have hpartition :
        P.partition i (halfSpaceComplexExtChart (P.center i) z) = 0 := by
      rw [controlledBoundaryChartCutoff_eq_of_mem P i hzDomain] at hcutoff
      exact hcutoff
    simp only [controlledBoundaryChartAreaSymplecticDensity,
      if_pos hzDomain, hpartition, zero_mul, mul_zero]
  · simp only [controlledBoundaryChartAreaSymplecticDensity,
      if_neg hzDomain]

/-- For a Lipschitz finite complex map, Rademacher on the controlled chart
domain supplies the chart-sign conversion almost everywhere. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_integral_symplecticDensity_eq_area_of_lipschitzWith
    [Nonempty M] [MeasurableSpace M] [BorelSpace M]
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) {CG : ℝ≥0} (hG : LipschitzWith CG G) :
    O.chartSign i *
        (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartSymplecticDensity P i G z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z := by
  let s : Set ℂ :=
    chosenControlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr (P.center i)
  have hsMeas : MeasurableSet s := by
    exact (isOpen_controlledInteriorComplexChartDomain
      (modelWithCornersEuclideanHalfSpace 2)
      Complex.orthonormalBasisOneI.repr
      (chosenInteriorChartControl
        (modelWithCornersEuclideanHalfSpace 2) (P.center i))).measurableSet
  have hGdiff : ∀ᵐ z ∂volume.restrict s, ∀ j : ι,
      MDifferentiableAt
        (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
        (fun x ↦ G x j)
        (halfSpaceComplexExtChart (P.center i) z) := by
    simpa only [s] using
      (P.ae_mdifferentiableAt_comp_halfSpace_of_lipschitzWith
        (Classical.choice inferInstance) G hG i)
  rw [← integral_const_mul]
  apply integral_congr_ae
  rw [Filter.EventuallyEq,
    ae_restrict_iff' (μ := volume)
      isOpen_complexRightOpenHalfPlane.measurableSet]
  rw [ae_restrict_iff' (μ := volume) hsMeas] at hGdiff
  filter_upwards [hGdiff] with z hGz hzRight
  by_cases hz : z ∈ s
  · exact O.chartSign_mul_symplecticDensity_eq_area_of_mdifferentiableAt
      i G (hGz hz) hzRight
  · rw [controlledBoundaryChartSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P i G hzRight (by simpa only [s] using hz),
      controlledBoundaryChartAreaSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
        P O i G hzRight (by simpa only [s] using hz),
      mul_zero]

/-- Integral form of the chart-sign conversion for the primitive error. -/
theorem ControlledBoundaryAtlasOrientation.chartSign_mul_integral_primitiveErrorDensity_eq_area
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M}
    (O : ControlledBoundaryAtlasOrientation P) (i : P.ι)
    (G : M → ι → ℂ) :
    O.chartSign i *
        (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartPrimitiveErrorDensity
            P O.tangentOrientation i G z) =
      ∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards
      [ae_restrict_mem isOpen_complexRightOpenHalfPlane.measurableSet] with z hz
  exact O.chartSign_mul_primitiveErrorDensity_eq_area i G hz

/-- Sign-weighted genuine chart-local weak Stokes.  The two interior terms
now use the canonical Riemannian chart-area density; the remaining signed
imaginary-axis action is exactly the datum that must be glued to the induced
orientation of the manifold boundary. -/
theorem ControlledBoundaryChartWeakStokesData.integral_areaSymplecticDensity_eq_areaPrimitiveError_sub_signedBoundary
    {ι : Type uι} [Fintype ι]
    {P : FiniteControlledBoundaryChartPartition M} {i : P.ι}
    {G : M → ι → ℂ}
    (D : ControlledBoundaryChartWeakStokesData P i G)
    (O : ControlledBoundaryAtlasOrientation P)
    (hG : ∀ j : ι, MDifferentiable
      (modelWithCornersEuclideanHalfSpace 2) 𝓘(ℝ, ℂ)
      (fun x ↦ G x j)) :
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
      (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
  calc
    (∫ z in complexRightOpenHalfPlane,
        controlledBoundaryChartAreaSymplecticDensity P O i G z) =
        O.chartSign i *
          (∫ z in complexRightOpenHalfPlane,
            controlledBoundaryChartSymplecticDensity P i G z) :=
      (O.chartSign_mul_integral_symplecticDensity_eq_area i G hG).symm
    _ = O.chartSign i *
        ((∫ z in complexRightOpenHalfPlane,
            controlledBoundaryChartPrimitiveErrorDensity
              P O.tangentOrientation i G z) -
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y) := by
      rw [D.integral_controlledBoundaryChartSymplecticDensity_eq_chartPrimitiveError
        O.tangentOrientation hG]
    _ = O.chartSign i *
          (∫ z in complexRightOpenHalfPlane,
            controlledBoundaryChartPrimitiveErrorDensity
              P O.tangentOrientation i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      ring
    _ = (∫ z in complexRightOpenHalfPlane,
          controlledBoundaryChartAreaPrimitiveErrorDensity P O i G z) -
        O.chartSign i *
          ∫ y : ℝ, controlledBoundaryChartActionDensity P i G y := by
      rw [O.chartSign_mul_integral_primitiveErrorDensity_eq_area i G]

#print axioms ControlledBoundaryAtlasOrientation.chartSign_sq
#print axioms
  toReal_riemannianChartDensity_eq_abs_orientedRiemannianChartJacobian
#print axioms controlledBoundaryChartAreaSymplecticDensity
#print axioms controlledBoundaryChartAreaPrimitiveErrorDensity
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_symplecticDensity_eq_area_of_mdifferentiableAt
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_symplecticDensity_eq_area
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_primitiveErrorDensity_eq_area
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_integral_symplecticDensity_eq_area
#print axioms
  controlledBoundaryChartSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  controlledBoundaryChartAreaSymplecticDensity_eq_zero_of_mem_rightOpen_of_not_mem_chosenInteriorDomain
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_integral_symplecticDensity_eq_area_of_lipschitzWith
#print axioms
  ControlledBoundaryAtlasOrientation.chartSign_mul_integral_primitiveErrorDensity_eq_area
#print axioms
  ControlledBoundaryChartWeakStokesData.integral_areaSymplecticDensity_eq_areaPrimitiveError_sub_signedBoundary

end

end GromovFilling
