import GromovFilling.RiemannianInteriorAtlasArea

/-!
# Locality of canonical Riemannian surface area

The canonical surface-area measure is assembled from disjointified controlled
chart pieces.  This file proves the complementary local statement: on the
image of any one controlled chart, the canonical measure is exactly the full
Jacobian-weighted measure of that chart.  Thus intrinsic integrands supported
in one controlled chart may be transferred between planar and canonical
surface integration without retaining the auxiliary disjointification.
-/

open Bundle MeasureTheory Set
open scoped Bundle ENNReal Manifold

namespace GromovFilling

noncomputable section

namespace ControlledInteriorAtlas

/-- A controlled-atlas area measure is supported on the manifold interior. -/
theorem areaMeasure_restrict_interior
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) :
    (A.areaMeasure I).restrict (I.interior M) = A.areaMeasure I := by
  change (Measure.sum fun i ↦
    riemannianChartAreaMeasure I (A.parametrization i)
      (A.piece I i)).restrict (I.interior M) = _
  rw [Measure.restrict_sum _
    (I.isOpen_interior one_ne_zero).measurableSet]
  apply congrArg Measure.sum
  funext i
  exact restrict_riemannianChartAreaMeasure_of_image_subset
    I (A.parametrization i) (A.piece I i)
      (A.measurableSet_piece I i)
      (I.interior M) (I.isOpen_interior one_ne_zero).measurableSet
      (((A.continuousOn_parametrization i).mono
        (A.piece_subset_domain I i)).aemeasurable
          (A.measurableSet_piece I i))
      ((image_mono (A.piece_subset_domain I i)).trans
        (A.image_subset_interior i))

/-- Restricting an arbitrary measurable subpiece of one controlled chart to
an arbitrary measurable subpiece of a second chart can be computed on the
open coordinate overlap. -/
theorem restrict_chartAreaMeasure_subset_eq_restrict_overlap
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A B : ControlledInteriorAtlas I M) (i j : ℕ)
    (s t : Set ℂ) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsDomain : s ⊆ A.domain i) (htDomain : t ⊆ B.domain j) :
    (riemannianChartAreaMeasure I (A.parametrization i) s).restrict
        (B.parametrization j '' t) =
      (riemannianChartAreaMeasure I (A.parametrization i)
        (A.overlapDomain I B i j)).restrict
          (A.parametrization i '' s ∩ B.parametrization j '' t) := by
  have hAimage : MeasurableSet (A.parametrization i '' s) :=
    hs.image_of_continuousOn_injOn
      ((A.continuousOn_parametrization i).mono hsDomain)
      ((A.injOn_parametrization i).mono hsDomain)
  have hBimage : MeasurableSet (B.parametrization j '' t) :=
    ht.image_of_continuousOn_injOn
      ((B.continuousOn_parametrization j).mono htDomain)
      ((B.injOn_parametrization j).mono htDomain)
  have hpair : MeasurableSet
      (A.parametrization i '' s ∩ B.parametrization j '' t) :=
    hAimage.inter hBimage
  have hoverlap : MeasurableSet (A.overlapDomain I B i j) :=
    (A.isOpen_overlapDomain I B i j).measurableSet
  have hFs : AEMeasurable (A.parametrization i) (volume.restrict s) :=
    ((A.continuousOn_parametrization i).mono hsDomain).aemeasurable hs
  have hFoverlap : AEMeasurable (A.parametrization i)
      (volume.restrict (A.overlapDomain I B i j)) :=
    ((A.continuousOn_parametrization i).mono
      (A.overlapDomain_subset_domain I B i j)).aemeasurable hoverlap
  have hcoord :
      s ∩ A.parametrization i ⁻¹' (B.parametrization j '' t) =
        A.overlapDomain I B i j ∩
          A.parametrization i ⁻¹'
            (A.parametrization i '' s ∩ B.parametrization j '' t) := by
    ext z
    constructor
    · rintro ⟨hzS, hzB⟩
      refine ⟨⟨hsDomain hzS, ?_⟩, ?_⟩
      · exact image_mono htDomain hzB
      · exact ⟨⟨z, hzS, rfl⟩, hzB⟩
    · rintro ⟨hzOverlap, hzA, hzB⟩
      rcases hzA with ⟨w, hwS, hwz⟩
      have hzw : z = w := A.injOn_parametrization i hzOverlap.1
        (hsDomain hwS) hwz.symm
      exact ⟨hzw ▸ hwS, hzB⟩
  rw [restrict_riemannianChartAreaMeasure I (A.parametrization i)
      s hs (B.parametrization j '' t) hBimage hFs,
    restrict_riemannianChartAreaMeasure I (A.parametrization i)
      (A.overlapDomain I B i j) hoverlap
      (A.parametrization i '' s ∩ B.parametrization j '' t)
      hpair hFoverlap,
    hcoord]

/-- The disjointified area measure of a controlled atlas, restricted to one
full chart image, is the full Jacobian-weighted measure of that chart. -/
theorem areaMeasure_restrict_chart_image
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    (A : ControlledInteriorAtlas I M) (i : ℕ) :
    (A.areaMeasure I).restrict
        (A.parametrization i '' A.domain i) =
      riemannianChartAreaMeasure I (A.parametrization i) (A.domain i) := by
  let U : Set M := A.parametrization i '' A.domain i
  let μ : Measure M :=
    riemannianChartAreaMeasure I (A.parametrization i) (A.domain i)
  have hdomain : MeasurableSet (A.domain i) :=
    (A.isOpen_domain i).measurableSet
  have hU : MeasurableSet U := by
    exact hdomain.image_of_continuousOn_injOn
      (A.continuousOn_parametrization i)
      (A.injOn_parametrization i)
  have hpair : ∀ j : ℕ,
      (riemannianChartAreaMeasure I (A.parametrization j)
          (A.piece I j)).restrict U =
        μ.restrict (A.imagePiece I j) := by
    intro j
    have hpiece : MeasurableSet (A.piece I j) :=
      A.measurableSet_piece I j
    calc
      (riemannianChartAreaMeasure I (A.parametrization j)
          (A.piece I j)).restrict U =
          (riemannianChartAreaMeasure I (A.parametrization j)
            (A.overlapDomain I A j i)).restrict
              (A.imagePiece I j ∩ U) := by
        simpa only [U, imagePiece] using
          A.restrict_chartAreaMeasure_subset_eq_restrict_overlap
            I A j i (A.piece I j) (A.domain i)
            hpiece hdomain (A.piece_subset_domain I j) (Subset.rfl)
      _ = (riemannianChartAreaMeasure I (A.parametrization i)
            (A.overlapDomain I A i j)).restrict
              (U ∩ A.imagePiece I j) := by
        rw [← A.riemannianChartAreaMeasure_overlap I A i j, inter_comm]
      _ = μ.restrict (A.imagePiece I j) := by
        simpa only [U, μ, imagePiece] using
          (A.restrict_chartAreaMeasure_subset_eq_restrict_overlap
            I A i j (A.domain i) (A.piece I j)
            hdomain hpiece (Subset.rfl) (A.piece_subset_domain I j)).symm
  have hF : AEMeasurable (A.parametrization i)
      (volume.restrict (A.domain i)) :=
    (A.continuousOn_parametrization i).aemeasurable hdomain
  have hsupport : μ.restrict (I.interior M) = μ := by
    exact restrict_riemannianChartAreaMeasure_of_image_subset
      I (A.parametrization i) (A.domain i) hdomain
        (I.interior M) (I.isOpen_interior one_ne_zero).measurableSet hF
        (A.image_subset_interior i)
  have hpartition : μ.restrict (I.interior M) =
      Measure.sum (fun j ↦ μ.restrict (A.imagePiece I j)) := by
    rw [← A.iUnion_imagePiece_eq_interior I]
    exact Measure.restrict_iUnion
      (A.pairwise_disjoint_image_piece I)
      (A.measurableSet_imagePiece I)
  change (riemannianAtlasAreaMeasure I A.parametrization
      (A.piece I)).restrict U = μ
  rw [riemannianAtlasAreaMeasure, Measure.restrict_sum _ hU]
  calc
    Measure.sum (fun j ↦
        (riemannianChartAreaMeasure I (A.parametrization j)
          (A.piece I j)).restrict U) =
        Measure.sum (fun j ↦ μ.restrict (A.imagePiece I j)) := by
      apply congrArg Measure.sum
      funext j
      exact hpair j
    _ = μ := hpartition.symm.trans hsupport

end ControlledInteriorAtlas

/-- Canonical surface area has the expected Jacobian-weighted expression on
the image of every chart in every controlled interior atlas. -/
theorem riemannianSurfaceAreaMeasure_restrict_chart_image
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)]
    (A : ControlledInteriorAtlas I M) (i : ℕ) :
    (riemannianSurfaceAreaMeasure I).restrict
        (A.parametrization i '' A.domain i) =
      riemannianChartAreaMeasure I (A.parametrization i) (A.domain i) := by
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  exact A.areaMeasure_restrict_chart_image I i

/-- Canonical Riemannian surface area is concentrated on the manifold
interior; the boundary has zero canonical area by construction. -/
theorem riemannianSurfaceAreaMeasure_restrict_interior
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoEMetricSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    [Nonempty (ControlledInteriorAtlas I M)] :
    (riemannianSurfaceAreaMeasure I).restrict (I.interior M) =
      riemannianSurfaceAreaMeasure I := by
  let A : ControlledInteriorAtlas I M :=
    Classical.choice (inferInstance : Nonempty (ControlledInteriorAtlas I M))
  rw [← A.areaMeasure_eq_riemannianSurfaceAreaMeasure I]
  exact A.areaMeasure_restrict_interior I

#print axioms
  ControlledInteriorAtlas.restrict_chartAreaMeasure_subset_eq_restrict_overlap
#print axioms ControlledInteriorAtlas.areaMeasure_restrict_interior
#print axioms ControlledInteriorAtlas.areaMeasure_restrict_chart_image
#print axioms riemannianSurfaceAreaMeasure_restrict_chart_image
#print axioms riemannianSurfaceAreaMeasure_restrict_interior

end

end GromovFilling
