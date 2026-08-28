import GromovFilling.Certificates
import GromovFilling.ComplexAreaFormula
import GromovFilling.ProfileFourier

/-!
# A complete finite certificate for planar filling domains

For a domain modeled by the complex plane, the Jordan coverage theorem,
the exact enclosed-area calculation, and the Lipschitz area formula combine
without any remaining coverage hypothesis.  The only final input is the
common Jacobian budget for the finite family of mixed maps.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace GromovFilling

noncomputable section

open unitInterval

/-- Bundled finite chartwise local planar data sufficient for one `N`-mode
orientation-free certificate.  This is the finite atlas-style interface left by
the current planar formalization. -/
structure FiniteComplexLocalCertificateData (N : ℕ) where
  m : ℕ
  omega : Fin N → Set ℂ
  witness : ∀ j : Fin N,
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j)
  pieces : Fin m → Set ℂ
  open_pieces : ∀ i, IsOpen (pieces i)
  G : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  lipschitz : ∀ j i, LipschitzOnWith (K j i) (G j i) (pieces i)
  cover : ∀ j : Fin N, omega j ⊆ ⋃ i, G j i '' pieces i

/-- The summed local Jacobian mass attached to one row of a finite chartwise
local certificate. -/
def FiniteComplexLocalCertificateData.jacobianMass
    {N : ℕ} (D : FiniteComplexLocalCertificateData N) (j : Fin N) : ℝ≥0∞ :=
  ∑ i : Fin D.m,
    ∫⁻ x in D.pieces i, ENNReal.ofReal |(fderiv ℝ (D.G j i) x).det| ∂volume

/-- A bundled finite chartwise local certificate implies the `N`-mode
orientation-free lower bound once its total Jacobian budget is available. -/
theorem FiniteComplexLocalCertificateData.finite_universal_ennreal
    {N : ℕ} (D : FiniteComplexLocalCertificateData N)
    (area : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  refine finite_universal_ennreal_of_givens_coverage_budget N area D.jacobianMass ?_ hbudget
  intro j
  exact (D.witness j).trans
    (complex_volume_le_sum_lintegral_abs_det_fderiv_of_isOpen_of_subset_iUnion_image
      D.pieces (D.G j) (D.omega j) D.open_pieces (D.lipschitz j) (D.cover j))


/-- A bundled finite chartwise local certificate also carries any common
additive defect term unchanged. -/
theorem FiniteComplexLocalCertificateData.finite_universal_ennreal_add
    {N : ℕ} (D : FiniteComplexLocalCertificateData N)
    (area defect : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area := by
  refine finite_universal_ennreal_of_givens_coverage_budget_add
    N area defect D.jacobianMass ?_ hbudget
  intro j
  exact (D.witness j).trans
    (complex_volume_le_sum_lintegral_abs_det_fderiv_of_isOpen_of_subset_iUnion_image
      D.pieces (D.G j) (D.omega j) D.open_pieces (D.lipschitz j) (D.cover j))
/-- Bundled chartwise local planar certificates for every finite truncation at a
common area budget.  Constructing this object is exactly the remaining
certificate-level surface-chart globalization task on the orientation-free side. -/
structure ComplexLocalCertificateSystem (area : ℝ≥0∞) where
  data : ∀ N : ℕ, FiniteComplexLocalCertificateData N
  budget : ∀ N : ℕ, (∑ j : Fin N, (data N).jacobianMass j) ≤ area

/-- A bundled system of chartwise local planar certificates for all finite
truncations implies the full orientation-free universal bound. -/
theorem ComplexLocalCertificateSystem.universal_ennreal
    {area : ℝ≥0∞} (S : ComplexLocalCertificateSystem area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal area (S.budget N)

/-- A bundled system of chartwise local planar certificates also carries any
common additive defect term unchanged through the limit. -/
theorem ComplexLocalCertificateSystem.universal_ennreal_add
    {area defect : ℝ≥0∞} (S : ComplexLocalCertificateSystem area)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add area defect (hbudget N)

/-- Source-side finite chart data for the actual metric Fourier family,
before any topological witness has been supplied.  This isolates the purely
chartwise planar input from the odd-degree obstruction that will later force
coverage of the Jordan witness regions. -/
structure FiniteMetricComplexSourceChartData
    (N : ℕ) (X : Type*) [PseudoMetricSpace X] (boundary : UnitAddCircle → X) where
  m : ℕ
  sourcePiece : Fin m → Set X
  sourcePiece_cover : Set.univ ⊆ ⋃ i, sourcePiece i
  targetPiece : Fin m → Set ℂ
  chart : ∀ i, sourcePiece i → targetPiece i
  targetPiece_open : ∀ i, IsOpen (targetPiece i)
  localMap : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  local_lipschitz : ∀ j i, LipschitzOnWith (K j i) (localMap j i) (targetPiece i)
  local_agree : ∀ j i (x : sourcePiece i),
    givensMetricFourierMap boundary N j x = localMap j i (chart i x)

/-- The summed local planar Jacobian mass attached to one row of a finite
metric source-chart system. -/
def FiniteMetricComplexSourceChartData.jacobianMass
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartData N X boundary) (j : Fin N) : ℝ≥0∞ :=
  ∑ i : Fin D.m,
    ∫⁻ x in D.targetPiece i, ENNReal.ofReal |(fderiv ℝ (D.localMap j i) x).det| ∂volume

/-- The finite orientation-free Fourier certificate for complex-plane
domains, with every rowwise area inequality discharged internally. -/
theorem finite_universal_ennreal_of_complex_planar_maps
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian
      j boundary hfine (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane
domains, with every rowwise area inequality discharged internally at each
finite truncation. -/
theorem universal_ennreal_of_complex_planar_maps
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hfine : HasFinePolygonalModels boundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps
    N area boundary hfine G hG hboundary K hGLipschitz hbudget

/-- A finite orientation-free certificate from chartwise local planar maps.
For each row, it is enough to cover a witnessing region for the mixed boundary
area by finitely many local open pieces and sum the corresponding local
Jacobian masses.  This is the certificate-level interface needed for future
surface-chart globalization. -/
theorem finite_universal_ennreal_of_complex_local_planar_maps
    (N m : ℕ) (area : ℝ≥0∞)
    (omega : Fin N → Set ℂ)
    (homega : ∀ j : Fin N,
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j))
    (pieces : Fin m → Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    (G : Fin N → Fin m → ℂ → ℂ)
    (K : Fin N → Fin m → ℝ≥0)
    (hGLipschitz : ∀ j i, LipschitzOnWith (K j i) (G j i) (pieces i))
    (hcoverage : ∀ j : Fin N, omega j ⊆ ⋃ i, G j i '' pieces i)
    (hbudget :
      (∑ j : Fin N, ∑ i : Fin m,
        ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  refine finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∑ i : Fin m,
      ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) ?_ hbudget
  intro j
  exact (homega j).trans
    (complex_volume_le_sum_lintegral_abs_det_fderiv_of_isOpen_of_subset_iUnion_image
      pieces (G j) (omega j) hpieces (hGLipschitz j) (hcoverage j))

/-- Infinite orientation-free certificate from chartwise local planar maps.
This is the exact limit-level handoff for a future surface proof: for each
finite truncation `N`, produce finitely many open chart pieces, rowwise
coverage of suitable witnessing regions, and one summed Jacobian budget. -/
theorem universal_ennreal_of_complex_local_planar_maps
    (area : ℝ≥0∞)
    (hfinite : ∀ N : ℕ,
      ∃ m : ℕ,
      ∃ omega : Fin N → Set ℂ,
      ∃ pieces : Fin m → Set ℂ,
      ∃ G : Fin N → Fin m → ℂ → ℂ,
      ∃ K : Fin N → Fin m → ℝ≥0,
        (∀ j : Fin N,
          ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j)) ∧
        (∀ i, IsOpen (pieces i)) ∧
        (∀ j i, LipschitzOnWith (K j i) (G j i) (pieces i)) ∧
        (∀ j : Fin N, omega j ⊆ ⋃ i, G j i '' pieces i) ∧
        (∑ j : Fin N, ∑ i : Fin m,
          ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨m, omega, pieces, G, K, homega, hpieces, hGLipschitz, hcoverage, hbudget⟩
  exact finite_universal_ennreal_of_complex_local_planar_maps
    N m area omega homega pieces hpieces G K hGLipschitz hcoverage hbudget


/-- Finite orientation-free certificate from chartwise local planar maps,
carrying an explicit additive defect term through the same local Jacobian
budget. -/
theorem finite_universal_ennreal_add_of_complex_local_planar_maps
    (N m : ℕ) (area defect : ℝ≥0∞)
    (omega : Fin N → Set ℂ)
    (homega : ∀ j : Fin N,
      ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j))
    (pieces : Fin m → Set ℂ)
    (hpieces : ∀ i, IsOpen (pieces i))
    (G : Fin N → Fin m → ℂ → ℂ)
    (K : Fin N → Fin m → ℝ≥0)
    (hGLipschitz : ∀ j i, LipschitzOnWith (K j i) (G j i) (pieces i))
    (hcoverage : ∀ j : Fin N, omega j ⊆ ⋃ i, G j i '' pieces i)
    (hbudget :
      (∑ j : Fin N, ∑ i : Fin m,
        ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area := by
  refine finite_universal_ennreal_of_givens_coverage_budget_add N area defect
    (fun j ↦ ∑ i : Fin m,
      ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) ?_ hbudget
  intro j
  exact (homega j).trans
    (complex_volume_le_sum_lintegral_abs_det_fderiv_of_isOpen_of_subset_iUnion_image
      pieces (G j) (omega j) hpieces (hGLipschitz j) (hcoverage j))

/-- Infinite orientation-free certificate from chartwise local planar maps,
with a common additive defect term carried unchanged through every finite
truncation. -/
theorem universal_ennreal_add_of_complex_local_planar_maps
    (area defect : ℝ≥0∞)
    (hfinite : ∀ N : ℕ,
      ∃ m : ℕ,
      ∃ omega : Fin N → Set ℂ,
      ∃ pieces : Fin m → Set ℂ,
      ∃ G : Fin N → Fin m → ℂ → ℂ,
      ∃ K : Fin N → Fin m → ℝ≥0,
        (∀ j : Fin N,
          ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j)) ∧
        (∀ i, IsOpen (pieces i)) ∧
        (∀ j i, LipschitzOnWith (K j i) (G j i) (pieces i)) ∧
        (∀ j : Fin N, omega j ⊆ ⋃ i, G j i '' pieces i) ∧
        ((∑ j : Fin N, ∑ i : Fin m,
          ∫⁻ x in pieces i, ENNReal.ofReal |(fderiv ℝ (G j i) x).det| ∂volume) + defect ≤ area)) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  rcases hfinite N with ⟨m, omega, pieces, G, K, homega, hpieces, hGLipschitz, hcoverage, hbudget⟩
  exact finite_universal_ennreal_add_of_complex_local_planar_maps
    N m area defect omega homega pieces hpieces G K hGLipschitz hcoverage hbudget
/-- Bundled source-side finite chart data sufficient to produce one local
planar certificate.  The source pieces cover the whole source, each local chart
lands in an open planar piece, and the row maps agree there with planar local
representatives. -/
structure FiniteComplexSourceChartCertificateData (N : ℕ) (X : Type*) where
  m : ℕ
  omega : Fin N → Set ℂ
  witness : ∀ j : Fin N,
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤ volume (omega j)
  rowMap : Fin N → X → ℂ
  rowMap_covers : ∀ j : Fin N, omega j ⊆ Set.range (rowMap j)
  sourcePiece : Fin m → Set X
  sourcePiece_cover : Set.univ ⊆ ⋃ i, sourcePiece i
  targetPiece : Fin m → Set ℂ
  chart : ∀ i, sourcePiece i → targetPiece i
  targetPiece_open : ∀ i, IsOpen (targetPiece i)
  localMap : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  local_lipschitz : ∀ j i, LipschitzOnWith (K j i) (localMap j i) (targetPiece i)
  local_agree : ∀ j i (x : sourcePiece i),
    rowMap j x = localMap j i (chart i x)

/-- Source-side chart data canonically yields the local planar certificate data
used by the finite and infinite planar certificate theorems. -/
def FiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData
    {N : ℕ} {X : Type*} (D : FiniteComplexSourceChartCertificateData N X) :
    FiniteComplexLocalCertificateData N where
  m := D.m
  omega := D.omega
  witness := D.witness
  pieces := D.targetPiece
  open_pieces := D.targetPiece_open
  G := D.localMap
  K := D.K
  lipschitz := D.local_lipschitz
  cover := by
    intro j z hz
    rcases D.rowMap_covers j hz with ⟨x, rfl⟩
    have hx : x ∈ ⋃ i, D.sourcePiece i := D.sourcePiece_cover (by trivial)
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    let y : D.targetPiece i := D.chart i ⟨x, hxi⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine ⟨y, y.property, ?_⟩
    simpa [y] using (D.local_agree j i ⟨x, hxi⟩).symm

/-- A bundled source-side finite chart certificate implies the `N`-mode
orientation-free lower bound once its total Jacobian budget is available. -/
theorem FiniteComplexSourceChartCertificateData.finite_universal_ennreal
    {N : ℕ} {X : Type*} (D : FiniteComplexSourceChartCertificateData N X)
    (area : ℝ≥0∞)
    (hbudget :
      (∑ j : Fin N, (D.toFiniteComplexLocalCertificateData).jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  (D.toFiniteComplexLocalCertificateData).finite_universal_ennreal area hbudget


/-- A bundled source-side finite chart certificate also carries any common
additive defect term unchanged. -/
theorem FiniteComplexSourceChartCertificateData.finite_universal_ennreal_add
    {N : ℕ} {X : Type*} (D : FiniteComplexSourceChartCertificateData N X)
    (area defect : ℝ≥0∞)
    (hbudget :
      (∑ j : Fin N, (D.toFiniteComplexLocalCertificateData).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area :=
  (D.toFiniteComplexLocalCertificateData).finite_universal_ennreal_add area defect hbudget
/-- Bundled source-side chart data for every finite truncation at a common area
budget.  Constructing this object is the next concrete surface-side obligation
for the orientation-free argument. -/
structure ComplexSourceChartCertificateSystem (X : Type*) (area : ℝ≥0∞) where
  data : ∀ N : ℕ, FiniteComplexSourceChartCertificateData N X
  budget : ∀ N : ℕ,
    (∑ j : Fin N, ((data N).toFiniteComplexLocalCertificateData).jacobianMass j) ≤ area

/-- A bundled source-side chart certificate system implies the full
orientation-free universal bound. -/
theorem ComplexSourceChartCertificateSystem.universal_ennreal
    {X : Type*} {area : ℝ≥0∞} (S : ComplexSourceChartCertificateSystem X area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal area (S.budget N)


/-- A bundled source-side chart certificate system also carries any common
additive defect term unchanged through the limit. -/
theorem ComplexSourceChartCertificateSystem.universal_ennreal_add
    {X : Type*} {area defect : ℝ≥0∞} (S : ComplexSourceChartCertificateSystem X area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N, ((S.data N).toFiniteComplexLocalCertificateData).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add area defect (hbudget N)
/-- A canonical choice of the Jordan region of the mixed `j`th boundary curve
that contains the origin. -/
def givensBoundaryCurveChosenJordanRegion {N : ℕ} (j : Fin N) : Set ℂ :=
  Classical.choose (exists_givensBoundaryCurve_jordanPartition_at_origin j)

/-- The complementary Jordan region paired with
`givensBoundaryCurveChosenJordanRegion`. -/
def givensBoundaryCurveChosenJordanRegionComplement {N : ℕ} (j : Fin N) : Set ℂ :=
  Classical.choose (Classical.choose_spec
    (exists_givensBoundaryCurve_jordanPartition_at_origin j))

/-- The chosen Jordan regions form a Jordan partition of the mixed boundary
curve. -/
theorem givensBoundaryCurveChosenJordanPartition
    {N : ℕ} (j : Fin N) :
    IsJordanPartition
      (Set.range (givensBoundaryCurveAddCircle j))
      (givensBoundaryCurveChosenJordanRegion j)
      (givensBoundaryCurveChosenJordanRegionComplement j) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_givensBoundaryCurve_jordanPartition_at_origin j))).1

/-- The chosen Jordan region contains the origin. -/
theorem zero_mem_givensBoundaryCurveChosenJordanRegion
    {N : ℕ} (j : Fin N) :
    0 ∈ givensBoundaryCurveChosenJordanRegion j :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_givensBoundaryCurve_jordanPartition_at_origin j))).2

/-- Source-side finite chart data with the topological witness generated
internally from the odd boundary-degree obstruction.  This removes the need to
supply the planar witness regions or their coverage by hand. -/
structure FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction
    (N : ℕ) (X : Type*) [TopologicalSpace X] (boundary : UnitAddCircle → X) where
  hobstruction : HasOddBoundaryDegreeObstruction boundary
  rowMap : Fin N → X → ℂ
  rowMap_cont : ∀ j, Continuous (rowMap j)
  rowMap_boundary : ∀ j t, rowMap j (boundary t) = givensBoundaryCurveAddCircle j t
  m : ℕ
  sourcePiece : Fin m → Set X
  sourcePiece_cover : Set.univ ⊆ ⋃ i, sourcePiece i
  targetPiece : Fin m → Set ℂ
  chart : ∀ i, sourcePiece i → targetPiece i
  targetPiece_open : ∀ i, IsOpen (targetPiece i)
  localMap : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  local_lipschitz : ∀ j i, LipschitzOnWith (K j i) (localMap j i) (targetPiece i)
  local_agree : ∀ j i (x : sourcePiece i),
    rowMap j x = localMap j i (chart i x)

/-- Obstruction-level source-side chart data canonically yields the finite
source-chart certificate data used by the planar certificate layer. -/
def FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction.toFiniteComplexSourceChartCertificateData
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary) :
    FiniteComplexSourceChartCertificateData N X where
  m := D.m
  omega := fun j ↦ givensBoundaryCurveChosenJordanRegion j
  witness := by
    intro j
    exact le_of_eq <|
      (volume_givensBoundaryCurve_jordan_region j
        (givensBoundaryCurveChosenJordanPartition j)
        (zero_mem_givensBoundaryCurveChosenJordanRegion j)).symm
  rowMap := D.rowMap
  rowMap_covers := by
    intro j
    exact jordan_region_subset_range_of_odd_boundary_degree_obstruction
      boundary D.hobstruction (D.rowMap j) (D.rowMap_cont j)
      (givensBoundaryCurveAddCircle j) (continuous_givensBoundaryCurveAddCircle j)
      (D.rowMap_boundary j) 0 (givensBoundaryCurveAddCircle_ne_zero j) 1
      (by simpa [givensBoundaryCurveAddCircle] using givensBoundaryCurve_degree_one j)
      odd_one (givensBoundaryCurveChosenJordanPartition j)
      (zero_mem_givensBoundaryCurveChosenJordanRegion j)
  sourcePiece := D.sourcePiece
  sourcePiece_cover := D.sourcePiece_cover
  targetPiece := D.targetPiece
  chart := D.chart
  targetPiece_open := D.targetPiece_open
  localMap := D.localMap
  K := D.K
  local_lipschitz := D.local_lipschitz
  local_agree := D.local_agree

/-- An obstruction-level bundled source-side finite chart certificate implies
the `N`-mode orientation-free lower bound once its total Jacobian budget is
available. -/
theorem FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction.finite_universal_ennreal
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (area : ℝ≥0∞)
    (hbudget :
      (∑ j : Fin N,
        (D.toFiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData).jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  (D.toFiniteComplexSourceChartCertificateData).finite_universal_ennreal area hbudget


/-- An obstruction-level bundled source-side finite chart certificate also
carries any common additive defect term unchanged. -/
theorem FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction.finite_universal_ennreal_add
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (area defect : ℝ≥0∞)
    (hbudget :
      (∑ j : Fin N,
        (D.toFiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area :=
  (D.toFiniteComplexSourceChartCertificateData).finite_universal_ennreal_add area defect hbudget
/-- Obstruction-level source-side chart data for every finite truncation at a
common area budget.  Constructing this object is the exact remaining
orientation-free chart-globalization task once the odd-degree obstruction is
available on the source. -/
structure ComplexSourceChartSystemOfOddBoundaryDegreeObstruction
    (X : Type*) [TopologicalSpace X]
    (boundary : UnitAddCircle → X) (area : ℝ≥0∞) where
  data : ∀ N : ℕ, FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary
  budget : ∀ N : ℕ,
    (∑ j : Fin N,
      (((data N).toFiniteComplexSourceChartCertificateData).toFiniteComplexLocalCertificateData).jacobianMass j) ≤ area

/-- An obstruction-level bundled source-side chart certificate system implies
the full orientation-free universal bound. -/
theorem ComplexSourceChartSystemOfOddBoundaryDegreeObstruction.universal_ennreal
    {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystemOfOddBoundaryDegreeObstruction X boundary area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal area (S.budget N)

/-- An obstruction-level bundled source-side chart certificate system also
carries any common additive defect term unchanged through the limit. -/
theorem ComplexSourceChartSystemOfOddBoundaryDegreeObstruction.universal_ennreal_add
    {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystemOfOddBoundaryDegreeObstruction X boundary area)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        (((S.data N).toFiniteComplexSourceChartCertificateData).toFiniteComplexLocalCertificateData).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add area defect (hbudget N)

/-- Source-side finite chart data for a generic family of row maps, separated
from the topological input that will later force coverage of the Jordan witness
regions. -/
structure FiniteComplexSourceChartData
    (N : ℕ) (X : Type*) [TopologicalSpace X] (boundary : UnitAddCircle → X) where
  rowMap : Fin N → X → ℂ
  rowMap_cont : ∀ j, Continuous (rowMap j)
  rowMap_boundary : ∀ j t, rowMap j (boundary t) = givensBoundaryCurveAddCircle j t
  m : ℕ
  sourcePiece : Fin m → Set X
  sourcePiece_cover : Set.univ ⊆ ⋃ i, sourcePiece i
  targetPiece : Fin m → Set ℂ
  chart : ∀ i, sourcePiece i → targetPiece i
  targetPiece_open : ∀ i, IsOpen (targetPiece i)
  localMap : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  local_lipschitz : ∀ j i, LipschitzOnWith (K j i) (localMap j i) (targetPiece i)
  local_agree : ∀ j i (x : sourcePiece i),
    rowMap j x = localMap j i (chart i x)

/-- The summed local planar Jacobian mass attached to one row of a generic
source-chart system. -/
def FiniteComplexSourceChartData.jacobianMass
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartData N X boundary) (j : Fin N) : ℝ≥0∞ :=
  ∑ i : Fin D.m,
    ∫⁻ x in D.targetPiece i, ENNReal.ofReal |(fderiv ℝ (D.localMap j i) x).det| ∂volume

/-- A generic source-chart system becomes an obstruction-level one once an odd
boundary-degree obstruction has been supplied. -/
def FiniteComplexSourceChartData.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary where
  hobstruction := hobstruction
  rowMap := D.rowMap
  rowMap_cont := D.rowMap_cont
  rowMap_boundary := D.rowMap_boundary
  m := D.m
  sourcePiece := D.sourcePiece
  sourcePiece_cover := D.sourcePiece_cover
  targetPiece := D.targetPiece
  chart := D.chart
  targetPiece_open := D.targetPiece_open
  localMap := D.localMap
  K := D.K
  local_lipschitz := D.local_lipschitz
  local_agree := D.local_agree

/-- A finite generic source-chart certificate yields the `N`-mode
orientation-free lower bound once the odd-degree obstruction and its summed
local planar Jacobian budget are available. -/
theorem FiniteComplexSourceChartData.finite_universal_ennreal_of_odd_boundary_degree_obstruction
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (area : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  simpa [FiniteComplexSourceChartData.jacobianMass,
    FiniteComplexSourceChartData.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction,
    FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction.toFiniteComplexSourceChartCertificateData,
    FiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData,
    FiniteComplexLocalCertificateData.jacobianMass]
    using
      (D.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction hobstruction).finite_universal_ennreal
        area hbudget

/-- A finite generic source-chart certificate carries any common additive
defect term once the odd-degree obstruction is supplied separately. -/
theorem FiniteComplexSourceChartData.finite_universal_ennreal_add_of_odd_boundary_degree_obstruction
    {N : ℕ} {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (area defect : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area := by
  simpa [FiniteComplexSourceChartData.jacobianMass,
    FiniteComplexSourceChartData.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction,
    FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction.toFiniteComplexSourceChartCertificateData,
    FiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData,
    FiniteComplexLocalCertificateData.jacobianMass]
    using
      (D.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction hobstruction).finite_universal_ennreal_add
        area defect hbudget

/-- Bundled source-side chart data for a generic family of row maps, separated
from the topological input that forces coverage of the Jordan witness regions. -/
structure ComplexSourceChartSystem
    (X : Type*) [TopologicalSpace X]
    (boundary : UnitAddCircle → X) (area : ℝ≥0∞) where
  data : ∀ N : ℕ, FiniteComplexSourceChartData N X boundary
  budget : ∀ N : ℕ, (∑ j : Fin N, (data N).jacobianMass j) ≤ area

/-- A bundled generic source-chart system implies the full orientation-free
universal bound once the odd boundary-degree obstruction is available on the
source. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_odd_boundary_degree_obstruction
    {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal_of_odd_boundary_degree_obstruction
    hobstruction area (S.budget N)

/-- The quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface supplies the odd boundary-degree obstruction needed by a generic
source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
      hmodels)

/-- The stronger directed abstract arbitrarily-fine polygonal-model interface
already supplies the obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
      hmodels)


/-- The bundled explicit glued-strip quotient mesh-data interface already
supplies the quotient-friendly abstract polygonal-model input needed by a
generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData
      hmodels)

/-- Explicit glued-strip quotient data already supplies the quotient-friendly
abstract polygonal-model interface needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle))) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_cylinderStripGluedArbitrarilyFineData
    (hasCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data hmodels)

/-- The bundled homeomorphism-plus-glued-strip interface supplies the generic
source-chart certificate through the homeomorphism-transfer route. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary') :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorphCylinderStripGluedArbitrarilyFineData D)

/-- The original unbundled homeomorphism-plus-glued-strip hypothesis likewise
feeds the generic source-chart certificate by first repackaging it into the
bundled interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_homeomorph_cylinderStripGlued_data
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle))) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    (homeomorphCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data
      e hboundaryHomeomorph hmodels)

/-- Coverage also transfers from a compact source carrying the quotient-friendly
 directed abstract arbitrarily-fine polygonal-model interface once a
 boundary-respecting homeomorphism identifies that source with the target of a
 generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The same homeomorphism-transfer route works already from the stronger
 directed abstract arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedArbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The same homeomorphism-transfer route also works from the ordinary
 arbitrarily-fine polygonal-model interface.  This is the direct handoff from a
 future compact-surface triangulation theorem to the generic source-chart
 certificate layer. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The same source-chart certificate also transfers from a compact source
through any boundary-respecting continuous map once the source carries the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_compact_continuous_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
        hmodels))

/-- The same continuous-map transfer route works from the stronger directed
abstract arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_compact_continuous_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
        hmodels))

/-- The same continuous-map transfer route also works from the ordinary
arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels hmodels))

/-- A nullhomotopy of the source boundary loop likewise supplies the odd
boundary-degree obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_nullhomotopy
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_nullhomotopy center F hF0 hF1)

/-- A closed-disk extension of the source boundary supplies the odd
boundary-degree obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_extension
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (F : ClosedUnitDisk → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension F hF hboundaryMap)

/-- A closed-disk homeomorphism with the source boundary supplies the odd
boundary-degree obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_direct
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundaryMap)

/-- The disk-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface likewise supplies the odd boundary-degree
obstruction for a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)

/-- The disk-homeomorphic route through the packaged disk existence interface
likewise supplies the odd boundary-degree obstruction for a generic
source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)

/-- Cylinder-strip arbitrarily-fine model data on the standard disk induces
the odd boundary-degree obstruction needed by a compact generic source-chart
system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
        e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match e with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryMap hmodels)

/-- A closed-square extension of the source boundary supplies the odd
boundary-degree obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_extension
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (F : ClosedUnitSquare → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_extension F hF hboundaryMap)

/-- A closed-square homeomorphism with the source boundary supplies the odd
boundary-degree obstruction needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_homeomorph_direct
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_direct e hboundaryMap)

/-- The square-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface likewise supplies the odd boundary-degree
obstruction for a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)

/-- A bundled generic source-chart system implies the full orientation-free
universal bound with a common additive defect term once the odd
boundary-degree obstruction is available on the source. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_odd_boundary_degree_obstruction
    {X : Type*} [TopologicalSpace X] {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add_of_odd_boundary_degree_obstruction
    hobstruction area defect (hbudget N)

/-- The quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface also supplies the odd boundary-degree obstruction needed for the
additive-defect generic source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
      hmodels)
    hbudget

/-- The stronger directed abstract arbitrarily-fine polygonal-model interface
already supplies the additive-defect generic source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
      hmodels)
    hbudget


/-- The bundled explicit glued-strip quotient mesh-data interface already
supplies the additive-defect quotient-friendly abstract polygonal-model input
needed by a generic source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData
      hmodels)
    hbudget

/-- Explicit glued-strip quotient data already supplies the additive-defect
quotient-friendly abstract polygonal-model interface needed by a generic
source-chart system. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_cylinderStripGluedArbitrarilyFineData
    (hasCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data hmodels)
    hbudget

/-- The bundled homeomorphism-plus-glued-strip interface also supplies the
additive-defect generic source-chart certificate through the homeomorphism
transfer route. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorphCylinderStripGluedArbitrarilyFineData D)
    hbudget

/-- The original unbundled homeomorphism-plus-glued-strip hypothesis likewise
feeds the additive-defect generic source-chart certificate after repackaging. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_cylinderStripGlued_data
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    (homeomorphCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The additive-defect generic source-chart certificate also transfers from a
 compact source carrying the quotient-friendly directed abstract arbitrarily-
 fine polygonal-model interface through a boundary-respecting homeomorphism. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The same additive-defect transfer route works already from the stronger
 directed abstract arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The same additive-defect transfer route also works from the ordinary
 arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The additive-defect generic source-chart certificate also transfers from a
compact source through any boundary-respecting continuous map once the source
carries the quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
        hmodels))
    hbudget

/-- The same additive-defect continuous-map transfer route works from the
stronger directed abstract arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
        hmodels))
    hbudget

/-- The same additive-defect continuous-map transfer route also works from the
ordinary arbitrarily-fine polygonal-model interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [TopologicalSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels hmodels))
    hbudget

/-- A nullhomotopy of the source boundary loop likewise supplies the odd
boundary-degree obstruction needed for the additive-defect generic source-chart
certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_nullhomotopy
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_nullhomotopy center F hF0 hF1)
    hbudget

/-- A closed-disk extension of the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect generic
source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_extension
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (F : ClosedUnitDisk → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension F hF hboundaryMap)
    hbudget

/-- A closed-disk homeomorphism with the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect generic
source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_direct
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundaryMap)
    hbudget

/-- The additive-defect generic source-chart certificate also follows from the
quotient-friendly directed disk-homeomorphism interface. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)
    hbudget

/-- The disk-homeomorphic route through the packaged disk existence interface
likewise supplies the additive-defect generic source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)
    hbudget

/-- Cylinder-strip arbitrarily-fine model data on the standard disk also
induces the additive-defect generic source-chart certificate on a compact
boundary homeomorphic to the closed disk. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
        e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match e with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryMap hmodels)
    hbudget

/-- A closed-square extension of the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect generic
source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_extension
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (F : ClosedUnitSquare → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_extension F hF hboundaryMap)
    hbudget

/-- A closed-square homeomorphism with the source boundary also supplies the
odd boundary-degree obstruction needed for the additive-defect generic
source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_homeomorph_direct
    {X : Type*} [TopologicalSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_direct e hboundaryMap)
    hbudget

/-- The square-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface also supplies the odd boundary-degree
obstruction for the additive-defect generic source-chart certificate. -/
theorem ComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : ComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)
    hbudget

/-- Source-side finite chart data for the actual metric Fourier family, with
the topological witness again generated internally from an odd boundary-degree
obstruction.  This is the direct chart-globalization interface for the genuine
mixed metric maps. -/
structure FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction
    (N : ℕ) (X : Type*) [PseudoMetricSpace X] (boundary : UnitAddCircle → X) where
  hobstruction : HasOddBoundaryDegreeObstruction boundary
  m : ℕ
  sourcePiece : Fin m → Set X
  sourcePiece_cover : Set.univ ⊆ ⋃ i, sourcePiece i
  targetPiece : Fin m → Set ℂ
  chart : ∀ i, sourcePiece i → targetPiece i
  targetPiece_open : ∀ i, IsOpen (targetPiece i)
  localMap : Fin N → Fin m → ℂ → ℂ
  K : Fin N → Fin m → ℝ≥0
  local_lipschitz : ∀ j i, LipschitzOnWith (K j i) (localMap j i) (targetPiece i)
  local_agree : ∀ j i (x : sourcePiece i),
    givensMetricFourierMap boundary N j x = localMap j i (chart i x)

/-- Metric source-side chart data converts to the generic obstruction-level
source-chart certificate by taking the row maps to be the genuine mixed metric
Fourier maps. -/
def FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    FiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary where
  hobstruction := D.hobstruction
  rowMap := fun j ↦ givensMetricFourierMap boundary N j
  rowMap_cont := fun j ↦ continuous_givensMetricFourierMap hboundary N j
  rowMap_boundary := fun j t ↦ givensMetricFourierMap_on_boundary hboundary j t
  m := D.m
  sourcePiece := D.sourcePiece
  sourcePiece_cover := D.sourcePiece_cover
  targetPiece := D.targetPiece
  chart := D.chart
  targetPiece_open := D.targetPiece_open
  localMap := D.localMap
  K := D.K
  local_lipschitz := D.local_lipschitz
  local_agree := D.local_agree

/-- The total planar Jacobian mass extracted from one finite metric
source-chart certificate. -/
def FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.jacobianMass
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (hboundary : IsometricCircleBoundary boundary) (j : Fin N) : ℝ≥0∞ :=
  ((D.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction hboundary).toFiniteComplexSourceChartCertificateData.toFiniteComplexLocalCertificateData).jacobianMass j

/-- A finite metric source-chart certificate yields the `N`-mode
orientation-free lower bound once its summed local planar Jacobian budget is
available. -/
theorem FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.finite_universal_ennreal
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (area : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass hboundary j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  (D.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction hboundary).finite_universal_ennreal area hbudget


/-- A finite metric source-chart certificate also carries any common additive
defect term unchanged. -/
theorem FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.finite_universal_ennreal_add
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (area defect : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass hboundary j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area :=
  (D.toFiniteComplexSourceChartDataOfOddBoundaryDegreeObstruction hboundary).finite_universal_ennreal_add area defect hbudget

/-- Bundled source-side chart data for the genuine mixed metric Fourier maps,
for every finite truncation at a common area budget.  This is the direct
chart-globalization interface now left on the orientation-free side once the
odd-degree obstruction is available on the source. -/
structure MetricComplexSourceChartSystemOfOddBoundaryDegreeObstruction
    (X : Type*) [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (area : ℝ≥0∞) where
  hboundary : IsometricCircleBoundary boundary
  data : ∀ N : ℕ, FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary
  budget : ∀ N : ℕ, (∑ j : Fin N, (data N).jacobianMass hboundary j) ≤ area

/-- A bundled metric source-chart certificate system implies the full
orientation-free universal bound. -/
theorem MetricComplexSourceChartSystemOfOddBoundaryDegreeObstruction.universal_ennreal
    {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystemOfOddBoundaryDegreeObstruction X boundary area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal S.hboundary area (S.budget N)

/-- A bundled metric source-chart certificate system at the obstruction level
also carries any common additive defect term unchanged through the limit. -/
theorem MetricComplexSourceChartSystemOfOddBoundaryDegreeObstruction.universal_ennreal_add
    {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystemOfOddBoundaryDegreeObstruction X boundary area)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass S.hboundary j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add S.hboundary area defect (hbudget N)

/-- A metric source-chart system becomes an obstruction-level one once an odd
boundary-degree obstruction has been supplied. -/
def FiniteMetricComplexSourceChartData.toFiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction N X boundary where
  hobstruction := hobstruction
  m := D.m
  sourcePiece := D.sourcePiece
  sourcePiece_cover := D.sourcePiece_cover
  targetPiece := D.targetPiece
  chart := D.chart
  targetPiece_open := D.targetPiece_open
  localMap := D.localMap
  K := D.K
  local_lipschitz := D.local_lipschitz
  local_agree := D.local_agree

/-- A finite metric source-chart certificate yields the `N`-mode
orientation-free lower bound once the odd-degree obstruction and its summed
local planar Jacobian budget are available. -/
theorem FiniteMetricComplexSourceChartData.finite_universal_ennreal_of_odd_boundary_degree_obstruction
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (area : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  simpa [FiniteMetricComplexSourceChartData.jacobianMass,
    FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.jacobianMass,
    FiniteMetricComplexSourceChartData.toFiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction]
    using
      (D.toFiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction hobstruction).finite_universal_ennreal
        hboundary area hbudget


/-- A finite metric source-chart certificate carries any common additive
defect term once the odd-degree obstruction is supplied separately. -/
theorem FiniteMetricComplexSourceChartData.finite_universal_ennreal_add_of_odd_boundary_degree_obstruction
    {N : ℕ} {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X}
    (D : FiniteMetricComplexSourceChartData N X boundary)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (area defect : ℝ≥0∞)
    (hbudget : (∑ j : Fin N, D.jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) + defect ≤ area := by
  simpa [FiniteMetricComplexSourceChartData.jacobianMass,
    FiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction.jacobianMass,
    FiniteMetricComplexSourceChartData.toFiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction]
    using
      (D.toFiniteMetricComplexSourceChartDataOfOddBoundaryDegreeObstruction hobstruction).finite_universal_ennreal_add
        hboundary area defect hbudget
/-- Bundled source-side chart data for the genuine mixed metric Fourier maps,
separated from the topological input that forces coverage of the Jordan witness
regions. -/
structure MetricComplexSourceChartSystem
    (X : Type*) [PseudoMetricSpace X]
    (boundary : UnitAddCircle → X) (area : ℝ≥0∞) where
  hboundary : IsometricCircleBoundary boundary
  data : ∀ N : ℕ, FiniteMetricComplexSourceChartData N X boundary
  budget : ∀ N : ℕ, (∑ j : Fin N, (data N).jacobianMass j) ≤ area

/-- A bundled metric source-chart system implies the full orientation-free
universal bound once the odd boundary-degree obstruction is available on the
source. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_odd_boundary_degree_obstruction
    {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact (S.data N).finite_universal_ennreal_of_odd_boundary_degree_obstruction
    hobstruction S.hboundary area (S.budget N)

/-- The quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface supplies the odd boundary-degree obstruction needed by a metric
source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
      hmodels)

/-- The stronger directed abstract arbitrarily-fine polygonal-model interface
already supplies the obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
      hmodels)


/-- The bundled explicit glued-strip quotient mesh-data interface already
supplies the quotient-friendly abstract polygonal-model input needed by a
metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData
      hmodels)

/-- Explicit glued-strip quotient data already supplies the quotient-friendly
abstract polygonal-model interface needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle))) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_cylinderStripGluedArbitrarilyFineData
    (hasCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data hmodels)

/-- The bundled homeomorphism-plus-glued-strip interface supplies the metric
source-chart certificate through the homeomorphism-transfer route. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary') :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorphCylinderStripGluedArbitrarilyFineData D)

/-- The original unbundled homeomorphism-plus-glued-strip hypothesis likewise
feeds the metric source-chart certificate after repackaging. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_homeomorph_cylinderStripGlued_data
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle))) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    (homeomorphCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data
      e hboundaryHomeomorph hmodels)

/-- The metric source-chart certificate also transfers from a compact source
 carrying the quotient-friendly directed abstract arbitrarily-fine polygonal-
 model interface through a boundary-respecting homeomorphism. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The same metric transfer route works already from the stronger directed
 abstract arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedArbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The same metric transfer route also works from the ordinary arbitrarily-
 fine polygonal-model interface, which is the direct target of a future
 compact-surface triangulation theorem. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)

/-- The metric source-chart certificate also transfers from a compact source
through any boundary-respecting continuous map once the source carries the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_compact_continuous_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
        hmodels))

/-- The same continuous-map transfer route works from the stronger directed
abstract arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_compact_continuous_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
        hmodels))

/-- The same continuous-map transfer route also works from the ordinary
arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels hmodels))

/-- A nullhomotopy of the source boundary loop likewise supplies the odd
boundary-degree obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_nullhomotopy
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_nullhomotopy center F hF0 hF1)

/-- A closed-disk extension of the source boundary supplies the odd
boundary-degree obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_extension
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (F : ClosedUnitDisk → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension F hF hboundaryMap)

/-- A closed-disk homeomorphism with the source boundary supplies the odd
boundary-degree obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_direct
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundaryMap)

/-- The disk-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface likewise supplies the odd boundary-degree
obstruction for a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)

/-- The disk-homeomorphic route through the packaged disk existence interface
likewise supplies the odd boundary-degree obstruction for a metric
source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)

/-- Cylinder-strip arbitrarily-fine model data on the standard disk induces the
odd boundary-degree obstruction needed by a compact metric source-chart
system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
        e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match e with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryMap hmodels)

/-- A closed-square extension of the source boundary supplies the odd
boundary-degree obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_extension
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (F : ClosedUnitSquare → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_extension F hF hboundaryMap)

/-- A closed-square homeomorphism with the source boundary supplies the odd
boundary-degree obstruction needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_homeomorph_direct
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_direct e hboundaryMap)

/-- The square-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface likewise supplies the odd boundary-degree
obstruction for a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary) :
    ENNReal.ofReal universalConstant ≤ area :=
  S.universal_ennreal_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)

/-- A bundled metric source-chart system implies the full orientation-free
universal bound with a common additive defect term once the odd
boundary-degree obstruction is available on the source. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_odd_boundary_degree_obstruction
    {X : Type*} [PseudoMetricSpace X] {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact (S.data N).finite_universal_ennreal_add_of_odd_boundary_degree_obstruction
    hobstruction S.hboundary area defect (hbudget N)

/-- The quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface also supplies the odd boundary-degree obstruction needed for the
additive-defect metric source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
      hmodels)
    hbudget

/-- The stronger directed abstract arbitrarily-fine polygonal-model interface
already supplies the additive-defect metric source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
      hmodels)
    hbudget


/-- The bundled explicit glued-strip quotient mesh-data interface already
supplies the additive-defect quotient-friendly abstract polygonal-model input
needed by a metric source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : HasCylinderStripGluedArbitrarilyFineData boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData
      hmodels)
    hbudget

/-- Explicit glued-strip quotient data already supplies the additive-defect
quotient-friendly abstract polygonal-model interface needed by a metric
source-chart system. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_cylinderStripGluedArbitrarilyFineData
    (hasCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data hmodels)
    hbudget

/-- The bundled homeomorphism-plus-glued-strip interface also supplies the
additive-defect metric source-chart certificate through the homeomorphism
transfer route. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorphCylinderStripGluedArbitrarilyFineData D)
    hbudget

/-- The original unbundled homeomorphism-plus-glued-strip hypothesis likewise
feeds the additive-defect metric source-chart certificate after repackaging. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_cylinderStripGlued_data
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    (homeomorphCylinderStripGluedArbitrarilyFineData_of_cylinderStripGlued_data
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The additive-defect metric source-chart certificate also transfers from a
 compact source carrying the quotient-friendly directed abstract arbitrarily-
 fine polygonal-model interface through a boundary-respecting homeomorphism. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The same additive-defect metric transfer route works already from the
 stronger directed abstract arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The same additive-defect metric transfer route also works from the
 ordinary arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_homeomorph_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (e : X ≃ₜ Y)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_homeomorph_arbitrarilyFine
      e hboundaryHomeomorph hmodels)
    hbudget

/-- The additive-defect metric source-chart certificate also transfers from a
compact source through any boundary-respecting continuous map once the source
carries the quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_abstractVariableDirectedQuotientArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedQuotientArbitrarilyFinePolygonalModels
        hmodels))
    hbudget

/-- The same additive-defect continuous-map transfer route works from the
stronger directed abstract arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_abstractVariableDirectedArbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasAbstractVariableDirectedArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_abstractVariableDirectedArbitrarilyFinePolygonalModels
        hmodels))
    hbudget

/-- The same additive-defect continuous-map transfer route also works from the
ordinary arbitrarily-fine polygonal-model interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_compact_continuous_arbitrarilyFine
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → Y} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem Y boundary' area)
    (f : X → Y) (hf : Continuous f)
    (hboundaryMap : boundary' = f ∘ boundary)
    (hmodels : HasArbitrarilyFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_comp_continuous f hf hboundaryMap
      (hasOddBoundaryDegreeObstruction_of_arbitrarilyFinePolygonalModels hmodels))
    hbudget

/-- A nullhomotopy of the source boundary loop likewise supplies the odd
boundary-degree obstruction needed for the additive-defect metric source-chart
certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_nullhomotopy
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (center : X)
    (F : C(I × UnitAddCircle, X))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_nullhomotopy center F hF0 hF1)
    hbudget

/-- A closed-disk extension of the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect metric
source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_extension
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (F : ClosedUnitDisk → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_extension F hF hboundaryMap)
    hbudget

/-- A closed-disk homeomorphism with the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect metric
source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_direct
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_direct e hboundaryMap)
    hbudget

/-- The additive-defect metric source-chart certificate also follows from the
quotient-friendly directed disk-homeomorphism interface. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)
    hbudget

/-- The disk-homeomorphic route through the packaged disk existence interface
likewise supplies the additive-defect metric source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hdisk : HasArbitrarilyFinePolygonalModels closedUnitDiskBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph e hboundaryMap hdisk)
    hbudget

/-- Cylinder-strip arbitrarily-fine model data on the standard disk also
induces the additive-defect metric source-chart certificate on a compact metric
boundary homeomorphic to the closed disk. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitDisk ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (e : CylinderStripEdge n m),
        e ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match e with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryMap hmodels)
    hbudget

/-- A closed-square extension of the source boundary also supplies the odd
boundary-degree obstruction needed for the additive-defect metric
source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_extension
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (F : ClosedUnitSquare → X) (hF : Continuous F)
    (hboundaryMap : boundary = F ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_extension F hF hboundaryMap)
    hbudget

/-- A closed-square homeomorphism with the source boundary also supplies the
odd boundary-degree obstruction needed for the additive-defect metric
source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_homeomorph_direct
    {X : Type*} [PseudoMetricSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_direct e hboundaryMap)
    hbudget
/-- The square-homeomorphic route through the quotient-friendly directed
abstract polygonal-model interface also supplies the odd boundary-degree
obstruction for the additive-defect metric source-chart certificate. -/
theorem MetricComplexSourceChartSystem.universal_ennreal_add_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {boundary : UnitAddCircle → X} {area defect : ℝ≥0∞}
    (S : MetricComplexSourceChartSystem X boundary area)
    (e : ClosedUnitSquare ≃ₜ X)
    (hboundaryMap : boundary = e ∘ closedUnitSquareBoundary)
    (hbudget : ∀ N : ℕ, (∑ j : Fin N, (S.data N).jacobianMass j) + defect ≤ area) :
    ENNReal.ofReal universalConstant + defect ≤ area :=
  S.universal_ennreal_add_of_odd_boundary_degree_obstruction
    (hasOddBoundaryDegreeObstruction_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      e hboundaryMap)
    hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains under the exact topological interface: an odd boundary-degree
obstruction and the global Jacobian budget. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
      j boundary hobstruction (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface.  This is the certificate-level handoff for future arbitrary
surface constructions. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    N area boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    G hG hboundary K hGLipschitz hbudget


/-- The finite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area D.homeomorph D.boundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData D.models)
    G hG hboundary K hGLipschitz hbudget

theorem finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary' t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    G hG hboundary K hGLipschitz hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary extends continuously across the standard closed disk. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
      j boundary F hF hboundaryExtension (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism and explicit checkerboard cylinder-strip data. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    N area boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    G hG hboundary K hGLipschitz hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
      j boundary e hboundaryHomeomorph (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-disk boundary by
a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
      j boundary e hboundaryHomeomorph (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The same finite planar certificate follows directly from a nullhomotopy
of the boundary loop. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
      j boundary center F hF0 hF1 (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
under the exact topological interface: an odd boundary-degree obstruction and
uniform global Jacobian budgets over all finite truncations. -/
theorem universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_odd_boundary_degree_obstruction
    N area boundary hobstruction G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary' t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph hmodels G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary' t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    N area D G hG hboundary K hGLipschitz hbudget

theorem universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary' t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_cylinderStripGlued_data
    N area e hboundaryHomeomorph hmodels G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary extends continuously across the standard closed disk. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_extension
    N area boundary F hF hboundaryExtension G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with the standard closed-disk boundary by a
homeomorphism and explicit checkerboard cylinder-strip data. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    N area boundary e hboundaryHomeomorph hmodels G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph
    N area boundary e hboundaryHomeomorph G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with the standard closed-disk boundary by a
homeomorphism. This is the direct-extension route. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    N area boundary e hboundaryHomeomorph G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary loop is nullhomotopic. -/
theorem universal_ennreal_of_complex_planar_maps_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_nullhomotopy
    N area boundary center F hF0 hF1 G hG hboundary K hGLipschitz hbudget

/-- Planar Lemma 5.4 for the genuine metric distance-profile map.  All
boundary, continuity, and Lipschitz inputs are discharged internally. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map under the exact topological interface: an odd boundary-degree obstruction
on the planar boundary. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary') :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    (givensMetricFourierMap_lipschitzWith hboundary' N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary') :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary'
    (hasOddBoundaryDegreeObstruction_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary' N j)
    (continuous_givensMetricFourierMap hboundary' N j)
    (givensMetricFourierMap_on_boundary hboundary' j)
    (givensMetricFourierMap_lipschitzWith hboundary' N j)


/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary') :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume :=
  givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j D.homeomorph D.boundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData D.models)
    hboundary'

theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary') :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume :=
  givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    hboundary'

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary') :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume :=
  exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j D.homeomorph D.boundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData D.models)
    hboundary'

theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    {N : ℕ} (j : Fin N)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary') :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume :=
  exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    hboundary'

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary extends continuously across the standard closed disk. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied by explicit
checkerboard cylinder-strip data. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by
a homeomorphism and the odd boundary-degree obstruction is supplied by
explicit checkerboard cylinder-strip data. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  let _ : CompactSpace ℂ := Homeomorph.compactSpace e
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary
    (hasOddBoundaryDegreeObstruction_of_closedUnitDisk_homeomorph_cylinderStrip_data
      e hboundaryHomeomorph hmodels)
    (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary loop is nullhomotopic in the source plane. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric
Fourier map.  It produces an open connected neighborhood of the origin whose
volume is controlled by the global complex Jacobian integral. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian
    j boundary hfine (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary extends continuously across the standard closed disk. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary loop is nullhomotopic in the source plane. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_nullhomotopy
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- The complete finite planar certificate for the actual metric Fourier
family.  Its sole analytic input is their common Jacobian budget. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
        j boundary hboundary hfine
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family.
The hypothesis is now exactly the common Jacobian budget, uniformly over
all finite truncations. -/
theorem universal_ennreal_of_metric_complex_planar_maps
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map
    N area boundary hboundary hfine (hbudget N)

/-- Once the Bessel estimate is known for the unmixed genuine Fourier
coordinates, full Givens orthogonality and Rademacher automatically give
the integrated unit Jacobian budget on every measurable planar set. -/
theorem sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (s : Set ℂ) (hs : MeasurableSet s)
    (henergy : ∀ᵐ x ∂volume.restrict s,
      (∑ k : Fin N, complexDerivativeEnergy
        (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2) :
    (∑ j : Fin N, ∫⁻ x in s, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        volume s := by
  have hmixed : ∀ᵐ x ∂volume.restrict s,
      (∑ j : Fin N, complexDerivativeEnergy
        (fderiv ℝ (givensMetricFourierMap boundary N j) x)) ≤ 2 := by
    have hsum : ∀ᵐ x ∂volume.restrict s,
        (∑ j : Fin N, complexDerivativeEnergy
          (fderiv ℝ (givensMetricFourierMap boundary N j) x)) =
          ∑ k : Fin N, complexDerivativeEnergy
            (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x) :=
      ae_restrict_of_ae
        (ae_sum_complexDerivativeEnergy_fderiv_givensMetricFourierMap
          hboundary N)
    filter_upwards [hsum, henergy] with x hsumx hex
    rw [hsumx]
    exact hex
  exact sum_lintegral_abs_det_fderiv_restrict_le_volume
    (fun j ↦ givensMetricFourierMap boundary N j) s hs hmixed

/-- The sharp pointwise Jacobian defect bound integrates to an additive area budget on any measurable planar domain. -/
theorem sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (s : Set ℂ) (hs : MeasurableSet s) :
    (∑ j : Fin N, ∫⁻ x in s, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
        ∫⁻ x in s, ENNReal.ofReal
          (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤
        volume s := by
  refine sum_lintegral_abs_det_fderiv_add_lintegral_ofReal_defect_restrict_le_volume
    (fun j ↦ givensMetricFourierMap boundary N j) s hs
    (distanceSlackDerivativeEnergyDefect boundary)
    (measurable_distanceSlackDerivativeEnergyDefect hboundary)
    (distanceSlackDerivativeEnergyDefect_nonneg boundary) ?_
  exact ae_restrict_of_ae
    (ae_sum_abs_det_fderiv_givensMetricFourierMap_add_distanceSlackDerivativeEnergyDefect_le_one
      hboundary N)

/-- Finite slack-refined planar certificate derived internally from the sharp Jacobian defect budget. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_coordinateEnergy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian
    j boundary hboundary hfine

/-- Infinite slack-refined planar certificate derived from the finite additive
slack-defect certificates. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_coordinateEnergy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_coordinateEnergy
      N area boundary hboundary hfine harea

/-- Finite slack-refined planar certificate under the exact topological
interface: an odd boundary-degree obstruction on the planar boundary. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
    j boundary hobstruction hboundary

/-- Infinite slack-refined planar certificate under the exact topological
interface: an odd boundary-degree obstruction on the planar boundary. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
      N area boundary hobstruction hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with a compact source carrying the quotient-friendly directed abstract
arbitrarily-fine polygonal-model interface. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary' hboundary' N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph hmodels hboundary'

/-- Infinite slack-refined planar certificate when the boundary is identified
with a compact source carrying the quotient-friendly directed abstract
arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      N area e hboundaryHomeomorph hmodels hboundary' harea


/-- Finite slack-refined planar certificate when the boundary is identified
with a compact source carrying the bundled homeomorphism-plus-glued-strip
interface. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area :=
  finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area D.homeomorph D.boundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData D.models)
    hboundary' harea

theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area :=
  finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    hboundary' harea

/-- Infinite slack-refined planar certificate when the boundary is identified
with a compact source carrying the bundled homeomorphism-plus-glued-strip
interface. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_cylinderStripGluedArbitrarilyFineData
      N area D hboundary' harea

theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary' x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_cylinderStripGlued_data
      N area e hboundaryHomeomorph hmodels hboundary' harea

/-- Finite slack-refined planar certificate when the boundary extends across
the standard closed disk. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
    j boundary F hF hboundaryExtension hboundary

/-- Infinite slack-refined planar certificate when the boundary extends across
the standard closed disk. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_extension
      N area boundary F hF hboundaryExtension hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
    j boundary e hboundaryHomeomorph hboundary

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
    j boundary e hboundaryHomeomorph hboundary

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
      N area boundary e hboundaryHomeomorph hboundary harea

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-disk boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary harea

/-- Finite slack-refined planar certificate when the boundary loop is
nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
    j boundary center F hF0 hF1 hboundary

/-- Infinite slack-refined planar certificate when the boundary loop is
nullhomotopic in the source plane. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_nullhomotopy
      N area boundary center F hF0 hF1 hboundary harea

/-- The complete finite planar certificate for the actual metric Fourier
family under the exact topological interface: an odd boundary-degree
obstruction on the planar boundary. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_odd_boundary_degree_obstruction
        j boundary hobstruction hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family
under the exact topological interface: an odd boundary-degree obstruction on
 the planar boundary. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    N area boundary hobstruction hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with a compact source carrying the
quotient-friendly directed abstract arbitrarily-fine polygonal-model
interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
        j e hboundaryHomeomorph hmodels hboundary'
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph hmodels hboundary' (hbudget N)


/-- The complete finite planar certificate for the actual metric Fourier family
when the boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area D.homeomorph D.boundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGluedArbitrarilyFineData D.models)
    hboundary' hbudget

theorem finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    hboundary' hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_cylinderStripGluedArbitrarilyFineData
      N area D hboundary' (hbudget N)

theorem universal_ennreal_of_metric_complex_planar_maps_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary' N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_cylinderStripGlued_data
      N area e hboundaryHomeomorph hmodels hboundary' (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary extends continuously across the standard closed
 disk. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_extension
        j boundary F hF hboundaryExtension hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary extends continuously across the standard closed disk. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    N area boundary F hF hboundaryExtension hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism and the odd boundary-degree obstruction is supplied by
explicit checkerboard cylinder-strip data. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_cylinderStrip_data
        j boundary e hboundaryHomeomorph hmodels hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with the standard closed-disk boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied by explicit
checkerboard cylinder-strip data. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_cylinderStrip_data
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ, ∃ _hm : 0 < m,
      ∃ _hedgeFaceCount : ∀ e : CylinderStripEdge n m,
        (Finset.univ.filter fun f ↦ e ∈ cylinderStripFaceEdges f).card =
          if e ∈ cylinderStripBoundaryEdges (n := n) (m := m) then 1 else 2,
      ∃ faceCenter : CylinderStripFace n m → ClosedUnitInterval × UnitAddCircle,
      ∀ (f : CylinderStripFace n m) (edge : CylinderStripEdge n m),
        edge ∈ cylinderStripFaceEdges f → ∀ x : ClosedUnitInterval,
          dist (faceCenter f)
            (match edge with
              | .radial i j => cylinderRadialEdgePath n m i j x
              | .angular i j => cylinderAngularEdgePath n m i j x) < ε)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_cylinderStrip_data
    N area boundary e hboundaryHomeomorph hmodels hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph
        j boundary e hboundaryHomeomorph hboundary
  · exact hbudget

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-disk boundary
by a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitDisk_homeomorph_direct
        j boundary e hboundaryHomeomorph hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary is identified with the standard closed-disk boundary by a
 homeomorphism. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary is identified with the standard closed-disk boundary by a
 homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary loop is nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_nullhomotopy
        j boundary center F hF0 hF1 hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary loop is nullhomotopic in the source plane. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    N area boundary center F hF0 hF1 hboundary (hbudget N)

/-- The finite planar certificate for the actual metric Fourier family with
the Jacobian budget derived internally from the coordinate-energy bound. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map
    N (volume (Set.univ : Set ℂ)) boundary hboundary hfine ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar conclusion for the actual metric Fourier family,
with each finite Jacobian budget derived internally from the corresponding
coordinate-energy bound. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hboundary : IsometricCircleBoundary boundary)
    (hfine : HasFinePolygonalModels boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy
    N area boundary hboundary hfine (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_odd_boundary_degree_obstruction
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_odd_boundary_degree_obstruction
    N (volume (Set.univ : Set ℂ)) boundary hobstruction hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget under the
exact topological interface: an odd boundary-degree obstruction on the planar
boundary. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_odd_boundary_degree_obstruction
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (hobstruction : HasOddBoundaryDegreeObstruction boundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_odd_boundary_degree_obstruction
      N area boundary hobstruction hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N (volume (Set.univ : Set ℂ)) e hboundaryHomeomorph hmodels hboundary' ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary' hboundary' N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the quotient-friendly
directed abstract arbitrarily-fine polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels boundary)
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
      N area e hboundaryHomeomorph hmodels hboundary' (hbudget N) harea


/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    N (volume (Set.univ : Set ℂ)) D hboundary' ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary' hboundary' N Set.univ MeasurableSet.univ hbudget'

theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (N : ℕ) (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    (hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_of_cylinderStripGlued_data
      hmodels)
    hboundary' hbudget harea

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with a compact source carrying the bundled
homeomorphism-plus-glued-strip interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_homeomorph_cylinderStripGluedArbitrarilyFineData
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (D : HomeomorphCylinderStripGluedArbitrarilyFineData boundary boundary')
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_cylinderStripGluedArbitrarilyFineData
      N area D hboundary' (hbudget N) harea

theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_homeomorph_cylinderStripGlued_data
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (area : ℝ≥0∞)
    {boundary : UnitAddCircle → X} {boundary' : UnitAddCircle → ℂ}
    (e : X ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary' = e ∘ boundary)
    (hmodels : ∀ ε : ℝ, 0 < ε → ∃ n m : ℕ,
      ∃ P : CylinderStripLowerBoundaryPairing m,
      ∃ _hm : 0 < m,
      ∃ vertexPoint : CylinderStripGluedVertex n P → X,
      ∃ edgeToX : CylinderStripGluedEdge n P → ClosedUnitInterval → X,
      ∃ _hedgeToX : ∀ e, Continuous (edgeToX e),
      ∃ _hedgeStart : ∀ e, edgeToX e closedUnitIntervalStart =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).1,
      ∃ _hedgeFinish : ∀ e, edgeToX e closedUnitIntervalFinish =
        vertexPoint (cylinderStripGluedEdgeChosenEnds n P e).2,
      ∃ faceCenter : CylinderStripFace n m → X,
        (∀ (f : CylinderStripFace n m) (e : CylinderStripGluedEdge n P),
          e ∈ cylinderStripGluedFaceEdges n P f → ∀ x : ClosedUnitInterval,
            dist (faceCenter f) (edgeToX e x) < ε) ∧
        (∀ k x,
          edgeToX (cylinderStripGluedBoundaryEdge n P k) x =
            boundary ((angularSubdivisionParameter m k x : ℝ) : UnitAddCircle)))
    (hboundary' : IsometricCircleBoundary boundary')
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary' (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_cylinderStripGlued_data
      N area e hboundaryHomeomorph hmodels hboundary' (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed disk. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_extension
    N (volume (Set.univ : Set ℂ)) boundary F hF hboundaryExtension hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed disk. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitDisk → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_extension
      N area boundary F hF hboundaryExtension hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph
    N (volume (Set.univ : Set ℂ)) boundary e hboundaryHomeomorph hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitDisk_homeomorph_direct
    N (volume (Set.univ : Set ℂ)) boundary e hboundaryHomeomorph hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_homeomorph
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-disk boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitDisk ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitDiskBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitDisk_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary loop is nullhomotopic in the source plane. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_nullhomotopy
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_nullhomotopy
    N (volume (Set.univ : Set ℂ)) boundary center F hF0 hF1 hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary loop is nullhomotopic in the source plane. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_nullhomotopy
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (center : ℂ)
    (F : C(I × UnitAddCircle, ℂ))
    (hF0 : ∀ t : UnitAddCircle, F (0, t) = center)
    (hF1 : ∀ t : UnitAddCircle, F (1, t) = boundary t)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_nullhomotopy
      N area boundary center F hF0 hF1 hboundary (hbudget N) harea


/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary extends continuously across the standard closed square. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_extension
      j boundary F hF hboundaryExtension (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-square boundary by
 a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x,
      ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume)
  · intro j
    exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
      j boundary e hboundaryHomeomorph (G j) (hG j) (hboundary j) (hGLipschitz j)
  · exact hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary extends continuously across the standard closed square. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_extension
    N area boundary F hF hboundaryExtension G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with the standard closed-square boundary by a
homeomorphism. This is the direct-extension route. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_direct
    N area boundary e hboundaryHomeomorph G hG hboundary K hGLipschitz hbudget

/-- The finite orientation-free Fourier certificate for complex-plane
domains whose boundary is identified with the standard closed-square boundary by
a homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (G : Fin N → ℂ → ℂ)
    (hG : ∀ j, Continuous (G j))
    (hboundary : ∀ j t,
      G j (boundary t) = givensBoundaryCurveAddCircle j t)
    (K : Fin N → ℝ≥0)
    (hGLipschitz : ∀ j, LipschitzWith (K j) (G j))
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    G hG hboundary K hGLipschitz hbudget

/-- Infinite orientation-free Fourier certificate for complex-plane domains
whose boundary is identified with the standard closed-square boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hfinite : ∀ N : ℕ,
      ∃ G : Fin N → ℂ → ℂ,
        (∀ j, Continuous (G j)) ∧
        (∀ j t, G j (boundary t) = givensBoundaryCurveAddCircle j t) ∧
        ∃ K : Fin N → ℝ≥0,
          (∀ j, LipschitzWith (K j) (G j)) ∧
          (∑ j : Fin N,
            ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (G j) x).det| ∂volume) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  rcases hfinite N with ⟨G, hG, hboundary, K, hGLipschitz, hbudget⟩
  exact
    finite_universal_ennreal_of_complex_planar_maps_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      N area boundary e hboundaryHomeomorph G hG hboundary K hGLipschitz hbudget

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary extends continuously across the standard closed square. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-square boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact givens_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary extends continuously across the standard closed square. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitSquare_extension
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitSquare_extension
    j boundary F hF hboundaryExtension (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-square boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume := by
  exact exists_givens_bounded_region_volume_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
    j boundary e hboundaryHomeomorph (givensMetricFourierMap boundary N j)
    (continuous_givensMetricFourierMap hboundary N j)
    (givensMetricFourierMap_on_boundary hboundary j)
    (givensMetricFourierMap_lipschitzWith hboundary N j)

/-- Planar Lemma 5.4 for the genuine metric distance-profile map when the
boundary is identified with the standard closed-square boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ENNReal.ofReal (mixedBoundaryArea (givensMatrix N) j) ≤
      ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume :=
  givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary

/-- Bounded-region form of planar Lemma 5.4 for the genuine metric Fourier
map when the boundary is identified with the standard closed-square boundary by
a homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    {N : ℕ} (j : Fin N)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary) :
    ∃ region : Set ℂ,
      IsOpen region ∧ IsConnected region ∧
      Bornology.IsBounded region ∧ 0 ∈ region ∧
      volume region ≤
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume :=
  exists_givensMetricFourierMap_bounded_region_volume_le_complex_jacobian_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    j e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary

/-- Finite slack-refined planar certificate when the boundary extends across
the standard closed square. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitSquare_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_extension
    j boundary F hF hboundaryExtension hboundary

/-- Infinite slack-refined planar certificate when the boundary extends across
the standard closed square. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitSquare_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitSquare_extension
      N area boundary F hF hboundaryExtension hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-square boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  let defectMass : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume
  have hbudget :
      (∑ j : Fin N, ∫⁻ x, ENNReal.ofReal
        |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) +
          defectMass ≤ volume (Set.univ : Set ℂ) := by
    simpa [defectMass, Measure.restrict_univ] using
      sum_lintegral_givensMetricFourierMap_add_lintegral_distanceSlackDerivativeEnergyDefect_le_volume
        boundary hboundary N Set.univ MeasurableSet.univ
  refine (finite_universal_ennreal_of_givens_coverage_budget_add N
    (volume (Set.univ : Set ℂ)) defectMass
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ?_ hbudget).trans harea
  intro j
  exact givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
    j boundary e hboundaryHomeomorph hboundary

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-square boundary by a homeomorphism.  This is the
direct-extension route. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitSquare_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates_add
  intro N
  exact
    finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary harea

/-- Finite slack-refined planar certificate when the boundary is identified
with the standard closed-square boundary by a homeomorphism and the odd
boundary-degree obstruction is supplied through the quotient-friendly directed
polygonal-model interface. -/
theorem finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area :=
  finite_universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary harea

/-- Infinite slack-refined planar certificate when the boundary is identified
with the standard closed-square boundary by a homeomorphism and the odd
boundary-degree obstruction is supplied through the quotient-friendly directed
polygonal-model interface. -/
theorem universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant +
      ∫⁻ x, ENNReal.ofReal (distanceSlackDerivativeEnergyDefect boundary x) ∂volume ≤ area :=
  universal_ennreal_add_lintegral_distanceSlackDerivativeEnergyDefect_of_metric_complex_planar_maps_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    area e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary harea

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary extends continuously across the standard closed
square. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_extension
        j boundary F hF hboundaryExtension hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary extends continuously across the standard closed square. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitSquare_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_extension
    N area boundary F hF hboundaryExtension hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-square boundary
by a homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  apply finite_universal_ennreal_of_givens_coverage_budget N area
    (fun j ↦ ∫⁻ x, ENNReal.ofReal
      |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume)
  · exact fun j ↦
      givensMetricFourierMap_mixedBoundaryArea_le_complex_jacobian_of_closedUnitSquare_homeomorph_direct
        j boundary e hboundaryHomeomorph hboundary
  · exact hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
 the boundary is identified with the standard closed-square boundary by a
 homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitSquare_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_direct
    N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- The complete finite planar certificate for the actual metric Fourier
family when the boundary is identified with the standard closed-square boundary
by a homeomorphism and the odd boundary-degree obstruction is supplied through
the quotient-friendly directed polygonal-model interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_metric_complex_planar_map_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary hbudget

/-- Infinite-mode planar conclusion for the actual metric Fourier family when
the boundary is identified with the standard closed-square boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      (∑ j : Fin N,
        ∫⁻ x, ENNReal.ofReal
          |(fderiv ℝ (givensMetricFourierMap boundary N j) x).det| ∂volume) ≤
        area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      N area boundary e hboundaryHomeomorph hboundary (hbudget N)

/-- The finite planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed square. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_extension
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_extension
    N (volume (Set.univ : Set ℂ)) boundary F hF hboundaryExtension hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary extends continuously across the standard closed square. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitSquare_extension
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (F : ClosedUnitSquare → ℂ) (hF : Continuous F)
    (hboundaryExtension : boundary = F ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_extension
      N area boundary F hF hboundaryExtension hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-square boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_homeomorph_direct
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area := by
  have hbudget' :
      ∀ᵐ x ∂volume.restrict (Set.univ : Set ℂ),
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2 :=
    ae_restrict_of_ae hbudget
  refine (finite_universal_ennreal_of_metric_complex_planar_map_of_closedUnitSquare_homeomorph_direct
    N (volume (Set.univ : Set ℂ)) boundary e hboundaryHomeomorph hboundary ?_).trans harea
  simpa only [Measure.restrict_univ] using
    sum_lintegral_givensMetricFourierMap_le_volume_of_coordinateEnergy
      boundary hboundary N Set.univ MeasurableSet.univ hbudget'

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-square boundary by a
homeomorphism.  This is the direct-extension route. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitSquare_homeomorph_direct
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_homeomorph_direct
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

/-- The finite planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-square boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (N : ℕ) (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget :
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal (finiteUniversalConstant N) ≤ area :=
  finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_homeomorph_abstractVariableDirectedQuotientArbitrarilyFine
    N area e hboundaryHomeomorph
    hasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels_closedUnitSquareBoundary
    hboundary hbudget harea

/-- Infinite-mode planar certificate with coordinate-energy budget when the
boundary is identified with the standard closed-square boundary by a
homeomorphism and the odd boundary-degree obstruction is supplied through the
quotient-friendly directed polygonal-model interface. -/
theorem universal_ennreal_of_metric_complex_planar_maps_of_coordinateEnergy_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
    (area : ℝ≥0∞)
    (boundary : UnitAddCircle → ℂ)
    (e : ClosedUnitSquare ≃ₜ ℂ)
    (hboundaryHomeomorph : boundary = e ∘ closedUnitSquareBoundary)
    (hboundary : IsometricCircleBoundary boundary)
    (hbudget : ∀ N : ℕ,
      ∀ᵐ x ∂volume,
        (∑ k : Fin N, complexDerivativeEnergy
          (fderiv ℝ (oddProfileFourierMap boundary (oddMode k)) x)) ≤ 2)
    (harea : volume (Set.univ : Set ℂ) ≤ area) :
    ENNReal.ofReal universalConstant ≤ area := by
  apply universal_ennreal_bound_of_finite_certificates
  intro N
  exact
    finite_universal_ennreal_of_metric_complex_planar_map_of_coordinateEnergy_of_closedUnitSquare_homeomorph_abstractVariableDirectedQuotient
      N area boundary e hboundaryHomeomorph hboundary (hbudget N) harea

end

end GromovFilling
