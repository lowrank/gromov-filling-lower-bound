import GromovFilling.FiniteSymplecticWeakStokes

/-!
# Localized planar weak Stokes

This file develops the compactly supported cutoff identities needed to glue
the planar Lipschitz weak-Stokes theorem over an oriented surface atlas.
-/

open Filter Function MeasureTheory
open scoped BigOperators NNReal

namespace GromovFilling

noncomputable section

/-- Multiplying a globally Lipschitz scalar function by a compactly supported
globally Lipschitz cutoff again gives a globally Lipschitz function. -/
theorem exists_lipschitzWith_mul_of_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ u : E → ℝ} {Cρ Cu : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρCompact : HasCompactSupport ρ)
    (hu : LipschitzWith Cu u) :
    ∃ C, LipschitzWith C (fun x ↦ ρ x * u x) := by
  obtain ⟨Bρ, hBρ⟩ :=
    hρ.continuous.bounded_above_of_compact_support hρCompact
  obtain ⟨Bu, hBu⟩ :=
    hρCompact.isCompact.exists_bound_of_continuousOn hu.continuous.continuousOn
  let L : ℝ := |Bρ| * (Cu : ℝ) + |Bu| * (Cρ : ℝ)
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  refine ⟨Real.toNNReal L, LipschitzWith.of_dist_le' ?_⟩
  have hbound (x y : E) (hx : x ∈ tsupport ρ) :
      dist (ρ x * u x) (ρ y * u y) ≤ L * dist x y := by
    have hρy : |ρ y| ≤ |Bρ| := by
      exact (le_trans (by simpa [Real.norm_eq_abs] using hBρ y) (le_abs_self Bρ))
    have hux : |u x| ≤ |Bu| := by
      exact (le_trans (by simpa [Real.norm_eq_abs] using hBu x hx) (le_abs_self Bu))
    have huDist : |u x - u y| ≤ (Cu : ℝ) * dist x y := by
      simpa [Real.dist_eq] using hu.dist_le_mul x y
    have hρDist : |ρ x - ρ y| ≤ (Cρ : ℝ) * dist x y := by
      simpa [Real.dist_eq] using hρ.dist_le_mul x y
    rw [Real.dist_eq]
    calc
      |ρ x * u x - ρ y * u y| =
          |ρ y * (u x - u y) + u x * (ρ x - ρ y)| := by ring_nf
      _ ≤ |ρ y * (u x - u y)| + |u x * (ρ x - ρ y)| := abs_add_le _ _
      _ = |ρ y| * |u x - u y| + |u x| * |ρ x - ρ y| := by
        rw [abs_mul, abs_mul]
      _ ≤ |Bρ| * ((Cu : ℝ) * dist x y) +
          |Bu| * ((Cρ : ℝ) * dist x y) := by
        gcongr
      _ = L * dist x y := by
        dsimp only [L]
        ring
  intro x y
  by_cases hx : x ∈ tsupport ρ
  · exact hbound x y hx
  · by_cases hy : y ∈ tsupport ρ
    · rw [dist_comm (ρ x * u x) (ρ y * u y), dist_comm x y]
      exact hbound y x hy
    · have hρx : ρ x = 0 := by
        exact Classical.not_not.mp (fun hne ↦ hx (subset_tsupport ρ hne))
      have hρy : ρ y = 0 := by
        exact Classical.not_not.mp (fun hne ↦ hy (subset_tsupport ρ hne))
      simpa [hρx, hρy] using mul_nonneg hL (dist_nonneg : 0 ≤ dist x y)

/-- The ordinary product rule expressed with Rademacher line derivatives at
a point where both scalar factors are Fréchet differentiable. -/
theorem lineDeriv_mul_eq_of_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x q : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    lineDeriv ℝ (fun y ↦ f y * g y) x q =
      f x * lineDeriv ℝ g x q + g x * lineDeriv ℝ f x q := by
  have hmul := hf.hasFDerivAt.mul hg.hasFDerivAt
  have hline := (hmul.hasLineDerivAt q).lineDeriv
  simpa only [Pi.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    hf.lineDeriv_eq_fderiv, hg.lineDeriv_eq_fderiv] using hline

/-- The line-derivative product rule holds almost everywhere for a smooth
factor and a globally Lipschitz scalar factor. -/
theorem ae_lineDeriv_mul_eq_of_differentiable_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {f g : E → ℝ} {C : ℝ≥0}
    (hf : Differentiable ℝ f) (hg : LipschitzWith C g) (q : E) :
    ∀ᵐ x ∂mu, lineDeriv ℝ (fun y ↦ f y * g y) x q =
      f x * lineDeriv ℝ g x q + g x * lineDeriv ℝ f x q := by
  filter_upwards [hg.ae_differentiableAt (μ := mu)] with x hx
  exact lineDeriv_mul_eq_of_differentiableAt (hf x) hx

/-- A compactly supported continuous scalar can multiply two bounded
Rademacher line derivatives without losing integrability. -/
theorem integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu]
    {ρ u v : E → ℝ} {Cu Cv : ℝ≥0}
    (hρ : Continuous ρ) (hρCompact : HasCompactSupport ρ)
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v) (p q : E) :
    Integrable (fun x ↦
      ρ x * lineDeriv ℝ u x p * lineDeriv ℝ v x q) mu := by
  have hρInt : Integrable ρ mu :=
    hρ.integrable_of_hasCompactSupport hρCompact
  have hρu : Integrable (ρ * fun x ↦ lineDeriv ℝ u x p) mu :=
    hρInt.mul_of_top_left (hu.memLp_lineDeriv (μ := mu) p)
  have hρuv :=
    hρu.mul_of_top_left (hv.memLp_lineDeriv (μ := mu) q)
  simpa only [Pi.mul_apply, mul_assoc] using hρuv

/-- If the middle line derivative comes from a compactly supported Lipschitz
function, it localizes an otherwise unbounded continuous first factor. -/
theorem integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsFiniteMeasureOnCompacts mu]
    {a b c : E → ℝ} {Cb Cc : ℝ≥0}
    (ha : Continuous a) (hb : LipschitzWith Cb b)
    (hbCompact : HasCompactSupport b) (hc : LipschitzWith Cc c)
    (p q : E) :
    Integrable (fun x ↦
      a x * lineDeriv ℝ b x p * lineDeriv ℝ c x q) mu := by
  obtain ⟨Ba, hBa⟩ :=
    hbCompact.isCompact.exists_bound_of_continuousOn ha.continuousOn
  let A : ℝ := |Ba| * ((Cb : ℝ) * ‖p‖) * ((Cc : ℝ) * ‖q‖)
  let bound : E → ℝ := (tsupport b).indicator (fun _ ↦ A)
  have hBoundIntegrable : Integrable bound mu := by
    change Integrable ((tsupport b).indicator (fun _ : E ↦ A)) mu
    rw [integrable_indicator_iff hbCompact.isCompact.measurableSet]
    exact integrableOn_const hbCompact.isCompact.measure_lt_top.ne
  have hMeasurable : AEStronglyMeasurable
      (fun x ↦ a x * lineDeriv ℝ b x p * lineDeriv ℝ c x q) mu :=
    (ha.aestronglyMeasurable.mul
      (aestronglyMeasurable_lineDeriv hb.continuous mu)).mul
      (aestronglyMeasurable_lineDeriv hc.continuous mu)
  apply hBoundIntegrable.mono' hMeasurable
  filter_upwards with x
  by_cases hx : x ∈ tsupport b
  · change ‖a x * lineDeriv ℝ b x p * lineDeriv ℝ c x q‖ ≤
      (tsupport b).indicator (fun _ : E ↦ A) x
    rw [Set.indicator_of_mem hx, norm_mul, norm_mul]
    dsimp only [A]
    gcongr
    · exact (hBa x hx).trans (le_abs_self Ba)
    · exact (norm_lineDeriv_le_of_lipschitz ℝ hb :
        ‖lineDeriv ℝ b x p‖ ≤ (Cb : ℝ) * ‖p‖)
    · exact (norm_lineDeriv_le_of_lipschitz ℝ hc :
        ‖lineDeriv ℝ c x q‖ ≤ (Cc : ℝ) * ‖q‖)
  · change ‖a x * lineDeriv ℝ b x p * lineDeriv ℝ c x q‖ ≤
      (tsupport b).indicator (fun _ : E ↦ A) x
    rw [Set.indicator_of_notMem hx,
      lineDeriv_eq_zero_of_not_mem_tsupport x p hx,
      mul_zero, zero_mul, norm_zero]

/-- Localized planar weak Stokes. A compactly supported differentiable
Lipschitz cutoff moves the weak Jacobian onto its own differential. This is
the form whose error terms cancel after summing a partition of unity. -/
theorem integral_cutoff_mul_lipschitz_jacobian_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {ρ u v : E → ℝ} {Cρ Cu Cv : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρDiff : Differentiable ℝ ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (p q : E) :
    (∫ x : E, ρ x *
      (lineDeriv ℝ u x p * lineDeriv ℝ v x q -
        lineDeriv ℝ u x q * lineDeriv ℝ v x p) ∂mu) =
      ∫ x : E, v x *
        (lineDeriv ℝ ρ x p * lineDeriv ℝ u x q -
          lineDeriv ℝ ρ x q * lineDeriv ℝ u x p) ∂mu := by
  obtain ⟨Cρv, hρv⟩ :=
    exists_lipschitzWith_mul_of_hasCompactSupport hρ hρCompact hv
  have hρvCompact : HasCompactSupport (fun x ↦ ρ x * v x) := by
    simpa only [Pi.mul_apply] using hρCompact.mul_right (f' := v)
  have hzero := integral_lipschitz_lipschitz_jacobian_eq_zero
    mu hu hρv hρvCompact p q
  have hprodP :=
    ae_lineDeriv_mul_eq_of_differentiable_lipschitzWith mu hρDiff hv p
  have hprodQ :=
    ae_lineDeriv_mul_eq_of_differentiable_lipschitzWith mu hρDiff hv q
  have hlocalizedZero :
      (∫ x : E,
        ρ x *
            (lineDeriv ℝ u x p * lineDeriv ℝ v x q -
              lineDeriv ℝ u x q * lineDeriv ℝ v x p) -
          v x *
            (lineDeriv ℝ ρ x p * lineDeriv ℝ u x q -
              lineDeriv ℝ ρ x q * lineDeriv ℝ u x p) ∂mu) = 0 := by
    calc
      _ = ∫ x : E,
          lineDeriv ℝ u x p * lineDeriv ℝ (fun y ↦ ρ y * v y) x q -
            lineDeriv ℝ u x q * lineDeriv ℝ (fun y ↦ ρ y * v y) x p ∂mu := by
        apply integral_congr_ae
        filter_upwards [hprodP, hprodQ] with x hxP hxQ
        rw [hxP, hxQ]
        ring
      _ = 0 := hzero
  have hLeftPQ :=
    integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      mu hρ.continuous hρCompact hu hv p q
  have hLeftQP :=
    integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      mu hρ.continuous hρCompact hu hv q p
  have hLeft : Integrable (fun x : E ↦
      ρ x *
        (lineDeriv ℝ u x p * lineDeriv ℝ v x q -
          lineDeriv ℝ u x q * lineDeriv ℝ v x p)) mu := by
    simpa only [mul_sub, mul_assoc] using hLeftPQ.sub hLeftQP
  have hRightPQ :=
    integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hv.continuous hρ hρCompact hu p q
  have hRightQP :=
    integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hv.continuous hρ hρCompact hu q p
  have hRight : Integrable (fun x : E ↦
      v x *
        (lineDeriv ℝ ρ x p * lineDeriv ℝ u x q -
          lineDeriv ℝ ρ x q * lineDeriv ℝ u x p)) mu := by
    simpa only [mul_sub, mul_assoc] using hRightPQ.sub hRightQP
  rw [integral_sub hLeft hRight] at hlocalizedZero
  exact sub_eq_zero.mp hlocalizedZero

/-- Symmetric localized weak Stokes. The right side is the cutoff derivative
paired with the standard antisymmetric primitive, including its exact factor
of one half. -/
theorem integral_cutoff_mul_lipschitz_jacobian_eq_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {ρ u v : E → ℝ} {Cρ Cu Cv : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρDiff : Differentiable ℝ ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : LipschitzWith Cu u) (hv : LipschitzWith Cv v)
    (p q : E) :
    (∫ x : E, ρ x *
      (lineDeriv ℝ u x p * lineDeriv ℝ v x q -
        lineDeriv ℝ u x q * lineDeriv ℝ v x p) ∂mu) =
      ∫ x : E, (1 / 2 : ℝ) *
        (v x *
            (lineDeriv ℝ ρ x p * lineDeriv ℝ u x q -
              lineDeriv ℝ ρ x q * lineDeriv ℝ u x p) -
          u x *
            (lineDeriv ℝ ρ x p * lineDeriv ℝ v x q -
              lineDeriv ℝ ρ x q * lineDeriv ℝ v x p)) ∂mu := by
  let A : E → ℝ := fun x ↦ ρ x *
    (lineDeriv ℝ u x p * lineDeriv ℝ v x q -
      lineDeriv ℝ u x q * lineDeriv ℝ v x p)
  let B : E → ℝ := fun x ↦ v x *
    (lineDeriv ℝ ρ x p * lineDeriv ℝ u x q -
      lineDeriv ℝ ρ x q * lineDeriv ℝ u x p)
  let D : E → ℝ := fun x ↦ u x *
    (lineDeriv ℝ ρ x p * lineDeriv ℝ v x q -
      lineDeriv ℝ ρ x q * lineDeriv ℝ v x p)
  have hAB : ∫ x : E, A x ∂mu = ∫ x : E, B x ∂mu := by
    exact integral_cutoff_mul_lipschitz_jacobian_eq
      mu hρ hρDiff hρCompact hu hv p q
  have hSwap := integral_cutoff_mul_lipschitz_jacobian_eq
    mu hρ hρDiff hρCompact hv hu p q
  have hNegAD : -(∫ x : E, A x ∂mu) = ∫ x : E, D x ∂mu := by
    calc
      -(∫ x : E, A x ∂mu) = ∫ x : E, -A x ∂mu := by
        rw [integral_neg]
      _ = ∫ x : E, ρ x *
          (lineDeriv ℝ v x p * lineDeriv ℝ u x q -
            lineDeriv ℝ v x q * lineDeriv ℝ u x p) ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [A]
        ring
      _ = ∫ x : E, D x ∂mu := hSwap
  have hB : Integrable B mu := by
    have hPQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hv.continuous hρ hρCompact hu p q
    have hQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hv.continuous hρ hρCompact hu q p
    simpa only [B, mul_sub, mul_assoc] using hPQ.sub hQP
  have hD : Integrable D mu := by
    have hPQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hu.continuous hρ hρCompact hv p q
    have hQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu hu.continuous hρ hρCompact hv q p
    simpa only [D, mul_sub, mul_assoc] using hPQ.sub hQP
  change (∫ x : E, A x ∂mu) =
    ∫ x : E, (1 / 2 : ℝ) * (B x - D x) ∂mu
  calc
    (∫ x : E, A x ∂mu) =
        (1 / 2 : ℝ) * ((∫ x : E, B x ∂mu) - ∫ x : E, D x ∂mu) := by
      linarith
    _ = ∫ x : E, (1 / 2 : ℝ) * (B x - D x) ∂mu := by
      rw [integral_const_mul, integral_sub hB hD]

/-- Pointwise coordinate expansion of the cutoff derivative paired with the
standard symplectic primitive. -/
theorem cutoffSymplecticPrimitiveError_eq_sum
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (ρ : E → ℝ) (F : E → ι → ℂ) (x p q : E) :
    lineDeriv ℝ ρ x q *
          standardComplexSymplecticPrimitive
            (F x) (finiteComplexWeakLineDerivative F x p) -
        lineDeriv ℝ ρ x p *
          standardComplexSymplecticPrimitive
            (F x) (finiteComplexWeakLineDerivative F x q) =
      ∑ i : ι, (1 / 2 : ℝ) *
        ((F x i).im *
            (lineDeriv ℝ ρ x p *
                lineDeriv ℝ (fun y ↦ (F y i).re) x q -
              lineDeriv ℝ ρ x q *
                lineDeriv ℝ (fun y ↦ (F y i).re) x p) -
          (F x i).re *
            (lineDeriv ℝ ρ x p *
                lineDeriv ℝ (fun y ↦ (F y i).im) x q -
              lineDeriv ℝ ρ x q *
                lineDeriv ℝ (fun y ↦ (F y i).im) x p)) := by
  rw [standardComplexSymplecticPrimitive_apply,
    standardComplexSymplecticPrimitive_apply]
  unfold standardComplexSymplectic finiteComplexWeakLineDerivative
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A finite complex map's real coordinate inherits its Lipschitz constant. -/
theorem lipschitzWith_complex_re_coordinate
    {E ι : Type*} [PseudoEMetricSpace E] [Fintype ι]
    {F : E → ι → ℂ} {C : ℝ≥0} (hF : LipschitzWith C F) (i : ι) :
    LipschitzWith C (fun x ↦ (F x i).re) := by
  simpa only [Function.comp_apply, one_mul] using
    (RCLike.lipschitzWith_re (K := ℂ)).comp
      ((LipschitzWith.eval i).comp hF)

/-- A finite complex map's imaginary coordinate inherits its Lipschitz
constant. -/
theorem lipschitzWith_complex_im_coordinate
    {E ι : Type*} [PseudoEMetricSpace E] [Fintype ι]
    {F : E → ι → ℂ} {C : ℝ≥0} (hF : LipschitzWith C F) (i : ι) :
    LipschitzWith C (fun x ↦ (F x i).im) := by
  simpa only [Function.comp_apply, one_mul] using
    (RCLike.lipschitzWith_im (K := ℂ)).comp
      ((LipschitzWith.eval i).comp hF)

/-- Finite-complex localized weak Stokes in the exact primitive form needed
for oriented chart gluing. -/
theorem integral_cutoff_mul_standardComplexSymplectic_weak_eq
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Fintype ι] (mu : Measure E) [mu.IsAddHaarMeasure]
    {ρ : E → ℝ} {F : E → ι → ℂ} {Cρ CF : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρDiff : Differentiable ℝ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F)
    (p q : E) :
    (∫ x : E, ρ x *
        standardComplexSymplectic
          (finiteComplexWeakLineDerivative F x p)
          (finiteComplexWeakLineDerivative F x q) ∂mu) =
      ∫ x : E,
        lineDeriv ℝ ρ x q *
            standardComplexSymplecticPrimitive
              (F x) (finiteComplexWeakLineDerivative F x p) -
          lineDeriv ℝ ρ x p *
            standardComplexSymplecticPrimitive
              (F x) (finiteComplexWeakLineDerivative F x q) ∂mu := by
  have hRe (i : ι) := lipschitzWith_complex_re_coordinate hF i
  have hIm (i : ι) := lipschitzWith_complex_im_coordinate hF i
  have hLeftIntegrable (i : ι) : Integrable (fun x : E ↦
      ρ x *
        (lineDeriv ℝ (fun y ↦ (F y i).re) x p *
            lineDeriv ℝ (fun y ↦ (F y i).im) x q -
          lineDeriv ℝ (fun y ↦ (F y i).re) x q *
            lineDeriv ℝ (fun y ↦ (F y i).im) x p)) mu := by
    have hPQ := integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      mu hρ.continuous hρCompact (hRe i) (hIm i) p q
    have hQP := integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
      mu hρ.continuous hρCompact (hRe i) (hIm i) q p
    simpa only [mul_sub, mul_assoc] using hPQ.sub hQP
  have hRightIntegrable (i : ι) : Integrable (fun x : E ↦
      (1 / 2 : ℝ) *
        ((F x i).im *
            (lineDeriv ℝ ρ x p *
                lineDeriv ℝ (fun y ↦ (F y i).re) x q -
              lineDeriv ℝ ρ x q *
                lineDeriv ℝ (fun y ↦ (F y i).re) x p) -
          (F x i).re *
            (lineDeriv ℝ ρ x p *
                lineDeriv ℝ (fun y ↦ (F y i).im) x q -
              lineDeriv ℝ ρ x q *
                lineDeriv ℝ (fun y ↦ (F y i).im) x p))) mu := by
    have hImPQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu (hIm i).continuous hρ hρCompact (hRe i) p q
    have hImQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu (hIm i).continuous hρ hρCompact (hRe i) q p
    have hRePQ := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu (hRe i).continuous hρ hρCompact (hIm i) p q
    have hReQP := integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
      mu (hRe i).continuous hρ hρCompact (hIm i) q p
    simpa only [Pi.sub_apply, mul_sub, mul_assoc] using
      ((hImPQ.sub hImQP).sub (hRePQ.sub hReQP)).const_mul (1 / 2 : ℝ)
  calc
    (∫ x : E, ρ x *
        standardComplexSymplectic
          (finiteComplexWeakLineDerivative F x p)
          (finiteComplexWeakLineDerivative F x q) ∂mu) =
        ∫ x : E, ∑ i : ι, ρ x *
          (lineDeriv ℝ (fun y ↦ (F y i).re) x p *
              lineDeriv ℝ (fun y ↦ (F y i).im) x q -
            lineDeriv ℝ (fun y ↦ (F y i).re) x q *
              lineDeriv ℝ (fun y ↦ (F y i).im) x p) ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [standardComplexSymplectic_finiteComplexWeakLineDerivative,
        Finset.mul_sum]
    _ = ∑ i : ι, ∫ x : E, ρ x *
          (lineDeriv ℝ (fun y ↦ (F y i).re) x p *
              lineDeriv ℝ (fun y ↦ (F y i).im) x q -
            lineDeriv ℝ (fun y ↦ (F y i).re) x q *
              lineDeriv ℝ (fun y ↦ (F y i).im) x p) ∂mu := by
      rw [integral_finset_sum Finset.univ]
      intro i _
      exact hLeftIntegrable i
    _ = ∑ i : ι, ∫ x : E, (1 / 2 : ℝ) *
          ((F x i).im *
              (lineDeriv ℝ ρ x p *
                  lineDeriv ℝ (fun y ↦ (F y i).re) x q -
                lineDeriv ℝ ρ x q *
                  lineDeriv ℝ (fun y ↦ (F y i).re) x p) -
            (F x i).re *
              (lineDeriv ℝ ρ x p *
                  lineDeriv ℝ (fun y ↦ (F y i).im) x q -
                lineDeriv ℝ ρ x q *
                  lineDeriv ℝ (fun y ↦ (F y i).im) x p)) ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_cutoff_mul_lipschitz_jacobian_eq_symmetric
        mu hρ hρDiff hρCompact (hRe i) (hIm i) p q
    _ = ∫ x : E, ∑ i : ι, (1 / 2 : ℝ) *
          ((F x i).im *
              (lineDeriv ℝ ρ x p *
                  lineDeriv ℝ (fun y ↦ (F y i).re) x q -
                lineDeriv ℝ ρ x q *
                  lineDeriv ℝ (fun y ↦ (F y i).re) x p) -
            (F x i).re *
              (lineDeriv ℝ ρ x p *
                  lineDeriv ℝ (fun y ↦ (F y i).im) x q -
                lineDeriv ℝ ρ x q *
                  lineDeriv ℝ (fun y ↦ (F y i).im) x p)) ∂mu := by
      symm
      rw [integral_finset_sum Finset.univ]
      intro i _
      exact hRightIntegrable i
    _ = ∫ x : E,
          lineDeriv ℝ ρ x q *
              standardComplexSymplecticPrimitive
                (F x) (finiteComplexWeakLineDerivative F x p) -
            lineDeriv ℝ ρ x p *
              standardComplexSymplecticPrimitive
                (F x) (finiteComplexWeakLineDerivative F x q) ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      exact (cutoffSymplecticPrimitiveError_eq_sum ρ F x p q).symm

/-- The localized finite-complex identity in Fréchet-derivative form, ready
for the signed chart-density change-of-variables theorem. -/
theorem integral_cutoff_mul_standardComplexSymplectic_fderiv_eq
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Fintype ι] (mu : Measure E) [mu.IsAddHaarMeasure]
    {ρ : E → ℝ} {F : E → ι → ℂ} {Cρ CF : ℝ≥0}
    (hρ : LipschitzWith Cρ ρ) (hρDiff : Differentiable ℝ ρ)
    (hρCompact : HasCompactSupport ρ) (hF : LipschitzWith CF F)
    (p q : E) :
    (∫ x : E, ρ x *
        standardComplexSymplectic
          ((fderiv ℝ F x) p) ((fderiv ℝ F x) q) ∂mu) =
      ∫ x : E,
        (fderiv ℝ ρ x) q *
            standardComplexSymplecticPrimitive (F x) ((fderiv ℝ F x) p) -
          (fderiv ℝ ρ x) p *
            standardComplexSymplecticPrimitive (F x) ((fderiv ℝ F x) q) ∂mu := by
  calc
    (∫ x : E, ρ x *
        standardComplexSymplectic
          ((fderiv ℝ F x) p) ((fderiv ℝ F x) q) ∂mu) =
        ∫ x : E, ρ x *
          standardComplexSymplectic
            (finiteComplexWeakLineDerivative F x p)
            (finiteComplexWeakLineDerivative F x q) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hF.ae_differentiableAt (μ := mu)] with x hx
      rw [finiteComplexWeakLineDerivative_eq_lineDeriv F hx p,
        finiteComplexWeakLineDerivative_eq_lineDeriv F hx q,
        hx.lineDeriv_eq_fderiv, hx.lineDeriv_eq_fderiv]
    _ = ∫ x : E,
          lineDeriv ℝ ρ x q *
              standardComplexSymplecticPrimitive
                (F x) (finiteComplexWeakLineDerivative F x p) -
            lineDeriv ℝ ρ x p *
              standardComplexSymplecticPrimitive
                (F x) (finiteComplexWeakLineDerivative F x q) ∂mu :=
      integral_cutoff_mul_standardComplexSymplectic_weak_eq
        mu hρ hρDiff hρCompact hF p q
    _ = ∫ x : E,
          (fderiv ℝ ρ x) q *
              standardComplexSymplecticPrimitive (F x) ((fderiv ℝ F x) p) -
            (fderiv ℝ ρ x) p *
              standardComplexSymplecticPrimitive (F x) ((fderiv ℝ F x) q) ∂mu := by
      apply integral_congr_ae
      filter_upwards [hF.ae_differentiableAt (μ := mu)] with x hx
      rw [(hρDiff x).lineDeriv_eq_fderiv (v := q),
        (hρDiff x).lineDeriv_eq_fderiv (v := p),
        finiteComplexWeakLineDerivative_eq_lineDeriv F hx p,
        finiteComplexWeakLineDerivative_eq_lineDeriv F hx q,
        hx.lineDeriv_eq_fderiv, hx.lineDeriv_eq_fderiv]

#print axioms exists_lipschitzWith_mul_of_hasCompactSupport
#print axioms lineDeriv_mul_eq_of_differentiableAt
#print axioms ae_lineDeriv_mul_eq_of_differentiable_lipschitzWith
#print axioms integrable_compactlySupported_mul_lineDeriv_mul_lineDeriv
#print axioms integrable_mul_lineDeriv_mul_lineDeriv_of_compact_middle
#print axioms integral_cutoff_mul_lipschitz_jacobian_eq
#print axioms integral_cutoff_mul_lipschitz_jacobian_eq_symmetric
#print axioms cutoffSymplecticPrimitiveError_eq_sum
#print axioms lipschitzWith_complex_re_coordinate
#print axioms lipschitzWith_complex_im_coordinate
#print axioms integral_cutoff_mul_standardComplexSymplectic_weak_eq
#print axioms integral_cutoff_mul_standardComplexSymplectic_fderiv_eq

end

end GromovFilling
