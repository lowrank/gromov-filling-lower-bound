# Revised Section 4

The statement of record for this update is `main2.tex` at Overleaf commit
`85c9eb9`. Theorem 1.2 states `Area(M) > 5.40154`; Theorem 4.1 gives the
all-parameter bound for every `0 ≤ λ < π² / 32`. Its numerical specialization
uses `λ = 1/25`. The source SHA-256 is `d6ec5c17e00be87d174cd730e2dd84b6c65881b3f36d4ab99abd0fb0dd556249`. The table below records the current labels and pages; the receipt identifies the exact Lean source.

The change is the first-variation coefficient. The boundary action and the
constants `Dstar` and `Qstar` are unchanged. The first component of the mixed
correlation cancels. The resulting Cauchy–Schwarz estimate has coefficient one
and uses the profile tail starting at frequency five. The capped weight-25
ellipse estimate then gives `sharpenedCstar`:

$$
C_* = \sqrt{2}\left(\frac{16}{\pi^2}
+\frac{8}{5\pi}\sqrt{2-\frac{16}{\pi^2}}\right).
$$

| Current manuscript item | Status | Formal endpoint or scope |
|---|---|---|
| Theorem 1.2, p. 2 | Verified | `riemannianSurfaceArea_gt_one_div_twenty_five_of_conventionally_oriented_isometric_filling`: the strict `5.40154` surface-area bound. |
| Theorem 4.1, p. 12 | Verified | `riemannianSharpenedNonlinearCertificate_le_surfaceArea_of_conventionally_oriented_isometric_filling`: the complete revised all-parameter formula. |
| Lemma 4.2, p. 13 | Partially verified | Existing coefficient and derivative-energy estimates; `oddProfileFourierMap_first_add_twenty_five_infiniteTailEnergy_le_two` adds the shorter profile tail. The standalone Hilbert-valued differentiability statement is not asserted by this update. |
| Proposition 4.3, p. 14 | Partially verified | Existing `boundaryActionSeries_eq` and finite controlled-atlas Stokes, followed by the integrated finite-to-infinite certificate. There is no new standalone Hilbert-valued surface-integral API. |
| Lemma 4.4, p. 16 | Partially verified | Existing finite differential/correlation identity, convergence to `infiniteResonantFirstVariation`, positive-saturation stationarity and orientation reversal. The cancelled mixed-correlation identity is explicit in `infiniteOddMixedCorrelation_eq_tail`. |
| Proposition 4.5, p. 17 | Partially verified | `abs_infiniteResonantFirstVariation_fourierCoeffOn_le_sharpenedCstar_Dstar`, with the genuine profile hypotheses supplied internally in the surface proof. |
| Lemma 4.6, p. 19 | Partially verified | Existing `abs_finiteTruncationResonantQuadraticVariation_le_Qstar`; the quadratic estimate is unchanged. The surface deduction uses these finite bounds and a vanishing truncation error. |
| Proposition 4.7, p. 19 | Partially verified | `abs_infiniteResonantDensity_fourierCoeffOn_le_sharpenedComassBound` and the coherent finite-density limit. This is the pointwise Fourier/comass content used by the surface theorem, without introducing a general Hilbert-valued differential-form API. |
| Numerical specialization, p. 19 | Partially verified | `sharpenedNonlinearCertificate_one_div_twenty_five_gt` proves the strict lower enclosure `5.401544 < B(1/25)/C(1/25)` by rational arithmetic. The displayed upper enclosure `5.401545` is not used or claimed by this certificate. |

Here “partially verified” identifies a finite-coordinate or Fourier core, or only one side of the displayed numerical interval. It does not assert the broader standalone Hilbert-space formulation. These broader formulations are not hypotheses of the final surface results.

The final surface statements have exactly the geometric assumptions of the
earlier endpoints: a compact connected smooth Riemannian surface modeled on
the two-dimensional half-space, a circle isometry parametrizing the full
boundary, and `RiemannianSurfaceOrientation`. They add no tail, correlation,
Stokes, comass, atlas, or area-conclusion hypothesis. Lean derives those data.
The proof uses coherent finite Fourier truncations; separate broader
Hilbert-space formulations are outside the formal claim.

The earlier `nonlinearCertificate` and the strict `λ = 0.03` theorem remain
available under their original names. They describe the previous estimate,
not the updated Theorems 1.2 and 4.1. Historical receipts remain evidence for
those earlier source versions only.

Lean CI [34167476132](https://github.com/lowrank/gromov-filling-lower-bound/actions/runs/34167476132) on `bdf0d050ee1d375d7025645c7a2ff22b9a2dd16b` passed the full package build and live axiom audit. The audit accepted 6,762 declarations under `GromovFilling`, using only `propext`, `Classical.choice`, and `Quot.sound`.
