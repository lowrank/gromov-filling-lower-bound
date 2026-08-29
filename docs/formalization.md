# Formalization boundary

The repository separates kernel-verified mathematics from manuscript claims
that still depend on unavailable foundations. The complete 27-item
manuscript ledger is maintained in
[`FORMALIZATION.md`](https://github.com/lowrank/conj-gromov-filling/blob/main/FORMALIZATION.md).

## Verified layers

| Layer | Representative content |
|---|---|
| Fourier algebra | triangle-wave coefficients, Fourier areas, odd-mode series |
| Linear algebra | Givens entries, orthogonality, energy preservation, dominance |
| Boundary topology | circle degree, degree one, Jordan partition, bounded component |
| Finite surface topology | mod-2 cochain obstruction, face lifts, edge turns, general side pairings |
| Compact-surface topology | Radó finite boundary-regular triangulation and faithful polygonal classification for half-space-modeled compact connected surfaces |
| Planar analysis | Lipschitz area inequality, determinant identity, Jacobian budgets |
| Certificate logic | finite-to-infinite universal deduction, defect propagation, scalar optimization |
| Rigorous numerics | rational bounds for `π`, `ζ(3)`, and the displayed constants |
| Logarithmic sine kernel | squared-sine gap, positive sine quotient, strict off-diagonal positivity, symmetry |
| Finite one-high-leg algebra | odd high-mode witness, exact resonance matrix, Gram positivity, Rayleigh ceiling |
| Resonance trace arithmetic | nonnegative double-series summability, Tonelli/antidiagonal regrouping, exact scalar value |
| De Sitter profile algebra | quadric membership, formal-velocity speed, pairwise Lorentz product, Züst kernel identity |

Proposition 8.1 is partial. `PositiveLogSineKernel.lean` verifies the exact
elementary kernel inequality on `0 < t, s < π` with `t ≠ s`. The last
hypothesis is essential: the Fourier series and logarithmic expression are
singular on the diagonal, even though Lean's real division and logarithm are
totalized there. The infinite-series identity, integrability passage, and
scalar and Hilbert-valued optimization remain open.

Proposition 15.1 is verified at an explicit denominator interface:
`DeSitterProfile.lean` takes profile values and the derivative value as scalars
and requires the relevant sine denominators to be nonzero. It does not claim a
separate almost-everywhere differentiability theorem for arbitrary Lipschitz
profiles.

Lemma 14.1 and Theorem 14.2 are partial at a precise analytic interface.
`OneHighLeg.lean` proves that the explicit odd mode `m = 2J+1` is unit norm
and anti-periodic, computes its occupied-coordinate symplectic cost exactly,
defines the displayed finite resonance matrix and boundary series, proves
their quadratic-form identity and weighted-Gram positivity, and derives the
finite Rayleigh ceiling. What remains is to identify the modeled output
coordinates with the derivative of the full normalized nonlinear deformation
on its infinite coefficient space and to connect the exhibited plane to the
global ambient comass.

Lemma 14.3 is partial. `ResonanceTrace.lean` proves convergence of the
manuscript's nonnegative scalar double series, its Tonelli/antidiagonal
reindexing, and its exact value `π/2 + 7ζ(3)/π + π³/24`. It does not
construct the infinite matrix on ℓ², prove Gram positivity or trace class, or
identify the scalar series with an operator trace.

## General polygon-side pairings

`GromovFilling.GeneralSurfaceObstruction` proves that every circle-valued map
on a glued-strip point quotient has even degree on the glued lower loop. The
proof pairs integer edge turns under an arbitrary fixed-point-free involution.
Preserving pairs agree; reversing pairs differ by sign; both cancel modulo two.

Consequently, the free boundary has the odd-degree obstruction for every
polygon schema, and the existing continuous-map and homeomorphism interfaces
derive their lower obstruction automatically.

`GromovFilling.CircleDegree` now also proves existence and multiplicativity of
the lift-defined degree.  Applying multiplicativity to a circle homeomorphism
and its inverse shows that every circle homeomorphism has degree `1` or `-1`.
Thus the odd-degree obstruction is invariant under arbitrary
circle-homeomorphic boundary reparametrization.

The theorem
`hasOddBoundaryDegreeObstruction_of_exists_homeomorph_cylinderStripGluedPointBoundary_pairing_reparametrized`
states the relaxed classification handoff without asking the caller to supply
an obstruction or preserve a chosen parameter pointwise. It needs an arbitrary
side pairing, a surface homeomorphism, and any circle homeomorphism relating
the schema's free loop to the supplied boundary. The remaining Lemma 5.4
topology task is to produce this boundary-component-preserving existential
presentation from the compact connected one-boundary manifold hypotheses.

`GromovFilling.NormalFormBoundaryObstruction` now proves the canonical target
of that presentation. It enumerates every side except the unique free `h`
side, constructs the induced fixed-point-free involutive pairing, verifies the
carrier quotient identifications, and applies the arbitrary-pairing parity
theorem. A disk homotopy and circle reversal then give the odd boundary-degree
obstruction for the free loop in every orientable one-boundary normal form and
every admissible nonorientable one-boundary normal form.

`GromovFilling.SurfaceTriangulationFoundation` now supplies the preceding
finite-triangulability step unconditionally. It imports a pinned,
Lean-4.29-compatible Radó source closure and proves
`exists_full_support_boundary_facewise_regular_partial_triangulation`. The
returned finite complex covers the surface, has edge valence at most two, and
meets the ambient boundary facewise. The unique cyclic boundary component
still has to be extracted before the relaxed handoff applies.

`GromovFilling.SurfaceClassificationFoundation` also exposes the vendored
classification theorem. Every compact connected surface under the same
half-space-manifold hypotheses is homeomorphic to the sphere or to a faithful
orientable or nonorientable polygonal normal-form quotient. This removes the
absolute classification gap, and the designated canonical free loop now has
the required obstruction.

`GromovFilling.BoundaryLocusClassification` strengthens the entire
finite-cyclic normalization chain at the realization level. It defines the
polygonal boundary locus as the quotient image of exactly the once-used
sides, proves that signed and unoriented relabelings and every P1/P2 move
preserve that locus in both directions, and composes the result through the
Gallier--Xu normalizer. Thus the normal-form homeomorphism now preserves the
complete combinatorial boundary locus.

`GromovFilling.CanonicalBoundaryLocus` closes the other end of this relative
chain. It classifies every once-used side of the canonical presentations as a
free `h` side, computes the final adapter on those sides, and proves equality
between the image of the full polygonal boundary locus and the raw quotient's
full free-side locus. With one boundary block this set is exactly the range of
the orientable or nonorientable canonical obstruction loop. What remains is to
identify the Radó realization's once-used-side locus with the ambient manifold
boundary, use the supplied one-component parametrization to force one
canonical boundary block, and identify the parametrization with that loop up
to a circle homeomorphism. That geometric endpoint statement is still
required for Lemma 5.4.

## Partial headline statements

The finite universal certificate and the nonlinear oriented certificate are
kernel-verified deductions from named geometric inputs. The following bridges
are not yet verified for every compact Riemannian surface:

- identification of the supplied one-boundary parametrization with the unique
  free loop in the verified polygonal normal form;
- almost-everywhere eikonal differentiation and weak parameter integration;
- intrinsic area measure and chartwise Jacobian globalization;
- the global differential-form Stokes/comass inequality.

!!! danger "No conditional-shell upgrade"
    These bridges are not declared as project axioms. Until they have kernel
    proofs, the project does not describe the two manuscript headlines as
    end-to-end Lean theorems.

## Open feasible manuscript obligations

Several later finite or algebraic manuscript claims remain suitable for future
formalization, including completion of the separable barrier, Hardy
stationarity, the stationary-resonance hierarchy, the operator layer of the
exact-trace lemma, and the one-high-leg spectral ceiling. Their current status
is recorded individually in the root statement ledger.
