# Gromov filling-area formalization

Lean formalization accompanying
`fourier_resonant_filling_area_v3.tex`. The project is pinned to Lean
4.12.0 and mathlib 4.12.0.

## Verification

```text
lake build
rg -n "\b(sorry|admit|axiom|unsafe)\b" --glob '*.lean' \
  GromovFilling GromovFilling.lean
```

The build succeeds. The second command returns no matches. GitHub Actions
runs both checks on every push and pull request.

## Formalized

- exact Fourier coefficients, Green boundary action, and finite Fourier
  area calculations;
- the explicit Givens mixing matrix, its orthogonality/energy identities,
  and rowwise dominant-harmonic inequalities;
- injectivity of every mixed boundary curve;
- an integer circle degree defined by real lifts, including uniqueness,
  additivity, its multiplicative complex-circle form, and the exact turn
  sum on every finite cyclic subdivision of the boundary;
- degree `+1` of every mixed boundary curve, proved by explicitly
  factoring the dominant first harmonic and controlling the correction;
- the fact that each mixed boundary image is a compact topological Jordan
  curve, exhibited by a homeomorphism between its range and the circle;
  given a Jordan partition, Lean identifies the region containing the
  origin with the bounded degree-one component and proves it is covered;
- local constancy of radial degree in the puncture, constancy on connected
  complement components, degree zero at infinity, and boundedness of the
  nonzero-degree origin component;
- the finite mod-2 cochain/Stokes obstruction, continuous local circle
  phases away from facewise cuts, and the compactness estimate that makes
  such cuts available below one uniform mesh size;
- the assembled finite-polygonal form of Lemma 5.4's contradiction: from
  ordinary one-face/two-face incidence, cyclic face and boundary data, an
  odd-degree boundary map, and a half-turn mesh estimate, Lean constructs
  the cuts, all real lifts and integer edge turns, proves the exact signed
  boundary-turn identity, and derives the mod-2 contradiction;
- a bundled `HasFinePolygonalModels` surface interface which reduces the
  remaining topological input to constructing one compatible fine finite
  model for each continuous circle-valued map;
- the resulting coverage implication: an odd radial boundary degree forces
  the puncture into the extension image, hence every point in the bounded
  nonzero-degree component of a mixed Givens curve is covered;
- the genuine Lipschitz planar area inequality on measurable subsets of
  both `Fin 2 → ℝ` and `ℂ`, derived from Rademacher's theorem, null-image
  control for the exceptional set, and mathlib's Jacobian image bound;
  for a complex-plane domain it is composed directly with the Jordan
  coverage theorem to bound the covered region by the Jacobian integral;
- the algebraic/numerical conclusions of the orientation-free and oriented
  certificates at their stated geometric interfaces.

## Not yet end-to-end

Lemma 5.4 is **not yet fully formalized**. Its finite-mesh topological
contradiction is assembled without auxiliary lift or turn assumptions, but
the passage from an arbitrary compact surface to that finite data still
needs:

1. a theorem proving `HasFinePolygonalModels` for every compact surface
   with one boundary component—equivalently, furnishing the required fine
   finite triangulation/cell structure and its compatible cyclic boundary
   subdivision;
2. a Jordan separation theorem supplying the two open connected regions
   for this topological Jordan curve (their identification with the proved
   bounded/nonzero-degree component is already formalized); and
3. globalization of the proved Lipschitz planar area inequality through
   Riemannian surface charts, including identification of the coordinate
   determinant density with the intrinsic `J₂ G`.

Consequently, the headline theorems in `GromovFilling/Certificates.lean`
remain conditional on their geometric coverage/Jacobian or
Stokes/comass interfaces. They must not be described as end-to-end proofs
of the two results in the note until those interfaces are discharged.
