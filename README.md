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
- the algebraic/numerical conclusions of the orientation-free and oriented
  certificates at their stated geometric interfaces.

## Not yet end-to-end

Lemma 5.4 is **not yet fully formalized**. Its finite-mesh topological
contradiction is assembled without auxiliary lift or turn assumptions, but
the passage from an arbitrary compact surface to that finite data still
needs:

1. a theorem furnishing the required arbitrarily fine finite
   triangulation/cell structure for every compact surface with one boundary
   component and identifying its boundary subcomplex with the cyclic
   subdivision already constructed in Lean;
2. a Jordan separation theorem identifying the proved bounded nonzero-degree
   component with the bounded component of the Jordan complement; and
3. the two-dimensional Lipschitz area formula giving
   `∫ J₂ G ≥ |Ω|` from coverage.

Consequently, the headline theorems in `GromovFilling/Certificates.lean`
remain conditional on their geometric coverage/Jacobian or
Stokes/comass interfaces. They must not be described as end-to-end proofs
of the two results in the note until those interfaces are discharged.
