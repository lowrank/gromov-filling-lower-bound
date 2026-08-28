# Gromov filling-area formalization

Lean formalization accompanying
`fourier_resonant_filling_area_v3.tex`. The project is pinned to Lean
4.29.0 and mathlib 4.29.0. The Jordan separation input is pinned to the
EPFL LARA `JordanCurveTheorem` package at commit `e442525`.

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
- the metric odd-distance profile itself: antipodal identities,
  nonnegative slack, vanishing boundary slack, Lipschitz estimates, fixed
  Fourier-coordinate maps, and the derived boundary formula
  `z_n(γ(s)) = -4/(πn²) exp(ins)` for every positive odd mode;
- the explicit Givens mixing matrix, its full orthogonality identity
  (including the off-diagonal column products), its energy identities,
  and rowwise dominant-harmonic inequalities;
- injectivity of every mixed boundary curve;
- an integer circle degree defined by real lifts, including uniqueness,
  additivity, its multiplicative complex-circle form, and the exact turn
  sum on every finite cyclic subdivision of the boundary;
- degree `+1` of every mixed boundary curve, proved by explicitly
  factoring the dominant first harmonic and controlling the correction;
- the fact that each mixed boundary image is a compact topological Jordan
  curve, exhibited by a homeomorphism between its range and the circle;
  the imported formal Jordan curve theorem supplies its two open connected
  complementary regions, and Lean transports that theorem to `ℂ`, selects
  the region containing the origin, identifies it with the bounded
  degree-one component, and proves it is covered;
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
- a map-independent `HasArbitrarilyFinePolygonalModels` interface and the
  compact uniform-continuity argument converting its geometric mesh bound
  into the half-turn mesh needed for every continuous circle-valued map;
- a quotient-friendly directed abstract polygonal-model interface,
  omitting face-vertex injectivity so it applies to quotient cell
  structures with repeated face vertices after gluing, together with its
  arbitrarily-fine, compact-map, and homeomorphism transport theorems, the
  resulting odd boundary-degree obstruction, a bundled explicit
  `HasCylinderStripGluedArbitrarilyFineData` mesh-data interface for the
  glued-strip quotient input, and downstream coverage and certificate wrappers from that
  bundled interface;
- the resulting coverage implication: an odd radial boundary degree forces
  the puncture into the extension image, hence every point in the bounded
  nonzero-degree component of a mixed Givens curve is covered;
- direct nullhomotopy invariance of circle degree through covering-space
  lifting, yielding the odd-degree obstruction for the standard square and
  disk boundaries and therefore direct coverage, Jacobian, and certificate
  wrappers for every compact source whose boundary either extends
  continuously across the closed disk or is identified with it by a
  homeomorphism;
- compact-source transport for the fine-polygonal-model interface: a
  geometric polygonal model can be pushed forward along a continuous map,
  `HasArbitrarilyFinePolygonalModels` transfers across compact continuous
  maps and in particular across homeomorphisms, and the resulting
  homeomorphism-level wrappers now feed both the odd-degree obstruction and
  the topological coverage theorems directly;
- the genuine Lipschitz planar area inequality on measurable subsets of
  both `Fin 2 → ℝ` and `ℂ`, derived from Rademacher's theorem, null-image
  control for the exceptional set, and mathlib's Jacobian image bound;
  for a complex-plane domain it is composed directly with the Jordan
  coverage theorem to bound the covered region by the Jacobian integral,
  the same local inequality now glues across finitely many open planar
  pieces both for one global map and for families of chartwise local maps,
  those finite and infinite local-map certificate interfaces are bundled,
  a source-side finite/infinite chart-certificate interface converts
  abstract chart data into that planar certificate layer, and an
  obstruction-level variant now generates the Jordan witness regions
  automatically from the mixed boundary curves, and the corresponding
  source-side metric-chart interface now feeds that certificate layer
  directly for the genuine mixed Fourier maps, and both the generic
  source-chart and metric source-chart interfaces now have topologically
  neutral versions separating the chart data from the odd-degree
  obstruction, with direct wrappers from nullhomotopies, from the
  quotient-friendly and stronger directed abstract arbitrarily-fine
  polygonal-model interfaces, and through homeomorphism transport from
  future compact-surface triangulation theorems stated at those polygonal
  interfaces, and the same local, source-chart, and metric source-chart
  layers now also carry a common additive defect term unchanged at
  both the finite and bundled infinite-system levels, and
  the metric source-chart interface now has the same closed-disk,
  closed-square, and disk-homeomorphism topological wrappers as the
  older whole-plane certificate theorems;
- the exact identification of mathlib's real determinant on `ℂ` with the
  elementary planar Jacobian, its finite-sum integrated `ENNReal` form,
  and the passage from a Hilbert--Schmidt derivative-energy bound to a
  unit Jacobian budget on measurable planar sets;
- exact boundary values, continuity, global Lipschitz bounds, almost-
  everywhere differentiability, and orthogonal derivative-energy
  preservation for the genuine metric-defined odd Fourier coordinates and
  their Givens mixtures;
- the finite Fourier--Bessel estimate needed to convert the coordinate
  derivative fields into the common energy bound for those genuine metric
  Fourier maps;
- injective polynomial fillings of the mixed Givens boundary curves,
  identification of their open-disk image with the Jordan region at the
  origin, and equality of that region's area with the explicit Fourier/
  Green expression;
- planar `ENNReal` certificates which internally compose Jordan coverage,
  exact region area, and the Jacobian budget for both abstract planar maps
  and the genuine metric Fourier maps;
- the algebraic/numerical conclusions of the orientation-free and oriented
  certificates at their stated geometric interfaces;
- fixed-endpoint path-homotopy invariance of closed `1`-form curve
  integrals, together with the free-loop equal-side cancellation criterion
  for square homotopies, the induced `UnitAddCircle` loop and circle
  nullhomotopy wrappers, the direct closed-disk extension and
  closed-disk-homeomorphism vanishing theorems, and the resulting
  nullhomotopic-loop vanishing statement, packaged at a reusable Euclidean
  chart-level interface for the future oriented Stokes/comass argument;
- the explicit square-center directed polygonal-model construction on the
  closed square and closed disk boundaries, together with transfer of that
  directed arbitrarily-fine interface to every compact metric boundary
  homeomorphic to the closed disk and the resulting direct coverage,
  Jacobian, and certificate wrappers.

## Not yet end-to-end

Lemma 5.4 is **not yet fully formalized**. Its finite-mesh topological
contradiction is assembled without auxiliary lift or turn assumptions, but
the passage from an arbitrary compact surface to that finite data still
needs:

1. a theorem proving the needed topological obstruction for every compact
   surface with one boundary component beyond the already formalized disk-like
   case.  The strongest currently packaged route uses either a direct
   surface-level odd-degree argument, or a theorem furnishing arbitrarily fine
   finite triangulations/cell structures at some bundled polygonal-model
   interface.  The quotient-friendly directed interface
   `HasAbstractVariableDirectedQuotientArbitrarilyFinePolygonalModels` is now
   formalized for cell decompositions where face vertices may repeat after
   gluing, it already transports across compact continuous maps and
   homeomorphisms, and it now also has a bundled explicit
   `HasCylinderStripGluedArbitrarilyFineData` source interface whose
   coverage- and certificate-level wrappers are formalized. Its homeomorphism-level wrappers
   now reach the planar coverage, Jacobian, slack-defect, and certificate
   statements.  The stronger directed interface
   `HasAbstractVariableDirectedArbitrarilyFinePolygonalModels` and the
   undirected interfaces `HasArbitrarilyFinePolygonalModels` /
   `HasFinePolygonalModels` are also formalized and still suffice when
   available.  The compact
   uniform-continuity passage from these geometric statements to the odd
   boundary-degree obstruction is formalized, and the disk-homeomorphic case is
   discharged directly and also at the directed abstract polygonal-model
   interface;
2. the weak differentiation-under-the-boundary-parameter-integral theorem
   for the metric Fourier coordinates and its Bessel estimate in the full
   surface setting.  The downstream planar Fourier/Jacobian/certificate
   assembly after that estimate is now formalized;
3. globalization of the proved Lipschitz planar area inequality through
   Riemannian surface charts, including intrinsic surface area and
   identification of the coordinate determinant density with `J₂ G`;
4. in the oriented argument, construction of the global differential-form
   interface supplying the Stokes/comass inequality on a Riemannian
   surface.

Consequently, the headline theorems in `GromovFilling/Certificates.lean`
remain conditional on their geometric coverage/Jacobian or
Stokes/comass interfaces. They must not be described as end-to-end proofs
of the two results in the note until those interfaces are discharged.
