# Mathematical architecture

The formal development turns metric boundary data into explicit planar
certificates. Its strongest unconditional statements are finite, algebraic,
topological, and planar. The final passage to arbitrary Riemannian surfaces is
tracked separately.

<div class="research-hero" markdown>
![Fourier modes passing through an orthogonal mixing lattice to a Jordan region](assets/fourier-architecture.webp)
</div>

<div class="proof-flow">
  <div><strong>Distance profiles</strong><span>Boundary distances produce odd Fourier coordinates with exact boundary values.</span></div>
  <div><strong>Orthogonal mixing</strong><span>Explicit Givens rotations preserve energy and force first-harmonic dominance.</span></div>
  <div><strong>Jordan coverage</strong><span>Degree and mod-2 obstruction force the bounded Jordan region into the image.</span></div>
  <div><strong>Area certificate</strong><span>Planar Jacobian budgets and exact boundary area yield finite and asymptotic bounds.</span></div>
</div>

## Boundary distance profiles

For a boundary parametrization `γ`, the metric profile records the distance
from an interior point to every boundary point. Its odd Fourier modes have
exact boundary values

```text
z_n(γ(s)) = -4 / (π n²) exp(i n s),   n positive and odd.
```

The Lean development proves the triangle-wave coefficients, continuity,
global Lipschitz bounds, planar weak differentiation, and finite Bessel energy
estimates for these genuine metric-defined maps.

## Givens untwisting

Higher odd modes wind several times around the origin. The project defines an
explicit orthogonal Givens product that mixes finitely many Fourier modes while
preserving their derivative energy. Every mixed row satisfies strict
first-harmonic dominance, so its boundary curve is injective and has degree
`+1`.

## Jordan regions and mod-2 topology

The formalization transports the Jordan curve theorem to the complex plane,
identifies the bounded degree-one component containing the origin, and proves
coverage from an odd boundary-degree obstruction.

The finite polygonal obstruction is fully assembled: face cuts, real lifts,
integer edge turns, and the signed boundary-turn identity are constructed in
Lean. The general glued-pairing theorem covers both preserving and reversing
side identifications.

## Planar area and explicit constants

For Lipschitz maps on planar pieces, the project proves a genuine area
inequality from Rademacher's theorem and mathlib's Jacobian image bound. It
then composes coverage, exact Fourier area, and the common derivative-energy
budget.

The orientation-free constant is

```text
14 ζ(3) / π = 5.3567723444...
```

The oriented nonlinear certificate at `λ = 0.03` gives the rigorous scalar
conclusion

```text
area > 5.38982446
```

Both headline surface statements remain conditional until the intrinsic
Riemannian globalization described on the
[formalization page](formalization.md) is supplied.

