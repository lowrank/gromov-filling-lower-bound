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
| Planar analysis | Lipschitz area inequality, determinant identity, Jacobian budgets |
| Certificate logic | finite-to-infinite universal deduction, defect propagation, scalar optimization |
| Rigorous numerics | rational bounds for `π`, `ζ(3)`, and the displayed constants |
| De Sitter profile algebra | quadric membership, formal-velocity speed, pairwise Lorentz product, Züst kernel identity |

Proposition 15.1 is verified at an explicit denominator interface:
`DeSitterProfile.lean` takes profile values and the derivative value as scalars
and requires the relevant sine denominators to be nonzero. It does not claim a
separate almost-everywhere differentiability theorem for arbitrary Lipschitz
profiles.

## General polygon-side pairings

`GromovFilling.GeneralSurfaceObstruction` proves that every circle-valued map
on a glued-strip point quotient has even degree on the glued lower loop. The
proof pairs integer edge turns under an arbitrary fixed-point-free involution.
Preserving pairs agree; reversing pairs differ by sign; both cancel modulo two.

Consequently, the free boundary has the odd-degree obstruction for every
polygon schema, and the existing continuous-map and homeomorphism interfaces
derive their lower obstruction automatically.

## Partial headline statements

The finite universal certificate and the nonlinear oriented certificate are
kernel-verified deductions from named geometric inputs. The following bridges
are not yet verified for every compact Riemannian surface:

- surface classification or arbitrarily-fine compatible cell structures;
- almost-everywhere eikonal differentiation and weak parameter integration;
- intrinsic area measure and chartwise Jacobian globalization;
- the global differential-form Stokes/comass inequality.

!!! danger "No conditional-shell upgrade"
    These bridges are not declared as project axioms. Until they have kernel
    proofs, the project does not describe the two manuscript headlines as
    end-to-end Lean theorems.

## Open feasible manuscript obligations

Several later finite or algebraic manuscript claims remain suitable for future
formalization, including the separable barrier, Hardy stationarity, the
stationary-resonance hierarchy, and the one-high-leg spectral ceiling. Their
current status is recorded individually in the root statement ledger.
