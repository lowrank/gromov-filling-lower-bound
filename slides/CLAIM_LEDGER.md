# Mother-deck claim ledger

This ledger pins every load-bearing core frame to the manuscript and, where
needed, to the formalization boundary. Line numbers refer to the frozen source
blobs recorded in [`README.md`](README.md). Expository diagrams and analogies
are not independent claims.

| Frame label | Load-bearing content | Source locus | Scope guard |
|---|---|---|---|
| `fr:fill-circle` | Definition of an isometric filling as equality of boundary and intrinsic distances; the unit hemisphere is the `2π` benchmark | manuscript lines 115--148; Gromov (1983) | Compact connected Riemannian surface with one boundary component; benchmark/equality candidate, not uniqueness proved here |
| `fr:conjecture` | Every orientable isometric filling is conjectured to have area at least `2π`; disk and genus-one cases are known | manuscript lines 140--153 | General conjecture remains open |
| `fr:scoreboard` | Earlier and paper lower bounds, numerical values, and orientation hypotheses | manuscript lines 155--214 | `14 ζ(3)/π` is orientation-free; nonlinear bound is oriented |
| `fr:pipeline` | Distance profile to certificate proof architecture | manuscript lines 216--257 | Roadmap only; arrows do not assert equivalences |
| `fr:profiles` | `u_θ(x)=d_M(x,γ(θ))` is 1-Lipschitz and gives the boundary triangle wave | manuscript lines 259--314 | Boundary identity uses the no-shortcuts hypothesis |
| `fr:odd-slack` | Odd profile, nonnegative antipodal slack, and a.e. energy split | manuscript lines 279--393 | Eikonal and differentiability are almost-everywhere statements |
| `fr:fourier-camera` | Odd Fourier coordinates, vanishing even modes, and exact boundary loop `z_n(γ(s))=-(4/(πn²))e^{ins}` | manuscript lines 394--434 and 486--523 | Positive odd integers `n` only in the displayed map |
| `fr:budget` | Orthogonal mixing preserves a common Jacobian budget at most one | manuscript lines 415--485 | Pointwise almost everywhere; finite orthogonal families |
| `fr:orientation` | Signed winding is unavailable on nonorientable fillings, motivating mod-2 coverage | manuscript lines 524--548 and 637--708 | Pedagogical contrast; theorem uses the precise surface hypotheses |
| `fr:untwist` | Explicit Givens mixing forces first-harmonic dominance | manuscript lines 524--636 | Finite collection of the first `N` odd modes |
| `fr:coverage` | Dominant harmonic gives a Jordan curve; mod-2 topology forces its bounded region into the image | manuscript lines 637--708 | Coverage is set-theoretic; area inequality also needs Lipschitz regularity |
| `fr:universal` | Summing planar payoffs yields `Area(M) ≥ 14 ζ(3)/π` | manuscript lines 709--748 | No orientability assumption; exact theorem interface in `FORMALIZATION.md`, Theorem 1.1 row |
| `fr:defect` | Antipodal slack produces a nonnegative Dirichlet defect above the baseline | manuscript lines 749--793 | Manuscript theorem; broader raw-distance eikonal formulation is partial in the Lean ledger |
| `fr:calibration` | Oriented symplectic/Stokes formulation recovers the linear baseline and identifies saturation | manuscript lines 794--904 | Hilbert-valued global Stokes is partial as a standalone Lean item; headline closure uses a verified controlled construction |
| `fr:barriers` | Separable scalar reparametrizations and ambient Euclidean Hilbert-space forms cannot beat the linear value | manuscript lines 905--1032 | Barriers apply only to the stated classes |
| `fr:resonance` | Cubic phase resonance increases boundary action linearly | manuscript lines 1033--1141 | Oriented setting; `λ ≥ 0` |
| `fr:stationarity` | First comass variation vanishes at linear saturation; gain is first order and certified cost is second order | manuscript lines 1142--1510 | Exact first variation/corollary remain partial/open as standalone Lean ledger items; quantitative headline closure is verified |
| `fr:nonlinear` | One-parameter certificate and `λ=0.03` give `Area(M)>5.38982446` | manuscript lines 1510--1581 | Oriented fillings; `0 ≤ λ < π²/32`; exact theorem interface in `FORMALIZATION.md`, Theorem 1.2 row |
| `fr:frontier` | One-high-leg resonances have ceiling below `5.466`; other nonlinear routes remain open | manuscript lines 1582--1988 and 2616--2676 | Ceiling is not a no-go theorem for all nonlinear Fourier/profile methods |
| `fr:verified-boundary` | Headline bounds are Lean-verified while named later mechanisms remain partial/open | `FORMALIZATION.md`, complete 27-item ledger and trust-evidence section | Kernel verification certifies formal statements, not the `2π` conjecture or priority |
| `fr:takeaways` (unnumbered close) | Summary of the problem, method, proved constants, and remaining gap | synthesis of the loci above | Must retain the phrase “the conjecture remains open” |

## Primary literature cross-check

Checked on 2026-09-04 against the primary publication/arXiv records:

- M. Gromov, *Filling Riemannian manifolds*, J. Differential Geometry 18
  (1983), 1--147. DOI `10.4310/jdg/1214509283`; MR `697984`.
- V. Bangert, C. Croke, S. Ivanov, and M. Katz, *Filling area conjecture and
  ovalless real hyperelliptic surfaces*, GAFA 15 (2005), 577--597. DOI
  `10.1007/s00039-005-0517-8`; MR `2221144`; arXiv `math/0405583`.
- R. Züst, *The Riemannian hemisphere is almost calibrated in the injective
  hull of its boundary*, Calc. Var. PDE 64 (2025), Art. 297. DOI
  `10.1007/s00526-025-03133-z`; arXiv `2104.04498`.
- J. Briggs and C. Wells, *A discrete view of Gromov's filling area
  conjecture*, arXiv `2602.17859` (2026).

## Release audit questions

For each formal statement frame, verify before release:

1. Are all parameter ranges, orientation assumptions, and quantifiers shown?
2. Is the statement labeled as theorem, mechanism, consequence, barrier, or
   open route honestly?
3. Does the displayed constant match the source to the shown precision?
4. Is every ceiling or obstruction limited to its actual method class?
5. Does any Lean badge correspond to the exact formalization-ledger status?
