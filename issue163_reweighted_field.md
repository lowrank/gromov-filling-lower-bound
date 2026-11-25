# A finite reweighting above 6.09

Every compact connected orientable Riemannian surface with one boundary component isometrically filling the intrinsic circle of length $2\pi$ satisfies

$$
 \operatorname{Area}(M)\ \ge\
 \frac{617071518788759584}{10^{18}}\pi^2
 \ >\ 6.090251777624436438.
$$

This finite result uses 112 antipodal anchor pairs. The annular Fourier certificate on this branch first gave $6.086380541911894628$. Reweighting the finite form gave $6.090117449247249322$, and three changes to its endpoint coefficients give the bound displayed above. Both take the transported finite calibration in the 25 November 2026 bundle as a theorem. The following argument consists of a pairwise closed form, an exact boundary-action calculation, and integer matrix and trace certificates. The earlier Fourier theorems have a separate Lean verification. [Earlier Fourier formalization](https://github.com/lowrank/gromov-filling-lower-bound)

## Changing the finite form

Let $h=\pi/112$. Split $|F_i|/h$ at the knots

~~~
0  8  16  24  32  36  40  42  44  46  48  50  52  54  55  56
~~~

On successive intervals use the multipliers $\sigma=S_j/10^8$ given by

~~~
100259911 100259899 100257343 100258354 100241253
100250506 100231480 100236670 100214191 100206599
100040345  99799793  99606872 100703694 100522025
~~~

First add the following increments to the unscaled final coefficient numerators, using the zero-based orbit indices in `reps_112`.

| Orbit | Increment in units of $1/(16\cdot 10^{12})$ |
|---:|---:|
| 1 | 6,714,930,082 |
| 115 | 49,203,043 |
| 280 | 10,427,640,066 |

Each orbit has at least one coordinate in the two outermost cells at either end of the 112-point scalar grid. Thus these changes vanish on the interior where the inherited decomposition is used. On every affected edge, adding half the absolute coefficient increment to each endpoint diagonal makes its two-by-two Hermitian correction positive semidefinite. Summing these edge corrections supplies an initial witness on every 112-point terminal cell.

Multiply each resulting coefficient $W_{ij}(F_i,F_j)$ by $\sigma(|F_i|)\sigma(|F_j|)$, with the interval of each scalar understood in units of $h$. Each term still pulls back a planar two-form, so the boundary Stokes calculation applies. The new coefficient array at a profile is $SWS$ with $S$ diagonal. Any old witness $D+iW/2\succeq0$ gives $SDS+iSWS/2\succeq0$. The raw trace is now $\sum_i d_i\sigma_i^2$. Since the multipliers are even, all signed dihedral reductions still apply. The extra knot $55h$ occurs only in terminal 112-point cells. Every reached ancestor cell is explicitly checked for constancy of its weights. Dyadic direct-sum inheritance commutes with this diagonal multiplication. The source zero-coordinate extension handles scalar grid facets.

The source stores matrix coefficient numerators $w_o$ in units of $1/(16\cdot 10^{12})$. Here $o$ indexes the 61,656 final pair classes. Let $\omega_o$ be the source's boundary polygon weight in units of $h^2$. The unordered pair of absolute scalar intervals $(a,b)$ is invariant on each orbit. The raw action in units of $\pi^2$ is therefore
$$
 \frac{\sum_o(2\omega_o)w_o S_a S_b}
 {112^2\,(32\cdot10^{12})\, (10^8)^2}.
$$
The integer numerator is $2474701746017983670807146346984704$. Before applying the three increments, substitution of unit multipliers reproduces the archived finite action exactly.

## Certifying the norm

The checker reconstructs the original diagonals on all four terminal levels and checks their SHA-256 hashes against the finite input certificate. At level 112 it canonicalizes the even and odd projections of all 116,986 cells, restores all 28 additional parent rows, interleaves the transported diagonals and adds the exact endpoint edge repairs. This recovers the original full child-diagonal hash. Each stored diagonal gives a fresh exact trace after rescaling.

For a row exceeding the target trace, the checker can substitute an improved diagonal for the corresponding unscaled matrix $W$, including the three increments at level 112. Floating-point block-coordinate ascent and Cholesky factorization only propose witnesses. For acceptance, let $d$ be the proposed integer diagonal, $G$ the integer Hermitian matrix for $\operatorname{diag}(d)+iW/2$ in common units, and $L$ a rational lower-triangular factor. Clear denominators in $G-LL^*$. The code checks for every row that its real diagonal dominates the sum of the absolute real and imaginary parts of all off-diagonal entries. Hermitian diagonal dominance gives $G-LL^*\succeq0$, hence $G\succeq0$. Only a reduction in the exact weighted trace is retained. An unsuccessful proposal leaves the previous exact witness available.

| Anchor pairs | Reached cells | Accepted replacement diagonals |
|---:|---:|---:|
| 14 | 53,100 | 64 |
| 28 | 29,410 | 27 |
| 56 | 14,562 | 49 |
| 112 | 116,986 | 30 |

The largest raw trace is bounded by
$$
 \frac{639412781378330309465819737102}
 {640000000000000000000000000000}.
$$
The denominator here is $64\cdot10^{12}(10^8)^2$. Dividing the exact action by this trace bounds the area. The checker rounds the resulting $\pi^2$ coefficient down to 18 decimal places and uses a directed rational enclosure of $\pi$ for the stated decimal.

## Replay

Keep the two JavaScript files together and run

~~~sh
node issue163_reweighted_field.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The replay uses Node.js built-ins. It pins the transported compact certificate, baseline compact certificate, source geometry, hierarchy maps, and endpoint profile file by hash. The bundle's original entry point is <code>python3 verify_improved.py</code> in that input directory. The reweighting checker uses its established coverage, inheritance and PSD theorems. The new bound has no Lean theorem on this branch.
