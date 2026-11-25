# A signed finite calibration above 6.091

Every compact connected orientable Riemannian surface with one boundary component isometrically filling the intrinsic circle of length $2\pi$ satisfies

$$
 \operatorname{Area}(M)\ \ge\
 \frac{617154280862042281}{10^{18}}\pi^2
 \ >\ 6.091068606547150624.
$$

This finite certificate uses 112 antipodal anchor pairs. The supplied note gave $6.082181436172889493\ldots$. A shell-dependent Fourier correction gave $6.086380541911894628$ on this branch. Reweighting the finite form and changing three endpoint coefficients gave $6.090475197311347654$. The new bound uses signed changes in 66 endpoint classes. It relies on the bundle’s transported finite theorem for profile coverage and positive semidefinite witnesses. The earlier Fourier theorems have a separate Lean verification. [Earlier Fourier formalization](https://github.com/lowrank/gromov-filling-lower-bound)

## Changing the finite form

Parameterize the boundary by arclength $\gamma$. For $h=\pi/112$, let $F_i(p)=(d_M(p,\gamma(ih+\pi))-d_M(p,\gamma(ih)))/2$. These functions are spatially $1$-Lipschitz and their prescribed boundary values determine the action. Split $|F_i|/h$ at the knots

~~~
0  8  16  24  32  36  40  42  44  46  48  50  52  54  55  56
~~~

On successive intervals use the multipliers $\sigma=S_j/10^8$ given by

~~~
100265936 100252506 100262495 100257567 100240481
100250394 100231550 100236549 100213980 100206332
100040363  99795356  99619763 100704371 100516523
~~~

First add the signed endpoint increments to the raw coefficient numerators in units of $1/(16\cdot10^{12})$. The complete array of zero-based orbit indices and signed integers is listed as <code>ENDPOINT_STEPS</code> in the checker. [Exact coefficient list](issue163_reweighted_field.cjs)

Each orbit has at least one coordinate in the two outermost cells at either end of the 112-point scalar grid. Thus these changes vanish on the interior where the inherited decomposition is used. On every affected edge, adding half the absolute coefficient increment to each endpoint diagonal makes its two-by-two Hermitian correction positive semidefinite. Summing these edge corrections supplies an initial witness on every 112-point terminal cell.

Multiply each resulting coefficient $W_{ij}(F_i,F_j)$ by $\sigma(|F_i|)\sigma(|F_j|)$, with the interval of each scalar understood in units of $h$. Each term still pulls back a planar two-form, so the boundary Stokes calculation applies. The new coefficient array at a profile is $SWS$ with $S$ diagonal. Writing the gradients in an oriented orthonormal frame as complex numbers $z_i$ gives $|z_i|\le1$. The form evaluates to $Q_{SWS}(z)=z^*(-iSWS/2)z$. Complex conjugation reverses its sign. Any old witness $D+iW/2\succeq0$ gives $SDS+iSWS/2\succeq0$. The raw trace is now $\sum_i d_i\sigma_i^2$. Since the multipliers are even, all signed dihedral reductions still apply. The extra knot $55h$ occurs only in terminal 112-point cells. Every reached ancestor cell is explicitly checked for constancy of its weights. Dyadic direct-sum inheritance commutes with this diagonal multiplication. The source zero-coordinate extension handles scalar grid facets.

The source stores matrix coefficient numerators $w_o$ in units of $1/(16\cdot 10^{12})$. Here $o$ indexes the 61,656 final pair classes. Let $\omega_o$ be the source's boundary polygon weight in units of $h^2$. The unordered pair of absolute scalar intervals $(a,b)$ is invariant on each orbit. The raw action in units of $\pi^2$ is therefore
$$
 \frac{\sum_o(2\omega_o)w_o S_a S_b}
 {112^2\,(32\cdot10^{12})\, (10^8)^2}.
$$
The integer numerator is $2475042091354999762510970141278304$. Before applying the signed increments, substitution of unit multipliers reproduces the archived finite action exactly.

### Discovering signed changes

For a fixed terminal cell and a complex unit-vector configuration, both its norm test and the boundary action are affine in the endpoint changes. We optimized the boundary action against these linear tests, with separate variables for increases and decreases. We evaluated every other cell using its previous diagonal bound plus the sum of the absolute edge changes and reoptimized the most restrictive cells.

Weak coupling between the dyadic residue classes slowed individual gradient updates. In the search we also rotated a whole residue block at once. For one complex component of a block, let $C$ be the sum of $\overline z_i(-\mathrm i W_{ij}/2)z_j$ over edges leaving the block. Multiplying that component throughout the block by $C/|C|$ maximizes its cross-block contribution while preserving all internal contributions and every vector norm. This exposed endpoint constraints missed by short individual-coordinate sweeps. The integer verifier tests the final coefficients on the full domain independently of these search heuristics.

## Certifying the norm

The checker reconstructs the original diagonals on all four terminal levels and checks their SHA-256 hashes against the finite input certificate. At level 112 it canonicalizes the even and odd projections of all 116,986 cells, restores all 28 additional parent rows, interleaves the transported diagonals and adds the exact endpoint edge repairs. This recovers the original full child-diagonal hash. Each stored diagonal gives a fresh exact trace after rescaling.

For a row exceeding the target trace, the checker can substitute an improved diagonal for the corresponding unscaled matrix $W$, including the signed increments at level 112. Floating-point block-coordinate ascent and Cholesky factorization only propose witnesses. For acceptance, let $d$ be the proposed integer diagonal, $G$ the integer Hermitian matrix for $\operatorname{diag}(d)+iW/2$ in common units, and $L$ a rational lower-triangular factor. Clear denominators in $G-LL^*$. The code checks for every row that its real diagonal dominates the sum of the absolute real and imaginary parts of all off-diagonal entries. Hermitian diagonal dominance gives $G-LL^*\succeq0$, hence $G\succeq0$. Only a reduction in the exact weighted trace is retained. An unsuccessful proposal leaves the previous exact witness available.

| Anchor pairs | Reached cells | Accepted replacement diagonals |
|---:|---:|---:|
| 14 | 53,100 | 341 |
| 28 | 29,410 | 35 |
| 56 | 14,562 | 77 |
| 112 | 116,986 | 270 |

The largest raw trace is bounded by
$$
 \frac{639414960924605591061056558420}
 {640000000000000000000000000000}.
$$
The denominator here is $64\cdot10^{12}(10^8)^2$. Dividing the exact action by this trace bounds the area. At the earlier three-coefficient checkpoint, increasing all 330 endpoint coefficients arbitrarily could give at most $6.090478414162$ under independent planar tests. Signed changes escape this ceiling. [Exact dual bounds](issue163_reweight_ceiling.md)

The checker rounds the resulting $\pi^2$ coefficient down to 18 decimal places and uses a directed rational enclosure of $\pi$ for the stated decimal.

## Replay

Keep the two JavaScript files together and run

~~~sh
node issue163_reweighted_field.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The replay uses Node.js built-ins. It pins the transported compact certificate, baseline compact certificate, source geometry, hierarchy maps, and endpoint profile file by hash. The bundle's original entry point is <code>python3 verify_improved.py</code> in that input directory. The reweighting checker uses its established coverage, inheritance and PSD theorems. The new bound has no Lean theorem on this branch.
