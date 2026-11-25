# The finite certificate above 6.095

For a compact connected orientable Riemannian surface whose single boundary is an isometrically embedded intrinsic circle of length $2\pi$, in every genus,
$$
 \operatorname{Area}(M)\ge
 \frac{316186938521718142086885116509}{511999948800000000000000000000}\pi^2
 >6.095000609501857507.
$$
The displayed decimal improves the previous $6.091188129789057449$ by $0.003812479712800058$. The construction uses the four existing anchor levels and changes the 829 active master coefficients jointly. Its mathematical inputs are the distance-coordinate Stokes argument and the coverage of the transported finite hierarchy. The supplied verifier checks every local positive semidefinite bound for the new field from scratch. The repository's Lean development covers the earlier Fourier theorem. [Geometric setup and scalar weights](issue163_reweighted_field.md) · [Earlier Fourier theorem](docs/current-manuscript.md)

## The changed form and its boundary action

Write $F_i$ for half the difference of distances to two antipodal anchors. The form is a sum of $W_{ij}(F_i,F_j)\sigma(|F_i|)\sigma(|F_j|)\,dF_i\wedge dF_j$. Each term is a pullback from a plane. It has a primitive for the Stokes computation, including the piecewise-constant coefficient case by the finite source argument. The 15 scalar multipliers have denominator $10^8$ and are even. On the interior of every reached terminal scalar bin the replay checks that the multiplier is constant. On a fixed scalar facet the corresponding coordinate differential vanishes almost everywhere on its preimage. The source extension treats these facets.

The integer master changes have units $1/(2\cdot10^{12})$. Start from the 65 signed endpoint changes in the previous 112-point field. At each of the four levels reconstruct every pair coefficient using the signed master changes and archived dyadic scales. Away from the two-step endpoint band, a child coefficient vanishes at odd separation and equals half its parent's at even separation. The verifier checks these identities directly on 1,206, 7,930 and 61,326 classes at the successive doublings. Since the scalar multipliers are functions of the coordinates themselves, the identities also hold after multiplication. Thus the two parity blocks inherit the parental comass bound on every region covered by the finite hierarchy.

On the final grid take $h=\pi/112$, and use integer coefficients $w_o$ in units $1/(16\cdot10^{12})$. For separation $k$, the scalar pair cell $(a,b)$ belongs to its boundary polygon when $|a-b|\le k$ and $|a+b-111|\le112-k$. Its area is $h^2/2$ if an equality holds and $h^2$ otherwise. There are $112-k$ index pairs at this separation. The replay counts all 480,704 positive-area cells, compares every orbit's weight with the source, and reproduces the previous field's action as a second normalization check. The new raw action is
$$
 \pi^2\frac{2478905598010270233961179313430560}
 {112^2(32\cdot10^{12})(10^8)^2}.
$$

## Integer norm verification

For a terminal matrix write $W$ for its unweighted real skew matrix and $S$ for the diagonal matrix of scalar multipliers. A diagonal $D$ with $D+iW/2\succeq0$ gives $SDS+iSWS/2\succeq0$. Since every coordinate gradient has norm at most one, the absolute evaluation of the weighted form is bounded by $\operatorname{tr}(SDS)$. Complex conjugation gives the opposite sign. The common rational trace budget is $999999900000/10^{12}$. Dividing the raw action by this budget gives the stated exact fraction.

The checker uses the earlier diagonal arrays to propose integer diagonals, with a stored replacement where needed. For each proposed $D$ it compares its weighted trace to the budget using integers. It next proposes a rounded complex triangular factor $L$ and verifies that the cleared-denominator Hermitian residual $D+iW/2-LL^*$ is diagonally dominant in every row. It uses $|\Re z|+|\Im z|$ as an upper bound for each off-diagonal modulus. The residual and the Gram matrix are therefore positive semidefinite. Floating-point Cholesky proposes the factor. Acceptance uses integer Gram products and trace comparisons. A bound on the squared norm of each integer factor row ensures all signed 64-bit dot products fit by Cauchy–Schwarz. The cleared residual and trace use signed 128-bit integers.

| Anchor pairs | Terminal profiles | Stored replacement diagonals |
|---:|---:|---:|
| 14 | 53,100 | 92 |
| 28 | 29,410 | 63 |
| 56 | 14,562 | 58 |
| 112 | 116,986 | 16,028 |
| Total | 214,058 | 16,241 |

The discovery search alternated between changing coefficients and testing individual matrices. A positive semidefinite correlation matrix from a restrictive profile supplies a linear inequality on the coefficients. Optimizing the corresponding diagonal trace exposed constraints missed by short phase searches. The final rational result uses the published coefficients and witnesses alone. The separate symmetry experiment studies a geometric route to larger gains. [One-dimensional geometric test](issue163_symmetry.md)

## Replay

From the branch root, with Node.js and a C++17 compiler supporting signed 128-bit integers, run

~~~sh
node issue163_free_field.cjs issue163_inputs
~~~

The checker verifies the five source hashes, uses a temporary build directory, and supports either OpenMP or a serial build. The little-endian witness archive contains one block per level. Each begins with the count and zero-based row indices followed by the corresponding unweighted diagonals in units of $10^{-9}$, using unsigned 32-bit integers. The reported decimal uses the lower end of a directed Machin-formula enclosure of $\pi$.
