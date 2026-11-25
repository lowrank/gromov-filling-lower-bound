# A planar comass improvement for the current filling-area certificate

For every compact connected orientable Riemannian surface with one isometrically embedded boundary circle of length $2\pi$,

```math
 \mathrm{Area}(M)\ge
 \frac{2213637594435078034608195815563}{3583999641600000000000000000000}\pi^2
 >6.095906676681434095 .
```

The increase over the exact bisected-gap action $B$ is $(125/69999993)\pi^2$, about $0.0000176242953$. The preceding full-boundary energy result was $B+2^{-1372}$. This improvement uses a failure of the current semidefinite relaxation and the positive area that the boundary distances force into the affected cells. [Previous finite field](issue163_midpoint.md) · [Angular energy result](issue163_angular_energy.md)

## A correlation in the optimizer that a tangent plane cannot produce

In an oriented orthonormal tangent frame represent $`dF_j`$ by $`z_j\in\mathbb C`$ with $`|z_j|\le1`$. A cell with real skew matrix $Y$ evaluates to

```math
 Q_Y(z)=\sum_{i<j}Y_{ij}\,\Im(\overline z_i z_j)=z^*(-iY/2)z .
```

The diagonal certificate $D+iY/2\succeq0$ bounds this by $\mathrm{tr}(D)$. The same certificate also bounds the sum with each $`z_j`$ replaced by a vector in a complex Hilbert space. This larger optimization allows correlations that miss a constraint of a Riemannian tangent plane.

For the current parent corner matrix, an explicit array of 112 vectors in $\mathbb C^3$, all of norm at most one, has value **at least $0.999999812$**. The old diagonal certificate bounds its optimum by $U=0.9999999$. In a real tangent plane the same matrix has value **at most $0.9997999$**. Convex averaging of planar configurations also satisfies this upper bound. Thus the violation singles out a near optimizer of the matrix actually used in the bound. The rational vectors and the planar upper certificates are included in the same witness. [Integer data](issue163_planar_witness.json)

Here is the extra planar constraint. The maximum of $`Q_Y`$ on the product of disks is attained with all $`|z_j|=1`$, by maximizing its affine dependence on one coordinate at a time. Then, for indices 3 and 110 in the signed frame of the gap,

```math
 q=\frac{3+4i}{5}\overline z_3z_{110},\qquad
 (\Re q)^2+(\Im q)^2=1 .
```

This is stronger than allowing $q$ to range over the whole disk. Put $t=1/1000$ and $c=U-1/5000$. For each $`\sigma\in\{1,i,-1,-i\}`$ the checker certifies a diagonal $`D_\sigma`$ with

```math
 Q_Y(z)+t\Re(\sigma q)\le\mathrm{tr}(D_\sigma)
 \qquad(|z_j|=1).
```

It does so by subtracting the corresponding off-diagonal Hermitian penalty from $`D_\sigma+iY/2`$ and verifying positive leading principal minors over the Gaussian integers. Write $`b_\sigma=(\mathrm{tr}(D_\sigma)-c)/t`$. If $`Q_Y(z)\gt c`$, these four bounds enclose $q$ in a rectangle whose coordinate magnitudes are bounded by $`X=\max(b_1,b_{-1})`$ and $`Z=\max(b_i,b_{-i})`$. The exact checker proves $`X^2+Z^2\lt 1`$ in each of the three old chambers. The rectangle misses the unit circle, which proves $`Q_Y\le c`$. Complex conjugation gives the lower bound $`Q_Y\ge-c`$. Signed reflection carries the result to the other half of the gap. Twelve diagonal comparisons suffice. The following radii are rounded upward.

| Chamber | Real radius $X$ | Imaginary radius $Z$ |
|---|---:|---:|
| Parent | 0.891740 | 0.402387 |
| Left child matrix | 0.797865 | 0.442902 |
| Right child matrix | 0.845596 | 0.395143 |

## How the shortest distances make the comass gain contribute area

Set $n=112$, $h=\pi/n$ and $R=h/2$. On the gap from $-h$ to zero use the signed frame $`F_0,\ldots,F_{n-1}`$ of antipodal half-distance differences and put $`e_j=F_j-(55.5-j)h`$. Angular Lipschitz continuity gives $`e_0\le\cdots\le e_{n-1}`$. Both neighboring anchor values are above $\pi/2-h$ exactly on the region

```math
 -R<e_0\le e_{n-1}<R .
```

The bisected certificate uses its three corner matrices and their reflections on this region. The 224 rotated regions are disjoint. Their total area is at least $\pi^2/n$ on **every** admissible filling. Indeed $`(F_0,F_{n-1})`$ maps the oriented boundary once around its pair polygon. In the displayed square the polygon is the triangle $`e_0\le e_{n-1}`$, of area $h^2/2$. Stokes, or the signed degree formula, gives

```math
 \int_{\{-R<e_0\le e_{n-1}<R\}}dF_0\wedge dF_{n-1}=h^2/2 .
```

Each gradient has norm at most one, so this signed integral is a lower bound on the area of the region. A clipped-coordinate planar primitive proves the same identity on open scalar cells. The Jacobian vanishes almost everywhere on the preimages of their edges. Summing over the gaps gives $2n(h^2/2)=\pi^2/n$. [Pairwise boundary-degree argument, Tang, Section 2](https://hexagonmath.org/pdf/2611.00218v2) · [Gap regions and matrices](issue163_midpoint.md)

The old form has integral $UB$ and is bounded by $U$ everywhere. Inside these mandatory regions the improved pointwise bound is $U-1/5000$. Hence

```math
 \mathrm{Area}(M)\ge B+\frac{\pi^2}{5000nU}
 =B+\frac{125}{69999993}\pi^2 .
```

Equivalently one may add $1/5000$ times the displayed pair form on each triangle. It is a pullback from the two extreme coordinates, with the same norm budget and the displayed action gain.

## How far can a better global normalization go?

There is also a planar witness for a neighboring cell of the current field. In units of $h$ its position is

```math
 F_j/h=55-j+(2j-55)/2000,\qquad 0\le j<112 .
```

Every angular inequality is strict, including the antiperiodic wrap. Only one of the 224 signed anchor values exceeds $55h$, so all gap corrections vanish nearby. Standard two-dimensional vectors with rational components give a raw evaluation at least $0.999701031$. The same witness therefore applies to both the bisected field and the corrected field. Even if the global comass were determined exactly, merely rescaling either of these two fixed forms would give **less than $6.09774$**. The new correction changes the form on the corner triangles.

This local witness can be approximated on genuine isometric fillings, even with area arbitrarily close to the all-genus infimum. Consequently one cannot discard it from a pointwise comparison by imposing the full boundary distances. For a different global constraint, every filling of area below $2\pi$ must have, at every fixed anchor, positive area on which the squared gradient norm drops below $1/2+\varepsilon$ for each $`\varepsilon\gt 0`$. [Local realization and global gradient obstruction](issue163_gradient_constraints.md)

## Replay

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_planar_comass.cjs issue163_inputs
~~~

The replay uses the published coefficients and the additional rational vectors and diagonals. It checks all twelve Hermitian comparisons, the two rank tests, the exact action, the decimal floor and the fixed-form ceiling. It uses the previous finite field and bisected-gap theorems on their stated domains. The Lean project formalizes the earlier Fourier result. [Exact checker](issue163_planar_comass.cjs) · [Lean statement ledger](../docs/current-manuscript.md)
