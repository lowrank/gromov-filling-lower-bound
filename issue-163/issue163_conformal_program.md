# A global convex problem in which the round hemisphere attains the minimum

The hemisphere supplies feasible distance coordinates in the finite calibration model. A stronger requirement is that its area be the minimum of the comparison problem. This can be achieved with a common conformal factor and globally defined distance coordinates on a fixed marked conformal surface. In the marked round class one averaged path inequality gives the exact minimum $`2\pi`$. With just 47 equally spaced antipodal pairs the same calculation gives **6.1502116** in that class. The remaining difficulty for an unconditional area improvement is uniform control across marked conformal classes and genus. [Finite all-genus certificate](issue163_anchor_occupation.md) · [Exact scalar checks](issue163_conformal_check.py)

## Global potentials and the metric they certify

Fix a compact orientable surface $`M`$ with one boundary, its boundary marking $`s\in\mathbb R/2\pi\mathbb Z`$, and a reference metric $`h`$ giving boundary arclength $`ds`$. Vary the metric as $`g=\rho^2h`$. For a collection $`S`$ of labels, solve

~~~math
 \begin{aligned}
 \inf_{\rho,F_a}\quad &\int_M\rho^2\,dA_h \\[2pt]
 \text{subject to}\quad &\rho\gt0,\quad \rho|_{\partial M}=1,\\[2pt]
 &|dF_a|_h\le\rho,\qquad
 F_a(\gamma(s))=\pi/2-d_{S^1}(a,s)\quad(a\in S).
 \end{aligned}
~~~

Here $`\rho`$ can be smooth and the $`F_a`$ Lipschitz with the derivative inequality almost everywhere. All variables live on the **same** surface. Convexity follows from the triangle inequality for each covector norm and the quadratic objective. This is an extremal-length formulation with boundary-point constraints. [Headrick and Zwiebach on convex conformal minimal-area programs](https://arxiv.org/abs/1806.00449)

This problem enforces exactly the sampled antipodal distances within the chosen marked conformal class. The global gradient bound makes each $`F_a`$ 1-Lipschitz for $`g`$, so every path from $`a`$ to $`a+\pi`$ costs at least $`\pi`$. Conversely, if those antipodal distances are at least $`\pi`$, the two boundary arcs give equality. For any boundary point, its distances to a tested pair are bounded above by the two circle distances and their sum is at least $`\pi`$. Both upper bounds are therefore attained. The half difference of the two intrinsic distance functions gives the required $`F_a`$. With all labels, every pair of boundary points has the correct distance. Taking the outer infimum over marked conformal structures and genus then recovers the original geometric problem.

On a fixed flat triangulation, affine potentials and a constant factor on each triangle give second-order cone constraints involving neighboring vertex values. Discretizing the potentials and metric on one mesh provides a calculation for that mesh. To certify a continuum lower bound one needs a relaxation or an independent lower certificate that applies to all continuum competitors. The path measures below provide such certificates.

There is a separate obstruction to making the hemisphere the minimum with only the present finite distance tests while varying all conformal structures. A smooth disk passing all 112 tests has area below **6.26430**. The known finite-sampling comparison $`(1-1/n)I\le I_n\le I`$ for the all-genus infima does leave enough room for a 6.15 certificate. For example, *if* $`I=2\pi`$, even $`I_{48}\ge 2\pi\cdot47/48\gt6.15228`$. [Smaller feasible disk](issue163_sampled_disk.md) · [Finite-sampling comparison](issue163_sampling.md)

## One path average solves the round case

Let $`h`$ be the unit round hemisphere with its standard arclength marking. A uniform round great semicircle has antipodal endpoints, length $`\pi`$, and mean arclength measure $`dA_h/2`$. This follows by rotating a full great circle uniformly on the sphere and restricting to its upper half. Thus every feasible factor for the full boundary problem satisfies

~~~math
 \pi\le\mathbb E_\gamma\int_\gamma\rho\,ds_h
       =\tfrac12\int_M\rho\,dA_h,\qquad
 \int_M\rho^2\,dA_h\ge2\pi+\int_M(\rho-1)^2\,dA_h .
~~~

One may keep just this single averaged constraint and the same quadratic objective. The unique minimizing factor up to equality almost everywhere is still $`\rho=1`$. This proves optimality in the marked round class and displays a dual certificate that is tight at the hemisphere.

For $`n`$ equally spaced antipodal pairs let $`\delta(s)`$ be the angular distance to the nearest of the $`2n`$ signed anchors. On a path from $`s`$ to $`s+\pi`$, the best sampled coordinate changes by $`\pi-2\delta(s)`$. Since the endpoint longitude is uniform, $`\mathbb E\delta=\pi/(4n)`$. Cauchy–Schwarz in the preceding display now gives

~~~math
 A\ge 2\pi\left(1-\frac1{2n}\right)^2
 \qquad\text{in the marked round conformal class.}
~~~

This particular lower estimate is below 6.15 at 46 pairs and above 6.15 at 47. The known 112-test disk uses the freedom to vary the metric and is consistent with this fixed-class estimate.

## A curve-family test in every genus

For any reference metric $`h`$, take a probability law on paths joining boundary antipodes. Write $`k\,dA_h`$ for the arclength measure averaged over the paths, assuming it has an $`L^2`$ density. Every isometric filling in that marked conformal class satisfies

~~~math
 \pi\le\int_M \rho k\,dA_h,\qquad
 A\ge\frac{\pi^2}{\int_M k^2\,dA_h}.
~~~

For a universal proof of 6.15, one sufficient aim is to find in each class a path law with $`\int k^2\le\pi^2/6.15=1.6048137\ldots`$. The round value is $`\pi/2=1.5707963\ldots`$. Under $`h\mapsto\psi^2h`$ the density becomes $`k/\psi`$, so its squared integral is conformally invariant. For a finite menu of path laws the only data needed to mix them are the inner products $`G_{ij}=\int k_i k_j\,dA_h`$. A probability mixture has energy $`\lambda^tG\lambda`$. A law on finitely many individual curves generally has singular arclength measure. Each member of the menu can instead describe a continuous family.

A construction independent of the boundary marking uses the closed surface $`N`$ obtained by identifying antipodal boundary points. It has area $`A`$. Every orientation-reversing loop on $`N`$ costs at least $`\pi`$. A transverse representative crosses the glued seam an odd number of times. Bound each intervening segment by the circle distance of its endpoints in the filling. Translating alternate comparison arcs by $`\pi`$ produces a circle path to the antipode. Approximation gives the same result for rectifiable loops. Thus the curve-family estimate also holds on $`N`$ for laws on orientation-reversing loops. [Antipodal quotient and length proof](issue163_symmetry.md) · [Bangert, Croke, Ivanov and Katz](https://arxiv.org/abs/math/0405583)

For an explicit test, suppose $`N`$ contains pairwise disjoint conformal Möbius bands of half-widths $`T_i`$. The convention for width is the flat orientation double $`(-T_i,T_i)\times(\mathbb R/2\pi\mathbb Z)`$ with identification $`(y,\theta)\sim(-y,\theta+\pi)`$. Then every such filling satisfies

~~~math
 \boxed{\quad A\ \ge\ 2\pi\sum_i\tanh T_i.\quad}
~~~

One band of half-width 2.27 gives area above **6.15047**. Three disjoint bands of half-width 0.34 give area above **6.17280**. These are conditions on the conformal geometry of a filling, valid with arbitrary genus. Existence of enough such bands or suitably overlapping curve families on every quotient remains open here. This uses the classical spherical-band idea from conformal systolic geometry. The loop constraint used in this application concerns the orientation-reversing class. [Pu on the projective plane and Möbius strip](https://msp.org/pjm/1952/2-1/pjm-v2-n1-p06-s.pdf) · [Eyll on fixed-class Möbius strip systolic inequalities](https://arxiv.org/abs/2502.13715)

To compute the arclength density, put $`H=\tanh T`$. The standard model is the round spherical belt $`|z|\lt H`$ modulo the antipodal map, since $`y=\frac12\log((1+z)/(1-z))`$ puts the metric in conformal cylinder coordinates. The upper half $`0\le z\lt H`$ represents its area once and has area $`2\pi H`$. Choose the starting longitude uniformly and the maximum height $`b\in(0,H)`$ of a great semicircle with probability density $`b/(H\sqrt{H^2-b^2})`$. The semicircle has height $`z=b\sin t`$ at round arclength $`0\le t\le\pi`$. Its projection is an orientation-reversing loop. At each $`0\lt z\lt H`$ the averaged arclength per unit height is

~~~math
 \frac2H\int_z^H\frac{b\,db}
 {\sqrt{H^2-b^2}\sqrt{b^2-z^2}}=\frac\pi H .
~~~

Indeed $`b^2=z^2+(H^2-z^2)v`$ reduces the integral to the beta integral on $`[0,1]`$. Longitude is uniform, so $`k=1/(2H)`$ relative to round belt area. If the physical metric on the band is $`\rho^2g_{\rm belt}`$, its loop constraint gives $`\int\rho\,dA_{\rm belt}\ge2\pi H`$. Completing the square bounds its physical area below by $`2\pi H+\int(\rho-1)^2\,dA_{\rm belt}`$. Summing over the disjoint bands proves the display. The round band itself attains equality in the problem with just these loop constraints. For two overlapping bands of the same $`H`$, the individual energies are $`E=\pi/(2H)`$. If $`G_{12}/E\le\eta`$, their equal mixture yields $`A\ge4\pi H/(1+\eta)`$. For instance $`H=0.6`$ and $`\eta\le0.22`$ suffice for **6.18018**. Only one overlap integral is required for this test.

## How hard is the exact pointwise planar maximum?

On one fixed cell the exact independent-gradient problem maximizes $`\sum_{i\lt j} W_{ij}\sin(\theta_j-\theta_i)`$. A maximizer may have every gradient of unit norm because the expression is separately affine on each disk, and a common rotation removes one angle. This leaves 111 relative angles on the 112-grid. The larger geometric problem also requires globally compatible potentials and a metric. [Planar cell and certificate](issue163_planar_comass.md)

For arbitrary input skew matrices even the exact local threshold problem is NP-hard. Here is a reduction specifying the difference between that worst-case statement and the particular structured matrices in this repository. Start with an instance of graph 3-colorability. For every edge $`uv`$ add a fresh vertex $`w_{uv}`$ and use the three edges of the triangle $`u,v,w_{uv}`$. Let $`m`$ be the original edge count and $`L`$ the graph Laplacian of the resulting triangle edges, counted with multiplicity. Use the integer skew matrix with upper-right block $`L`$, lower-left block $`-L`$, and zero diagonal blocks. [Garey, Johnson and Stockmeyer on graph 3-colorability](https://doi.org/10.1016/0304-3975%2876%2990059-1)

For disk vectors in its two blocks the objective is $`\Im(z^*Ly)`$. Since $`L\succeq0`$, Cauchy–Schwarz bounds its absolute value by the maximum of $`z^*Lz`$ on the disk product, and $`y=iz`$ attains that value. In $`z^*Lz`$ each triangle contributes its three squared edge differences, equal to

~~~math
 3(|z_u|^2+|z_v|^2+|z_w|^2)-|z_u+z_v+z_w|^2\le9 .
~~~

Equality requires three unit vectors at phases spaced by 120 degrees. Hence the threshold $`9m`$ is attained exactly when the original graph is 3-colorable. In each connected component the phase at a root and adjacency force every original vertex to one of three phases. Conversely a coloring extends by the unused color on each new triangle vertex. The reduction supplies a worst-case complexity result as the matrix size varies. It leaves room for short certificates in individual geometric cells.

The scalar thresholds and height moments can be replayed from this folder.

~~~sh
python3 issue163_conformal_check.py
~~~
