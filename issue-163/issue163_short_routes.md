# Short antipodal routes and tests on actual fillings

A point can approximate a prescribed distance profile and a prescribed family of planar unit gradients while lying on almost shortest routes for **every** antipodal pair. This holds on a small open patch of a genuine orientable filling, with arbitrarily small area added to any starting filling. It applies to the continuum of labels and to the detour-dependent coordinate $`G_a=e^{-2H_a/\pi}F_a`$. Its area can tend to zero. [Area inequality that measures those detours](issue163_detour_comparison.md)

## Local realization

Let $`u:S^1\to[-\pi/2,\pi/2]`$ be antiperiodic and 1-Lipschitz in circular distance. Let $`v:S^1\to S^1\subset\mathbb R^2`$ be continuous and satisfy $`v(t+\pi)=-v(t)`$. For any isometric filling $`M_0`$ and any $`\varepsilon\gt 0`$ there is a smooth isometric filling of area less than $`\mathrm{Area}(M_0)+\varepsilon`$, with a Euclidean open disk on which

~~~math
 |F_t-u(t)|<\varepsilon,\qquad
 0\le H_t<\varepsilon,\qquad
 |\nabla F_t-v(t)|+|\nabla H_t|<\varepsilon .
~~~

The value estimates hold throughout the disk for every $`t`$. The derivative estimates are uniform wherever the two distance derivatives exist, hence almost everywhere for each fixed label and almost everywhere in the product. By taking smaller errors, the same value and gradient approximation holds for $`G_t`$. The added genus is finite and can grow as $`\varepsilon`$ decreases.

**Proof.** Scale $`u`$ toward zero by a factor arbitrarily close to one so that its angular Lipschitz constant is $`k\lt 1`$. Choose a fine finite antipodally symmetric net of labels $`t_i`$, of covering radius $`\delta`$. In a flat square torus of side $`10r`$ mark points $`p_i=o+rw_i`$ about its center $`o`$, where the unit vectors $`w_i`$ approximate $`v(t_i)`$ and are perturbed slightly to make the points distinct. Drill holes of radius $`s`$ about them. Drill matching interior holes in $`M_0`$ centered at points within $`\xi`$ of the corresponding boundary anchors. Connect each pair of rims by a cylinder of length

~~~math
 L_i=\pi/2-u(t_i)+\kappa .
~~~

Use product rims of radius $`4s`$ and smooth the metrics from above on radial annuli of width $`s`$ as in the previous construction. They dominate the original metrics on retained pieces. Each cylinder costs $`8\pi s L_i`$ area. The torus costs $`100r^2`$ and the changes on the finitely many annuli cost $`O(s^2)`$ each. Choose $`r`$ small and then $`s`$ arbitrarily small to control the area. [Smooth rims and estimates on the Euclidean patch](issue163_gradient_constraints.md#local-realization-at-arbitrarily-small-added-area)

Take $`\kappa\gt 2(\xi+2s)`$, with all three parameters tending to zero after $`r`$ is fixed. Antiperiodicity and the angular Lipschitz bound give

~~~math
 L_i+L_j=\pi-u(t_i)-u(t_j)+2\kappa
 \ \ge\ d_{S^1}(t_i,t_j)+2\kappa .
~~~

Any excursion from the old piece across the torus to the old piece costs at least $`L_i+L_j`$. Between the same rim points the original surface has a path of length at most $`d_{S^1}(t_i,t_j)+2(\xi+2s)`$, through the two boundary labels. The comparison also holds for returning through the same cylinder. Partial cylinder visits project to the entrance rim without increasing length. By replacing excursions, distances between retained old points dominate their original distances in $`M_0`$. In particular all external boundary distances are preserved. Paths of finite length have only finitely many full crossings because the finitely many cylinder lengths are positive.

For $`|y-o|\le\rho`$ in the new disk, a direct route through mouth $`i`$ to a boundary label $`t`$ costs at most

~~~math
 r+\rho+L_i+d_{S^1}(t_i,t)+O(\xi+s).
~~~

The constants may depend on the finite net. Small detours around drilled holes and travel along rims have cost $`O(s)`$ per hole. If a shortest path first exits the central piece through mouth $`j`$, it costs at least $`r-\rho-s+L_j+d_{S^1}(t_j,t)-(\xi+2s)`$. The initial part projects to the flat torus, and the terminal part uses the comparison on the old piece. Choosing $`i`$ within $`\delta`$ of $`t`$ gives

~~~math
 (1-k)d_{S^1}(t_j,t)\le (1+k)\delta+2\rho+O(\xi+s) .
~~~

Here we used $`u(t_j)-u(t)\le k\,d_{S^1}(t_j,t)`$. The same estimates bound the distance to $`t`$ between $`r+\pi/2-u(t)+\kappa-\rho-O(\xi+s)`$ and $`r+\pi/2-u(t)+\kappa+(1+k)\delta+\rho+O(\xi+s)`$. Thus the detours can be made small uniformly around the full circle.

To control initial directions, compare the minimizer to the direct route through its **own** first exit $`j`$. Its central portion projects to a curve ending within $`s`$ of $`p_j`$ of length at most $`r+\rho+O(\xi+s)`$. The first $`r/3`$ lies in untouched Euclidean coordinates. For fixed $`r`$ and finite net, as $`\rho,\xi,s\to0`$ this segment's direction converges uniformly to $`w_j`$. Otherwise compactness of arclength-parametrized projected paths would give a limiting length-$`r`$ curve from $`o`$ to $`p_j`$ different from their unique straight segment. The inequality for $`d_{S^1}(t_j,t)`$ and uniform continuity of $`v`$ control $`|w_j-v(t)|`$. First take the net fine relative to $`1-k`$, then choose $`r`$ and finally $`\rho,\kappa,\xi,s`$ small. At differentiability points $`\nabla r_t`$ is the negative of the initial unit direction toward $`t`$. Antiperiodicity of $`v`$ gives the claimed bounds for $`\nabla F_t`$ and $`\nabla H_t`$.

## Two tests of the construction

In the earlier long-cylinder construction the two-leg distance tends to $`20\pi+2r`$ on the sampled pairs as the mouth sizes tend to zero. The new exponential coordinate has gradient norm at most $`e^{-19}+o(1)`$ there. Projection of the zero profile onto the distance intervals makes every sampled coordinate constant on the patch. Thus the detour estimate detects a concrete geometric realization which the earlier gradient-only estimate can miss. [Earlier distance construction](issue163_gradient_constraints.md)

The short cylinders give the opposite test. Take the strict neighboring profile and the unit directions of its published rational planar witness. Interpolate these directions continuously around a half circle and extend antipodally. Interpolate the profile linearly including the antiperiodic wrap. Both the original and the exponential coordinates approach a raw value of at least $`0.999701090`$ in the open cell. Moreover, indices 0, 58 and 110 alone are isotropically distributed with weights respectively above $`0.323649`$, $`0.343956`$ and $`0.332393`$. The directions therefore pass the angular test below as well. Reweighting the coordinate by the route length still leaves the ceiling of $`6.09774`$ on globally rescaling this fixed calibration. [Exact neighboring witness](issue163_planar_comass.md#how-far-can-a-better-global-normalization-go)

For the exact check let $`z`$ be the rational witness, $`w_j=z_j/|z_j|`$ and $`L=1+4\cdot10^{-8}`$. Integer comparisons of squared row lengths give $`\|w-Lz\|_\infty\le10^{-8}`$. The old diagonal $`D`$ satisfies $`-D\preceq -iY/2\preceq D`$ and $`\mathrm{tr}(D)\le U`$. Cauchy–Schwarz after scaling by $`D^{-1/2}`$ therefore bounds $`|x^*(-iY/2)y|`$ by $`U\|x\|_\infty\|y\|_\infty`$. It follows that $`Q_Y(w)\ge L^2Q_Y(z)-10^{-8}(2+10^{-8})U`$. The doubled-angle vectors $`(\Re w_j^2,\Im w_j^2)`$ are rational. The three barycentric weights of zero in their triangle are proportional to the opposite signed determinants. The checker verifies all three weights exceed $`8/25`$ and gives their decimal floors. Zero mean doubled angle is exactly $`\sum_j\lambda_jw_jw_j^T=I/2`$ for the associated real unit vectors. [Integer replay](issue163_planar_comass.cjs)

The construction also tests the proposed continuum correction with action above $`6.22`$. Its rotating cylinder argument gives an independent planar comass strictly above $`491`$. At the profiles used there the form depends continuously on the profile in the uniform norm and on finitely many integrals of the two gradient components against continuous angular weights. This follows by differentiating the displayed primitives, which depend on the nonlinear first Fourier coordinate and its residual moment. Any continuous disk-valued antiperiodic gradient test can be approximated in these integrals by continuous unit-valued antiperiodic tests. Partition a half circle into short intervals. On each, realize the desired mean by two unit vectors with the corresponding length fractions, then join the endpoint values on arbitrarily short subintervals and extend antipodally. Uniform continuity of the weights bounds the errors, including those of the joins. Apply the local realization theorem, then use the strict margin above $`491`$. The value above $`491`$ occurs on actual fillings, on positive-area patches, even starting from a filling arbitrarily close to the infimum. This rules out the proposed $`1.0114`$ pointwise norm for that continuum form on genuine distance data. [Continuum form and rotating cylinder proof](issue163_interior_candidate.md#a-rotating-path-obstruction)

## How much area can carry nearly parallel gradients?

The following estimate holds on every filling. Suppose an interior open set $`O`$ has a smooth unoriented line field. Suppose for each label, at almost every point of $`O`$, the gradient of $`G_a`$ either has norm at most $`1/\sqrt2`$ or its line makes angle at most $`\arctan(1/3)`$ with that field. Then

~~~math
 A\ge I+\tfrac14\,\mathrm{Area}(O),
 \qquad A<6.15\ \Longrightarrow\ \mathrm{Area}(O)<0.216361 ,
~~~

where $`I`$ is the all-genus infimum. In checking the angular condition one may discard every label whose route through the point has length at least $`(1+\tfrac12\log2)\pi`$, because its gradient already satisfies the small-norm alternative.

Indeed take the metric with eigenvalues $`9/8`$ along the line and $`1/2`$ across it, in an old orthonormal frame. Its area density is $`3/4`$. Small covectors have new squared norm at most $`2|\zeta|^2\le1`$. For a unit covector in the indicated cone, $`\sin^2\theta\le1/10`$ and its new squared norm is at most $`8/9+(2-8/9)/10=1`$. Every $`G_a`$ is protected. On a compact subset of $`O`$ use this metric and interpolate smoothly to the old one in an open neighborhood with arbitrarily small extra area beyond the compact subset. Convex interpolation preserves the inequalities $`\zeta\otimes\zeta\preceq g`$ for all protected covectors. All densities on the transition are bounded by a universal constant. Exhaust $`O`$ by compact subsets. The boundary values of the $`G_a`$ preserve circle distances in each comparison and taking the infimum gives the estimate. The decimal uses the unconditional $`C\le I`$. [Certified area constant](issue163_detour_comparison.md)


## A restriction on smooth area minimizers

Suppose a smooth isometric filling minimizes area locally under smooth interior metric perturbations preserving the external distances. At every interior point $`x`$, let $`V_x`$ be the set of unoriented unit tangent lines of **minimizing** antipodal chords through $`x`$. Then in an orthonormal frame

~~~math
 \tfrac12 I=\sum_{\nu=1}^{m}\lambda_\nu v_\nu v_\nu^{T},\qquad
 v_\nu\in V_x,\qquad \lambda_\nu\ge0,\qquad \sum_\nu\lambda_\nu=1,\qquad m\le3 .
~~~

In particular, if there are exactly two lines they are perpendicular. Related variations for systolic curves are treated in Calabi's work. The following argument uses the boundary-distance coordinates for the circle specifically. Existence of a smooth all-genus minimizer is open. [Calabi, *Extremal isosystolic metrics for compact surfaces*](https://smf.emath.fr/publications/extremal-isosystolic-metrics-compact-surfaces)

If there are no such lines then $`\min_a H_a(x)\gt 0`$, so uniform conformal shrinking decreases area near $`x`$ by the metric comparison. Otherwise the contact labels $`H_a(x)=0`$ form a compact set. For such a label any shortest paths from $`a`$ and $`b`$ to $`x`$ concatenate to a minimizing path. Their unit terminal velocities at the interior point must be opposite for every pairing. Thus the velocity from each endpoint is unique at $`x`$. Terminal velocities at nearby interior points and labels vary upper semicontinuously, by compactness of minimizing paths and convergence of their last short segments in a convex normal ball.

If $`I/2`$ were outside the convex hull of $`vv^T`$ over $`V_x`$, separation in the trace-one symmetric matrices would give a symmetric tensor $`S`$ with $`\mathrm{tr}(S)\lt 0`$ and $`v^TSv\gt 0`$ for every contact direction. Indeed first separate by a strict gap and then add a scalar multiple of $`I`$. Extend $`S`$ in a local orthonormal frame. Any sequence of covectors $`dG_a`$ at differentiability points tending to $`x`$ with norms tending to one must approach the compact set of contact directions up to sign. The exponential bound forces $`H_a\to0`$, and the formula for $`dG_a`$ and upper semicontinuity of both terminal velocities give the assertion along every convergent subsequence of labels. There is consequently a smaller neighborhood and a uniform positive lower bound for $`S(dG_a,dG_a)`$ whenever $`|dG_a|`$ is sufficiently close to one (identify covectors with vectors using the old metric).

For a nonnegative smooth bump $`\chi`$ in that neighborhood, replace $`g`$ by $`g+\tau\chi S`$ for small $`\tau\gt 0`$. The squared dual norm of a covector $`\zeta`$ changes by $`-\tau\chi S(\zeta,\zeta)+O((\tau\chi)^2)|\zeta|^2`$ uniformly. The preceding lower bound protects all nearly unit covectors, and the others have uniform slack. Hence every $`G_a`$ stays 1-Lipschitz, using its almost-everywhere gradient bound for the new smooth metric. Its boundary values protect every boundary distance. The first variation of area is $`\int\chi\,\mathrm{tr}(S)\,dA/2\lt 0`$, a contradiction. Carathéodory's theorem in the two-dimensional trace-one affine plane gives $`m\le3`$. The metric compression estimate for arbitrary fillings applies even when a minimizing sequence has no smooth limit. [Unconditional metric compression](issue163_detour_comparison.md#metric-compression-on-a-whole-region)
