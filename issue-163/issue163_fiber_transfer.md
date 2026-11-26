# What the shortest distances force on different sheets of a disk projection

Let a compact oriented Riemannian filling have area $`A`$ and boundary isometric to the circle of length $`2\pi`$. For **every** triangulated disk projection described below, the 112 antipodal distance coordinates force

~~~math
 A+E_{112} \ \ge\ \frac{111}{112}\,2\pi=6.22708543836548\ldots .
~~~

Here $`E_{112}`$ is a nonnegative excess measured where several points of the filling project to the same point of the disk. It depends on their **joint** distance gradients. A filling with $`A\le6.15`$ must have $`E_{112}\gt0.0770854`$ on every such projection. Using a nested dense set of labels raises the required excess to more than **0.1331853**. Any one-to-one region contributes zero regardless of the shape or distortion of its tangent planes. A test using only two-by-two Jacobians forces more than **0.0667579** of disagreement between sheets even though every individual signed discrepancy integrates to zero. The unconditional area certificate remains **6.096292737690900167**. [Area certificate](issue163_anchor_occupation.md) · [Scalar and witness replay](issue163_fiber_check.py)

## Signed transfer of the distances

Use $`n\ge2`$ antipodal pairs, $`h=\pi/n`$ and $`p_j=\gamma(jh)`$, with indices modulo $`2n`$. Write $`F_j=(d(\cdot,p_{j+n})-d(\cdot,p_j))/2`$. Each coordinate is 1-Lipschitz, $`F_{j+n}=-F_j`$, and $`F_j(\gamma(s))=\pi/2-d_{S^1}(s,jh)`$.

Triangulate the filling and map it to an oriented polygonal disk $`D`$ by a map $`f`$ affine of rank two on each triangle in its parameter coordinates. Require an orientation-preserving boundary homeomorphism, piecewise affine in boundary arclength, and $`f^{-1}(\partial D)=\partial M`$. There are such maps in every genus. Subdivide to give each triangle an interior vertex and to keep only boundary edges between boundary vertices, take a strictly convex boundary polygon with the prescribed cyclic vertices, and assign interior vertices generic interior images. The estimates also apply to a fixed target polygon with subdivided sides when all triangles have rank two. For example one can approximate a projection by two distance coordinates into their pair parallelogram by refining the source and perturbing interior vertex images into the interior of that parallelogram. Include its four boundary corners as vertices.

Off the finitely many images of edges, let $`x_i(y)`$ be the inverse branches and $`\epsilon_i=\pm1`$ their orientation signs. Their sum is one by the boundary degree. Let $`a_i\,dy=x_i^*dA`$ as unsigned measures in planar coordinates. For each label transfer its scalar value to the disk by the signed sum

~~~math
 U_j(y)=\sum_i\epsilon_i F_j(x_i(y)),\qquad
 K_n(y)=\mathrm{conv}\{\pm dU_j(y):0\le j\lt n\}.
~~~

Each $`U_j`$ extends to a Lipschitz function. Across a regular edge a continuing branch has the same trace, and two branches that end together have opposite signs and equal values there. At a vertex, group branches by their limiting source point. The signed count of each group is its local degree, constant nearby, by taking a small neighborhood disjoint from the other preimages. At a boundary vertex the single limiting source point and total degree one give the boundary trace. Bounded derivatives on the finitely many inverse triangles and continuity give the Lipschitz bound. Thus $`U_j`$ has exactly the original triangular trace on the disk. Set

~~~math
 E_n(f)=\int_D\left(\frac{|K_n(y)|}{\pi}-\sum_i a_i(y)\right)_+dy .
~~~

The expression is independent of the target coordinate chart. On a single sheet $`K_n`$ is contained in the pulled-back unit cotangent disk, an ellipse of area $`\pi a_1`$. The same conclusion holds on a fiber where all the pulled-back rows $`d(F_j\circ x_i)`$ agree across sheets for each $`j`$. The signed sum leaves just one copy. In particular repeatedly superposing a common graph of all the coordinates over two of them cannot pay this excess, even with reversed sheets.

## The finite disk inequality

For any Lipschitz functions $`U_j`$ on the disk with these traces,

~~~math
 \frac1\pi\int_D |K_n|\,dy\ \ge\ 2\pi(1-1/n).
~~~

To see the shortest-distance input, give the disk the seminorm $`v\mapsto\max_j|dU_j(v)|`$. Its unit cotangent body is $`K_n`$, and its Holmes–Thompson area density is $`|K_n|/\pi`$. Every path from anchor $`p_j`$ to the boundary point $`\gamma(s)`$ has length at least $`d_{S^1}(jh,s)`$ by the single coordinate $`U_j`$. Along the boundary the seminorm gives unit speed. The argument below justifies these comparisons for smooth metrics approximating the integral.

For a smooth strongly convex reversible Finsler metric on a disk, let $`r_j`$ be the distance from its boundary anchor $`p_j`$. At common differentiability points the ordered list of these covectors traces a convex polygon on the unit cotangent circle in boundary order, allowing repetitions. The unit cotangent body contains this polygon, giving the integrated bound below. [Ivanov, Example 3.2, Lemma 3.6 and Proposition 3.7](https://arxiv.org/pdf/0910.2257)

~~~math
 \mathrm{Area}_{\mathrm{HT}}(D)\ge
 \frac1{2\pi}\sum_{j=0}^{2n-1}\int_{\partial D}r_j\,dr_{j+1}.
~~~

For the circle distances the consecutive pair on the boundary traces its parallelogram once positively, of area $`2h(\pi-h)`$. Translating both coordinates or changing both signs preserves the oriented area. The sum divided by $`2\pi`$ is $`2\pi(1-1/n)`$.

Here are the approximation details. First interpolate the finitely many $`U_j`$ on shape-regular uniform refinements of a target triangulation with boundary vertices at the trace breakpoints. This preserves the piecewise affine traces. The differentials are uniformly bounded and converge almost everywhere to $`dU_j`$. At a differentiability point the vertex errors from its affine tangent are $`o(\ell)`$ on a triangle of diameter $`\ell`$, and shape regularity bounds the inverse edge matrix by $`O(1/\ell)`$. Dominated convergence gives convergence of the integrated convex hull areas.

For each fixed interpolant, dominate its piecewise constant seminorms by smooth strongly convex norms on each face with arbitrarily small uniform error on unit vectors. For instance smooth their support functions by angular averaging and add a small Euclidean norm to dominate the approximation error and give positive curvature. Near the internal edges and the finitely many vertices pass to a common large background norm, interpolating by positive convex combinations on each incident face. Corners admit sector charts bi-Lipschitz to a half disk, so shrinking their neighborhoods costs vanishing area. The resulting smooth metrics dominate length variation of every interpolated coordinate, including on edges where the tangential derivatives agree. Their areas tend to the desired polygonal area. Their boundary speeds stay uniformly bounded for the fixed interpolant and their boundary lengths tend to $`2\pi`$, since the interpolated traces have unit maximum speed on each open boundary edge. The distances $`r_j`$ on the boundary lie between the circle distances and those distances plus the total excess boundary length. These boundary distance functions converge uniformly and have uniformly bounded variation. Integration by parts therefore gives convergence of each $`\int r_j\,dr_{j+1}`$. This proves the finite disk inequality and hence $`A+E_n(f)\ge 2\pi(1-1/n)`$.

Fixing $`f`$ and doubling the label count makes the hulls nested. All lie in the sum of the sheet ellipses, a bounded body for a fixed finite projection. Monotone convergence gives $`A+E_\infty(f)\ge2\pi`$. Only countably many coordinate differentials are used in this limit.

## A necessary two-dimensional discrepancy between sheets

There is a coordinate test for the excess that uses only determinants of pairs of scalar differences. Put $`u_{ir}=F_r\circ x_i`$ and define $`L_{rs}\,dy`$ by

~~~math
 \begin{split}
 L_{rs}\,dy
 &=\sum_i\epsilon_i\,du_{ir}\wedge du_{is}-dU_r\wedge dU_s \\[2pt]
 &=\sum_{i\lt k}\epsilon_i\epsilon_k\,d(u_{ir}-u_{kr})\wedge d(u_{is}-u_{ks}).
 \end{split}
~~~

Expansion of the two sides uses $`\sum_i\epsilon_i=1`$. Every individual $`L_{rs}`$ integrates to **zero**. The first term integrates to $`\int_M dF_r\wedge dF_s`$ by signed change of variables, and Stokes gives the same boundary integral for $`U_r,U_s`$. Nevertheless every filling and every projection satisfy

~~~math
 \boxed{\quad
 A+\frac{2}{\sqrt3}\int_D\max_{r\lt s}|L_{rs}(y)|\,dy
 \ \ge\ 2\pi(1-1/n).\quad}
~~~

At $`A\le6.15`$ the integral must exceed **0.0667579** on 112 antipodal pairs, **0.0910499** on 224 pairs, and **0.1153418** on a nested dense set. In particular, on fibers where each pair of sheets differs in at most one independent differential direction across the labels, all these discrepancies vanish, however large the first derivatives are. The dense statement follows by monotone convergence of the pointwise maxima.

Here is a proof of the coefficient. In target coordinates write $`w_r=dU_r`$ as column vectors. Choose probability weights $`p_r`$ maximizing the determinant of $`T=\sum p_r w_rw_r^t`$. If the rows span a line then $`|K_n|=0`$. Otherwise $`T`$ is positive definite, and varying the weights toward any individual row gives $`w_r^tT^{-1}w_r\le2`$, with equality on the support. The ellipse defined by this inequality contains the transferred polygon and has area $`2\pi\sqrt{\det T}`$. The supported matrices $`T^{-1/2}w_rw_r^tT^{-1/2}`$ have trace two. Their weighted average is the identity, so planar Carathéodory in the trace-two affine plane allows weights on at most three rows with the same $`T`$.

By the two-column Gram determinant identity, $`\sqrt{\det T}`$ is the Euclidean norm of the list $`\sqrt{p_rp_s}\det(w_r,w_s)`$ for $`r\lt s`$. Split this list by the first formula for $`L_{rs}`$ and apply the triangle inequality. On sheet $`i`$ the analogous norm is at most $`a_i/2`$. Indeed in an orthonormal source frame the weighted covariance has trace at most one since every original gradient has norm at most one. The positive square root of its determinant is at most half its trace, and pulling back multiplies it by $`a_i`$. For the discrepancy list, $`\sum_{r\lt s}p_rp_s\le1/3`$ since at most three weights sum to one. This proves the pointwise bound

~~~math
 |K_n|/\pi\le \sum_i a_i+(2/\sqrt3)\max_{r\lt s}|L_{rs}|.
~~~

For a direct target, write $`B=6.096286779581369797\ldots`$ for the signed finite calibration action. An upper bound of $`1.242(A-B)`$ on the 112-pair discrepancy integral, for some projection of each filling, would already imply $`A\gt6.15`$. It is possible to keep every pairwise boundary integral correct while missing this constraint, because the test measures where their signed Jacobians disagree after transferring the coordinates to a common disk.

### Four labels on actual distance data

One can take two prescribed distance coordinates as the disk projection in a precise approximation sense. Fix two distinct nonantipodal labels $`a,b`$ on the grid. On refinements of a fixed smooth source triangulation interpolate all $`F_j`$ at the vertices, preserving the boundary traces. Use shape-regular meshes in the triangle parameters, with arclength parameters on the boundary edges, including the breakpoints of the traces. The interpolated pair $`(F_a,F_b)`$ lies in its convex pair parallelogram and is a homeomorphism from the boundary onto its perimeter. Perturb just the interior vertex images of this pair generically into the interior, by $`o(\ell_{\min})`$ where $`\ell_{\min}`$ is the least mesh diameter. This gives a projection $`f_m`$ of the required rank once no internal edge joins two boundary vertices. The interpolants, including the two perturbed coordinates, have uniformly bounded differentials and their gradients converge almost everywhere to the original gradients by the affine tangent argument above. Thus the source area budget for the row estimate can be taken as

~~~math
 A_m=\int_M\max\{1,\max_j|dF_{j,m}|_g^2\}\,dA\ \longrightarrow\ A .
~~~

For these projections the $`a,b`$ coordinates on *every* inverse sheet equal the two target coordinates, so $`L_{rs}=0`$ when either $`r`$ or $`s`$ is one of them. The preceding bounds hold with $`A_m`$. At $`A\le6.15`$ the lower limit of the 112-pair discrepancy integral over **the other labels** is at least $`(2\pi\cdot111/112-6.15)\sqrt3/2\gt0.0667579`$. This statement accommodates genuine pair maps that collapse an open set or have critical values.

There is also a collision interpretation at each finite approximation. For fixed $`r,s`$ among the remaining labels and an offset $`v\in\mathbb R^2`$, count ordered pairs of distinct source points with identical $`a,b`$ coordinates and with $`r,s`$ coordinates differing by $`v`$. Count in the open regular cells. For these piecewise affine maps the cell edges give only finitely many image segments in offset space. The area formula says the integral of this count over offsets equals

~~~math
 2\int_D\sum_{i\lt k}\left|\det\big(d(u_{ir}-u_{kr}),d(u_{is}-u_{ks})\big)\right|\,dy .
~~~

For almost every offset the **signed** count is zero, with sign $`\epsilon_i\epsilon_k`$ times the Jacobian sign of the difference map. To see this, integrate any smooth test two-form in offset space against the signed count. It has a smooth primitive on the plane. Apply Stokes to its pullback by each ordered sheet difference on each cell, with sheet sign $`\epsilon_i\epsilon_k`$. One may include the diagonal pairs, which pull every positive-degree form back to zero. Across an interior edge, group all ordered pairs by their two limiting source points. Their signed multiplicities agree on the two sides by the same local degree rule as for the scalar transfer, and the limiting difference and its tangential derivative agree. On the outside edge the two points coincide, so the difference is constant. All boundary terms cancel. A discrepancy therefore requires opposite-sign collisions, even with the offset specified. Large motion in a single residual coordinate cannot produce this obstruction.

## Testing a repeated near-maximizer

A triple fiber has signs $`+,+,-`$. Suppose its three inverse branches are similarities of the same scale in oriented orthonormal source frames. Suppose also that all three source arrays of gradient directions are rotations of one array $`z_j\in\mathbb C`$, with the same boundary label indices. Write $`H=\mathrm{conv}\{\pm z_j\}`$. In units of the common scale the transferred rows have the form $`Cz_j+D\overline{z_j}`$ with $`|C|\le2`$ and $`|D|=1`$. The two positive rotations give $`C`$ and the negative branch reverses orientation. The absolute real determinant is $`|\,|C|^2-|D|^2\,|\le3`$. Thus the transferred hull has density at most $`|H|/\pi`$ times the **total** source area density of the three sheets. This also holds on one sheet. For the published 112-vector planar near-maximizer, the integer convex hull gives

~~~math
 0.9847407\lt |H|/\pi\lt0.9847408 .
~~~

Such triples contribute zero positive excess for all choices of the three rotations. For a separate test permitting different arrays and sheet metrics, choose a positive reference sheet with area density $`a_0`$, and pair the remaining positive and negative sheets arbitrarily. Write $`t`$ for the sum over pairs of the largest labelwise norm of $`d(F_j\circ x_+)-d(F_j\circ x_-)`$, measured in the reference dual metric. Then $`K_n`$ lies in $`(1+t)`$ times the reference ellipse. On three sheets of equal area density, $`t\le\sqrt3-1`$ already suffices for zero excess. These tests distinguish multiplicity itself from the relative distance information carried by different sheets. [Published planar array and its cell](issue163_planar_comass.md)

The finite normalized calibration has action $`B=6.096286779581369797\ldots`$ and pointwise density at most one. An upper estimate $`E_{112}(f)\le1.435(A-B)`$ for a suitably chosen projection on each filling would give $`A\gt6.15`$. The new lower constraint holds for every projection. This upper estimate, or a stronger estimate after taking dense labels, remains open. [Finite calibration](issue163_anchor.md)

### How much of a filling could use the published gradient array?

There is a simpler test of the specific near-maximizer that uses no projection and makes no assumption about the scalar profile. On the 224 signed labels let $`z_j\in\mathbb C`$ represent the spatial gradient in an oriented orthonormal frame. Give arrays their root mean square norm. Write $`Jz_j=z_{j+56}`$, so $`J^2=-I`$ by antipodality, and put $`P_-=(I+iJ)/2`$. This is an orthogonal projection. The signed pair degree gives exactly

~~~math
 \int_M\frac1{224}\sum_j\Im(\overline z_j z_{j+56})\,dA=\pi^2/2,\qquad
 \frac1A\int_M\|P_-z\|^2\,dA\le\tfrac12\left(1-\frac{\pi^2}{2A}\right).
~~~

Indeed $`2\|P_-z\|^2=\|z\|^2-224^{-1}\sum_j\Im(\overline z_j z_{j+56})`$ and $`\|z\|\le1`$. At $`A\le6.15`$ the upper bound is less than **0.098797**. On the published witness the quarter-turn determinant averages **0.6043893**. Every individual determinant exceeds 0.27922. Its projected norm is greater than **0.4447530**. The sample average needed across a filling of area at most 6.15 exceeds **0.8024068**. Using the witness everywhere, even with pointwise grid and frame rotations, would force area above **8.16**. Using it on half the area already forces area above **6.1516**, since the complement contributes at most one per unit area.

Allow an arbitrary tangent-frame rotation and cyclic relabeling of the witness at each point. Reflection of both variables also preserves the norm, and reversing either one alone exchanges the two orthogonal projections. The complementary witness norm is larger. If the local root mean square distance to this orbit is at most $`\eta`$, its projected norm is at least $`0.4447530-\eta`$. Integrating the square proves that, for $`A\le6.15`$,

- **more than 50.05 percent** of the area must differ from the exact orbit.
- **more than 36.59 percent** must differ by more than 0.05 in root mean square norm.

One may allow arbitrary fractional label shifts by linearly interpolating the published angular samples. Between consecutive shifts the projected array runs along a segment between vectors of equal norm. Its minimum norm occurs at the midpoint. The same integer calculation for both projections gives a minimum greater than 0.43513 across all fractional shifts. Even with this additional freedom **more than one third** of the surface must differ by over 0.05. Thus the published vectors can occur on a patch, but using them throughout a putative filling misses a compulsory flux by a measurable amount. Other arrays can carry the missing flux, so this occupancy estimate alone leaves the area bound open.

### Can adding this flux to the finite calibration reach 6.15?

For arbitrary **real** coefficients on the signed single-anchor calibration and the constant quarter-turn form, two planar tests give an action ceiling of **6.09878** under pointwise comass certification. The raw obstruction above is therefore diagnostic even though its simplest direct use has little room. [Two matrix evaluations and exact dual weights](issue163_quarter_test.cjs)

Denote the two normalized densities by $`W,Q`$. Their boundary integrals are $`B=b\pi^2`$ and $`\pi^2/2`$. The first test is the published neighboring cell, including its single-anchor correction. The second has scalar coordinates $`F_j/h=1/100`$ for $`0\le j\le56`$ and $`-1/100`$ for $`57\le j\le111`$, extended antipodally. All angular slopes are strictly inside the allowed interval. Its gradients are rational disk approximations of $`e^{ijh}`$, with the second quarter obtained by rotating the first by a right angle. The two evaluated pairs $`(W_i,Q_i)`$ are approximately $`(0.999230,0.604389)`$ and $`(0.999928,1.000000)`$. The replay uses their exact rational values.

Solve the two linear equations $`u_1W_1+u_2W_2=b`$, $`u_1Q_1+u_2Q_2=1/2`$. Both weights are positive and $`6.09877808\le\pi^2(u_1+u_2)\lt6.09878`$. If $`\lambda W+tQ`$ has pointwise comass at most one, its evaluations on both tests are at most one. Multiplying by $`\pi^2u_i`$ and adding gives the stated action ceiling simultaneously for all $`\lambda,t\in\mathbb R`$. The four-label comparison above tests data that these two scalar actions leave free.

## A comparison using inverse lengths

There is also a Riemannian calculation for a smooth map $`P:M\to S^2_+`$ taking the interior into the open hemisphere and the boundary to its equator by arclength and with positive orientation. For a uniform unit tangent vector $`v`$ at $`P(x)`$, set $`m(x)=\mathbb E_v|dP_x^*v|`$, let $`J`$ be the signed Jacobian and put $`e=\|dP\|_{\mathrm{HS}}^2/2`$. Then

~~~math
 2\pi\le\int_M m\,dA,\qquad
 \frac{4\pi^2}{A}-2\pi\le
 2\int_M J_-\,dA+\frac8{\pi^2}\int_M(e-|J|)\,dA\ \le\ \int_M(e-J)\,dA .
~~~

For almost every great circle normal $`n\in S^2`$, the inverse image of $`n\cdot P=0`$ is a compact one-manifold with just two boundary points. They are antipodes, so its interval component has length at least $`\pi`$. Regularity follows by Sard on the incidence set, since variation in $`n`$ is transverse at zero. Coarea on that set gives mean inverse length $`\tfrac12\int m\,dA`$. Indeed $`n\cdot P(x)`$ has density $`1/2`$ at zero and the conditional direction of $`n`$ is uniform in the tangent plane. The signed area integral is $`2\pi`$ by the boundary degree.

For singular values $`s_1\ge s_2\ge0`$ put $`p=(s_1+s_2)/2`$ and $`t=(s_1-s_2)/(s_1+s_2)`$ when $`p\gt0`$. The mean length is $`p\sum_{k\ge0}{1/2\choose k}^2t^{2k}`$, by averaging $`|1+t e^{i\theta}|`$. Its square divided by $`p^2`$ is convex in $`t^2`$ by its nonnegative coefficients. Its endpoint values are 1 and $`16/\pi^2`$. The secant bound gives $`m^2\le |J|+(8/\pi^2)(e-|J|)`$, including the rank-one equality case. Cauchy–Schwarz and the signed integral give the display. The same estimates hold for Lipschitz maps by strong first-order approximation with the boundary trace fixed, for instance in the stereographic closed unit disk by interpolation and smoothing, with a collar restoring the smooth equator trace.

At $`A\le6.15`$ every such map must spend more than **0.1360695** in $`\int(e-J)`$. Conformal expansion contributes zero to this quantity. For the map obtained by inverse stereographic projection of $`T=(\pi/2)\langle F_a e^{ia}\rangle`$, the older neighboring-cell witness has $`e-J\gt0.139`$ on a single tangent frame. Here $`\langle\cdot\rangle`$ is uniform angular probability. Integration by parts against the sine shows $`|T|\le1`$ from angular Lipschitz continuity, and the boundary triangle gives $`T(\gamma(s))=e^{is}`$. If $`z_a=\partial_1F_a+i\partial_2F_a`$, direct differentiation gives

~~~math
 e-J=\frac{\pi^2}{2(1+|T|^2)^2}\,|\langle z_a e^{ia}\rangle|^2 .
~~~

For this test interpolate both scalar values and gradient rows linearly between the published angular samples and extend antipodally. The first Fourier moment of the interpolant is the sample moment times $`(\sin(h/2)/(h/2))^2`$. The strict scalar inequalities allow these gradients on a sufficiently small planar patch of the relaxation. The certified normalized bisected-gap density there exceeds 0.99970, and after the later single-anchor correction the density still exceeds 0.99922. Thus this first Fourier map fails the pointwise comparison with finite slack by a factor exceeding 170 even for the later field. An integrated estimate can also use the way different patches fit together. [Old cell and exact evaluation](issue163_planar_comass.md) · [Single-anchor coefficients](issue163_anchor.md) · [Replay](issue163_fiber_check.py)

From the repository's <code>issue-163</code> directory, both exact checks run without an optimizer.

~~~sh
python3 issue163_fiber_check.py
node issue163_quarter_test.cjs
~~~
