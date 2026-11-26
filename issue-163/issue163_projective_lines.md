# Projective lines on a three-sheeted cover

For a genus-two isometric filling of the circle of length $`2\pi`$, the conjectured lower bound holds if the orientation double of its antipodal quotient admits a cyclic conformal cover of the sphere of degree three on which the real involution acts on the deck group by inversion and covers the antipodal map. These hypotheses include nonhyperelliptic surfaces. On the explicit double $`y^3=z^6+1`$ the estimate is

~~~math
 A\ \ge\ \frac{2\pi}{D_*}=13.504192\ldots,\qquad
 D_*=\frac13+\frac{13\,\zeta(3)}{12\pi^2}.
~~~

Consequently $`2\pi`$ also holds throughout a neighborhood of this example, for smooth markings of conformal distortion at most $`1/D_*=2.149258\ldots`$. The hypothesis on the conformal structure still leaves the general genus-two problem open. There are examples of the cyclic-cover criterion for every filling genus $`g\ge 2`$. The argument uses the lengths of individual lifts of projective lines. [Bangert, Croke, Ivanov and Katz on genus one and hyperelliptic doubles](https://arxiv.org/abs/math/0405583) · [Unrestricted numerical bound](issue163_distance_balls.md)

The subsequent arc-exchange argument proves $`2\pi`$ for **every cyclic trigonal genus-four double**, including the commuting clustered examples below. A quantitative deformation also gives area above 7.42 on an explicit double with trivial holomorphic automorphism group. [Cyclic companion curves](issue163_cyclic_companions.md) · [Asymmetric example](issue163_asymmetric_genus_two.md)

## What a line on the quotient measures

Identify antipodal boundary points of the filling $`M`$ to obtain $`N`$, of the same area $`A`$. Its seam is a one-sided circle of length $`\pi`$. Every orientation-reversing loop in $`N`$ has length at least $`\pi`$. Indeed, split a transverse loop at its seam crossings. Each piece in the cut surface can be replaced by a shorter or equal boundary arc, since the boundary is isometrically embedded. Replacement preserves the orientation character because the orientation local system pulls back trivially to $`M`$. The resulting loop on the one-sided seam has odd winding. Approximation gives the assertion for rectifiable loops. For filling genus $`g`$, the quotient has nonorientable genus $`2g+1`$ and its orientation double $`X`$ has orientable genus $`2g`$, by Euler characteristic. Write $`\tau`$ for its deck involution.

Suppose a conformal branched covering $`f:X\to S^2`$ satisfies $`f(\tau x)=-f(x)`$ on the unit round sphere. It descends to $`\bar f:N\to\mathbb{RP}^2`$. Away from the finite branch set write the metric length element of $`N`$ as $`\rho\,ds_0`$, where $`ds_0`$ is pulled back from the round projective plane. Then $`A=\int_N \rho^2\,dA_0`$. This works for the continuous metric obtained by sewing the original boundary, whenever this is its conformal covering. Finite branch sets have area zero.

Choose a projective line $`\ell`$ with rotation-invariant probability. It avoids the branch values almost surely. If its sheet permutation has a cycle of length $`k`$, the corresponding closed lift has reference length $`k\pi`$. For odd $`k`$ it reverses orientation. Indeed the pullback of $`S^2\to\mathbb{RP}^2`$ is the orientation cover $`X\to N`$, and the line changes sheets on each circuit. Cauchy–Schwarz on that lift gives $`\int\rho^2\,ds_0\ge\pi/k`$.

For a nonnegative integrand on the base, its expected line integral is half its area integral, by rotation invariance and the ratio $`\pi/(2\pi)`$ of line length to base area. Apply this to the sum of $`\rho^2`$ over each fiber, using truncation if necessary. Thus in any degree and genus,

~~~math
 A\ \ge\ 2\pi\,\mathbb E_\ell
       \sum_{\substack{\text{cycles of }\ell\\ k\ {\rm odd}}}\frac1k ,
~~~

where $`k`$ denotes each cycle's length. In degree three, let $`p_1,p_3`$ be the probabilities of the identity and a three-cycle, respectively. A transposition has one fixed sheet. The estimate becomes

~~~math
 A\ \ge\ 2\pi\left(1+2p_1-\frac23p_3\right).
~~~

For example, $`p_3\le3p_1`$ suffices for $`2\pi`$. Even with $`p_1=0`$, a three-cycle probability at most $`0.0317`$ suffices for $`6.15`$.

## A fixed sheet on every line

Suppose $`f`$ is cyclic of odd degree $`d`$, with deck generator $`\sigma`$ and $`\tau\sigma\tau^{-1}=\sigma^{-1}`$. Label the sheets over a point of the sphere by $`j\in\mathbb Z/d`$ using $`\sigma`$. Lift a semicircle to the antipodal basepoint and use $`\tau`$ to return to the initial fiber. Path lifting commutes with the deck generator, while $`\tau`$ inverts it. The resulting permutation has the form $`j\mapsto c-j`$. It has exactly one fixed sheet since $`d`$ is odd. All remaining cycles have length two. The preceding inequality gives $`A\ge2\pi`$ for every filling in this conformal class.

For genus two take the smooth compactification of

~~~math
 y^3=z^6+1,\qquad
 \sigma(z,y)=(z,e^{2\pi i/3}y),\qquad
 \tau(z,y)=(-1/\bar z,\bar y/\bar z^2).
~~~

Projection to $`z`$ has six branch points of index three and is unramified at infinity (use $`y/z^2`$ there). Riemann–Hurwitz gives $`2g_X-2=-6+12=6`$. The displayed $`\tau`$ has square one, is fixed-point-free and inverts $`\sigma`$. This genus-four surface is nonhyperelliptic. If it also had a degree-two map to the sphere, the joint map to $`\mathbb P^1\times\mathbb P^1`$ would be birational onto its image since its generic degree divides both two and three. A curve of bidegree $`(2,3)`$ has arithmetic genus $`(2-1)(3-1)=2`$ by adjunction, and its normalization has genus at most two.

## The area gained when the selected sheet varies

At a regular point $`b`$ of the projective plane, use a uniform unoriented direction through $`b`$. Let $`w_i(b)`$ be the probability that sheet $`i`$ over $`b`$ belongs to the unique degree-one lift of this line. Then $`\sum_iw_i=1`$. Every selected lift has metric length at least $`\pi`$. Averaging length before applying Cauchy–Schwarz gives

~~~math
 \pi\ \le\ \frac12\int_{\mathbb{RP}^2}\sum_i w_i\rho_i\,dA_{\rm rd},
 \qquad
 A\ \ge\ \frac{2\pi}{\displaystyle
   \mathbb E_b\sum_i w_i(b)^2}.
~~~

Here $`b`$ is uniform in projective area. The direction in the incidence measure is uniform conditional on $`b`$, by rotation invariance. The denominator therefore measures sheet selection using the actual branched cover alone.

For the sextic example the three projective branch values are equally spaced in direction on the equator, at angular intervals $`\pi/3`$. Fix $`b`$ off the equator. The lines from $`b`$ through those values divide its direction circle into three intervals. The fixed sheet is constant on each interval. Crossing one of these directions changes monodromy by a conjugate of a local three-cycle, since the two nearby line loops differ by a detour around that branch value. The two resulting transpositions are distinct and have different fixed sheets. Consecutive intervals, including the last and first, thus have different sheets. All three sheets occur, with probabilities equal to the three angular intervals divided by $`\pi`$.

Lift $`b`$ to a unit vector $`p`$ and put $`t=|p_z|`$. In round projective area $`t`$ is uniform on $`[0,1]`$ and the azimuth is independently uniform. Orthogonal projection from the equatorial plane to $`p^\perp`$ sends each equatorial branch direction to its line direction at $`b`$. Its singular values are $`t,1`$, with the contracting axis at the azimuth of $`p`$. For a linear map $`T`$ between planes the absolute angular derivative at a unit vector $`u`$ is $`|\det T|/|Tu|^2`$. Thus the angular derivative here, measured from the contracting axis, is the Poisson kernel

~~~math
 \frac{t}{t^2\cos^2\theta+\sin^2\theta}
 =1+2\sum_{k=1}^{\infty} q^k\cos(2k\theta),
 \qquad q=\frac{1-t}{1+t}.
~~~

Each $`w_i`$ is the integral of this derivative over one interval of width $`\pi/3`$, divided by $`\pi`$. Squaring, averaging over the azimuth and summing the three intervals kills the cross terms by trigonometric orthogonality. For $`t\gt0`$ the series converges absolutely, and the resulting terms are nonnegative. Thus

~~~math
 \mathbb E_b\sum_i w_i^2
 =\frac13+\frac6{\pi^2}\sum_{k=1}^{\infty}
 \frac{\sin^2(k\pi/3)}{k^2}\int_0^1
 \left(\frac{1-t}{1+t}\right)^{2k}\,dt .
~~~

Since $`\log((1-t)/(1+t))\le-2t`$, the integral is at most $`1/(4k)`$. The squared sine is $`3/4`$ off the multiples of three and zero on them. The last display is therefore at most $`D_*`$, proving the stated area bound.

For the neighborhood result, pull a filling metric back by a smooth marking from this projective quotient and suppose the ratio of its two length singular values relative to the reference conformal structure is at most $`K`$. Off the branch set use the larger singular value as $`\rho`$. It dominates lengths and its square times reference area is at most $`K`$ times actual area. The same line proof gives $`A\ge 2\pi/(K D_*)`$. This allows perturbations of the conformal structure that break the cyclic symmetry. [Rational checks of the thresholds](issue163_conformal_check.py)

## How three-cycles can destroy this estimate

Take three distinct $`a_j`$ in a spherical cap of radius $`\varepsilon`$ centered at $`z=0`$, with $`\sin\varepsilon\le1/20`$. In stereographic coordinates set

~~~math
 H_a(z)=\frac{z-a}{1+\bar a z},\qquad
 y^3=\frac{H_{a_1}(z)H_{a_2}(z)}{H_{a_3}(z)},\qquad
 \tau(z,y)=(-1/\bar z,-1/\bar y).
~~~

Each factor satisfies $`H_a(-1/\bar z)=-1/\overline{H_a(z)}`$. This gives another fixed-point-free genus-four example with six points of index three, now with $`\tau`$ commuting with $`\sigma`$. For a great circle missing the two polar caps, the hemisphere containing the first cap contains two simple zeros and one simple pole. Full-circle continuation multiplies a cubic root by a nontrivial cube root of unity, by the argument principle. That continuation is the square of the projective-line permutation, so the latter is a three-cycle. A uniform great circle hits the polar caps with probability $`\sin\varepsilon`$, since the absolute polar coordinate of its unit normal is uniform on $`[0,1]`$. Even assigning the identity to every exceptional line, the right-hand side of the unweighted cycle estimate is at most

~~~math
 2\pi\left(\frac13+\frac83\sin\varepsilon\right)
 \ \le\ \frac{14\pi}{15}.
~~~

This bounds the certificate from projection to $`z`$. The other coordinate can give a substantially better result on the same surface.

### Switching projections on the same family

Write $`B=H_{a_1}H_{a_2}/H_{a_3}`$ and $`\delta=\max_j|a_j|`$. Projection to $`y`$ also has degree three and covers the antipodal involution. Fix $`0\lt r\lt1`$. If $`\delta\le r^3/40`$, the spherical belt $`r\lt|y|\lt1/r`$ has a single-valued holomorphic lift to the curve commuting with the antipodal maps.

To see this put $`\eta=r^3`$ and $`s=\eta/4`$. On $`|z|=s`$ the three factors give

~~~math
 |B(z)|\le
 \frac{(s+\delta)^2(1+\delta s)}
 {(s-\delta)(1-\delta s)^2}\lt 2s\lt\eta .
~~~

Here $`\delta\le s/10`$ and $`\delta s\lt1/100`$. For $`\eta\lt|w|\lt1/\eta`$, write $`B=N/D`$ with the factors above. Inside $`|z|=s`$ the denominator has just the simple zero $`a_3`$. Rouché's theorem gives $`N-wD`$ one zero there, counted with multiplicity. Antipodal equivariance applied to $`-1/\bar w`$ gives exactly one root outside $`|z|=1/s`$, counting infinity on the sphere. There is precisely one root in the middle annulus. It is simple, depends holomorphically on $`w`$, and is carried to the corresponding middle root by the antipodal map. Taking $`w=y^3`$ gives the asserted lift.

Its quotient is an embedded conformal Möbius band of half-width $`\log(1/r)`$. The band estimate gives every filling in this class the lower bound

~~~math
 A\ge 2\pi\,\frac{1-r^2}{1+r^2}.
~~~

For example $`r=1/16`$ and $`\delta\le10^{-6}`$ give $`2\pi\cdot255/257\gt6.23428`$. These branch points satisfy the small-cap condition for the first projection, whose unweighted certificate is at most $`14\pi/15`$. As the points coalesce, the second-projection bound tends to $`2\pi`$. Obtaining a comparable lift or line distribution for every genus-two conformal structure remains open. [Conformal band estimate](issue163_conformal_program.md) · [Rational checks](issue163_conformal_check.py)

## Examples and fillings in higher genus

For each filling genus $`g\ge2`$ choose $`g+1`$ distinct antipodal pairs $`\{\pm e^{i\theta_j}\}`$ on the equator. Choose exponents $`e_j\in\{1,2\}`$ with sum divisible by three, which is possible since their sums fill the integer interval from $`g+1`$ to $`2g+2`$. Put

~~~math
 P_j(z)=i e^{-i\theta_j}(z^2-e^{2i\theta_j}),\qquad
 y^3=\prod_j P_j(z)^{e_j},\qquad k=\frac23\sum_j e_j .
~~~

On the compact normalization there are $`2g+2`$ fully ramified points, no ramification at infinity, and the cover is connected since a local monodromy is a three-cycle. Its genus is $`2g`$. Each quadratic obeys $`P_j(-1/\bar z)=\overline{P_j(z)}/\bar z^2`$. The lift $`(z,y)\mapsto(-1/\bar z,\bar y/\bar z^k)`$ squares to one since $`k`$ is even and inverts the deck generator. The odd cyclic theorem applies.

These quotient conformal classes contain actual isometric fillings after cutting. To see this, take a simple one-sided characteristic curve on the quotient, whose complement is orientable, and use its geodesic representative for the uniformizing hyperbolic metric. It has an embedded Möbius collar. If the core has length $`L`$, multiply hyperbolic lengths by $`\pi/L`$ near it and by a smooth factor at least this large throughout the collar. Projection to the core in hyperbolic normal coordinates is length nonincreasing, so orientation-reversing loops contained there cost at least $`\pi`$ after scaling. Use a sufficiently large constant factor outside a smaller collar, including a buffer inside the larger collar. The scaled hyperbolic systole for a loop contained in the constant-factor region and the cost of crossing the buffer can both be made at least $`\pi`$. These three cases cover every orientation-reversing loop. The core attains $`\pi`$. Cutting it open gives one boundary of length $`2\pi`$. Any shortcut between a boundary pair extends along the boundary to an antipodal shortcut, which would close to an orientation-reversing loop of length less than $`\pi`$ on the quotient.
