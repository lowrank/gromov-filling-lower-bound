# What the sharp pair-weight estimate permits in planar comass

On one explicit family of angular profiles, the normalized Züst form has planar comass tending to $`(1+\pi^2/4)/\pi=1.1037080495\ldots`$. Thus its $`2\pi`$ boundary action can certify at most **5.692796486865** by global normalization. Even an arbitrary bounded signed symmetric reweighting by the angle between the two inferred round gradients has a ceiling of **5.843897829067**. Both results use continuum integrals. They apply to the pointwise comass method in every genus. [Sharp pair-weight inequality](issue163_zust_mass.md) · [Züst's original form](https://arxiv.org/pdf/2104.04498)

## Two angles determined by a pair

As in the preceding note let $`x_a=\sin F_a`$. Write $`\delta=b-a\in(0,\pi)`$ for the boundary-label separation. The scalar pair also determines the angle $`\gamma\in[0,\pi]`$ by

~~~math
 \cos\gamma=\frac{\cos\delta-x_ax_b}{\sqrt{1-x_a^2}\sqrt{1-x_b^2}},
 \qquad p_{ab}=\frac{\sin^2\gamma}{\sin^2\delta}.
~~~

On the round hemisphere $`\gamma`$ is the angle between the two distance gradients. For a bounded real multiplier $`w(\gamma)=w(\pi-\gamma)`$ consider the exact pair form whose value on disk-valued gradients $`z_a\in\mathbb R^2`$ is

~~~math
 \Omega_w(z)=\frac1\pi\int_0^\pi\int_a^\pi
 p_{ab}\,w(\gamma)\det(z_a,z_b)\,db\,da .
~~~

Its coefficients depend only on the two scalar coordinates and the fixed labels. Bounded measurable multipliers are interpreted by the oriented pair-area formula. At the central zero profile take $`z_a=(\cos(ka),\sin(ka))`$ for positive odd integers $`k`$. The resulting evaluation is

~~~math
 Q_k=\frac12\int_0^\pi w(\gamma)\sin(k\gamma)\,d\gamma .
~~~

The same $`Q_1`$ is the tangential density on the whole round hemisphere. Indeed there $`p_{ab}=g_a g_b`$, the round gradient at label $`a`$ has phase $`\nu(a)`$, and $`d\nu=g_a\,da`$ with $`\nu(a+\pi)=\nu(a)+\pi`$. Changing both variables gives the central-profile integral. Consequently the full boundary action is $`2\pi Q_1`$, or its limit from smaller round latitude circles. [Züst, Lemmas 3.1 and 3.9](https://arxiv.org/pdf/2104.04498)

## A family with two gradient directions

Start with the boundary triangle $`b(a)=\pi/2-a`$ on $`[0,\pi]`$. For $`\varepsilon\gt0`$ take $`F_a=\mathrm{sgn}(b(a))(|b(a)|-\varepsilon)_+`$ and extend by antipodality. Assign the first unit coordinate vector on the positive ramp, the second on the negative ramp, and zero on the central flat interval. The two ramps each have angular slope minus one. Pairs on a common ramp have $`p_{ab}=0`$. Pairs with a flat label have $`p_{ab}\le1`$. In fact $`p_{ab}\le (1-x_a^2)^{-1}`$ and the analogous second-label inequality follow by completing a square in the numerator. The flat-label contribution to the norm is $`O(\varepsilon)\|w\|_\infty`$. All cross-ramp determinants in the chosen test equal one. For nonnegative weights this realizes the entire cross-ramp upper bound. These are admissible planar comass tests. For a continuous multiplier, strict angular profiles can also be obtained by contracting $`F`$ by a factor tending to one at each fixed width.

Write a pair of cross-ramp labels as $`a,\pi-v`$ with $`0\lt a,v\lt\pi/2-\varepsilon`$. Use $`k=\tan\varepsilon`$, $`B=1+k^2`$, and set

~~~math
 U=\frac{\tan a}{k+\tan a},\qquad V=\frac{\tan v}{k+\tan v},
 \qquad S=BUV,\qquad D=U+V-2UV.
~~~

The new square is $`[0,1/B]^2`$. From the cosine formula above, $`1+\cos\gamma=2\sin a\sin v/(\sin(a+\varepsilon)\sin(v+\varepsilon))=2S`$. Also $`\cot(a+v)=(1-S-D)/(kD)`$. A direct substitution in $`p_{ab}\,da\,dv`$ gives

~~~math
 \frac{4S(1-S)}{D^2}\,dU\,dV .
~~~

With $`T=\tfrac12\log(U/V)`$, the resulting density in $`dS\,dT`$ is
$`(1-S)/(\cosh T-\sqrt{S/B})^2`$ on $`0\lt S\lt1/B`$, $`|T|\le-\tfrac12\log(BS)`$. As $`B\downarrow1`$ these positive densities increase to the limiting density. Its $`T`$ integral is

~~~math
 G(S)=(1-S)\int_{\log\sqrt S}^{-\log\sqrt S}
       \frac{dT}{(\cosh T-\sqrt S)^2}
     =2+2\sqrt{\frac{S}{1-S}}\arccos\sqrt S .
~~~

For the evaluation put $`r=\sqrt S`$, $`b=\sqrt{(1-r)/(1+r)}`$, and $`z=\tanh(T/2)/b`$. The integral becomes $`(4/b)\int_0^b(1-b^2z^2)(1+z^2)^{-2}\,dz`$. Integrating the derivative of $`z/(1+z^2)`$ and the arctangent gives the formula. In particular $`G\le4`$. Dominated convergence now works for bounded signed multipliers as well.

By symmetry of $`w`$ we may set $`S=\sin^2(\gamma/2)`$ in the limiting integral. Averaging $`G(S)`$ with $`G(1-S)`$ and using $`dS=\tfrac12\sin\gamma\,d\gamma`$ gives the limiting planar evaluation

~~~math
 L(w)=\frac1{2\pi}\int_0^\pi w(\gamma)K(\gamma)\,d\gamma,
 \qquad K(\gamma)=2\sin\gamma+\frac\pi2+(\gamma-\pi/2)\cos\gamma .
~~~

In particular $`L(1)=(1+\pi^2/4)/\pi`$. The total profile weight from the previous note tends to $`2(1+\pi^2/4)/\pi^2\lt1`$, yet the surviving weight connects just the two perpendicular gradient groups.

## A ceiling for every symmetric angle multiplier

Direct sine integration gives the absolutely convergent expansion

~~~math
 K(\gamma)=\frac72\sin\gamma-
 \sum_{k=3,5,\ldots}\frac{2}{k(k^2-1)}\sin(k\gamma).
~~~

For odd $`k\ge3`$, integrate the term with $`(\gamma-\pi/2)\cos\gamma`$ at the two frequencies $`k\pm1`$. Together with the constant term this gives $`2/k-1/(k-1)-1/(k+1)`$. The coefficient at one is $`7/2`$, and symmetry kills the even coefficients. The series has the same Fourier coefficients as the continuous function and converges uniformly. Partial fractions and the alternating harmonic series give $`\sum_{k=3,5,\ldots}2/[k(k^2-1)]=3/2-2\log2`$.

If $`C`$ bounds the global planar comass, the above tests give $`|Q_k|\le C`$ and $`|L(w)|\le C`$. The identity for $`L(w)`$ therefore implies

~~~math
 \frac72|Q_1|\le(\pi+3/2-2\log2)C,\qquad
 \frac{2\pi |Q_1|}{C}\le
 \frac{4\pi}{7}(\pi+3/2-2\log2)<5.843897829067 .
~~~

This restriction persists even when the multiplier changes sign. To distinguish the problematic pairs from those at the center, a correction can also use their separation on the external boundary or information from another label.

The same calculation measures how much a further correction must contribute. For a field $`\Phi`$, write $`A(\Phi)`$ for its boundary action, $`E(\Phi)`$ for the limit of its evaluation in the two-direction test when it exists, and $`q_k(\Phi)`$ for its central odd-frequency tests. Define

~~~math
 T(\Phi)=A(\Phi)-\frac{4\pi}{7}\left[
 \pi E(\Phi)+\sum_{k=3,5,\ldots}\frac{2q_k(\Phi)}{k(k^2-1)}
 \right].
~~~

The sine-series identity gives $`T(\Omega_w)=0`$. If $`\Omega_w+\Phi`$ has comass at most one and action at least 6.15, the bracket tested on the combined field is at most $`\pi+3/2-2\log2`$. Consequently **$`T(\Phi)\gt0.306102170932`$**. This is a necessary quantitative test for information added to a visual-angle kernel. It uses one limiting profile and the Fourier responses at the center.

## A change using both angles

For a concrete test put $`\eta=\arctan(1/5)`$, $`d=\min(\delta,\pi-\delta)`$, and replace $`p_{ab}`$ by

~~~math
 p_{ab}\big(1-\tfrac17\mathbf 1_{\{d<\eta\}}\sin^2\gamma\big).
~~~

This remains a closed pair form. Its boundary action is at least $`2\pi-4\eta/7\gt6.1703`$. The original unnormalized pair integral on its boundary polygon is four for every separation. The two end bands have together $`\pi\eta`$ of pair-parameter area, and the removed fraction is at most $`1/7`$. The action is also at most $`2\pi`$.

For completeness, on the boundary pair polygon write the two scalar coordinates as $`X,Y`$. The substitutions $`u=\tan(\delta/2)\tan((X+Y)/2)`$, $`v=\tan((X-Y)/2)/\tan(\delta/2)`$ carry this polygon to $`[-1,1]^2`$. The factorization of the numerator in the weight theorem gives $`p\,dX\,dY=2(1-u^2)(1-v^2)(1-u^2v^2)^{-2}\,du\,dv`$. Expanding the positive denominator series and integrating gives $`4\sum_{j\ge0}[(2j+1)^{-2}-(2j+3)^{-2}]=4`$. The triangular boundary trace winds once around the polygon. [Pair polygon and degree](issue163_free_field.md#the-changed-form-and-its-boundary-action)

Every round profile passes the unit-comass test for this modified form. Its nonnegative kernel is dominated there by $`g_a g_b`$. For any probability distribution of planar unit vectors, two independent samples satisfy $`\mathbb E|\det(Z,Z')|\le2/\pi`$. This follows from the absolutely convergent Fourier series $`|\sin t|=2/\pi-(4/\pi)\sum_{m\ge1}\cos(2mt)/(4m^2-1)`$, since the expected cosines are squared moduli. Shorter vectors can only reduce this absolute bound. Apply it to the probability measure $`g_a\,da/\pi`$ on a half-circle. The unordered pair integral of the absolute determinant, with the form's normalization, is at most one.

In the cross-ramp limit $`d\to0`$ at almost every fixed $`(S,T)`$. The limiting comass is $`L(1)-L(\sin^2)/7\lt0.998`$, where $`L(\sin^2)=(20/9+\pi^2/4)/(2\pi)`$ follows by integrating $`K\sin^2`$. This correction therefore passes both the round and limiting two-direction tests with enough action to contemplate 6.15.

At the finite width $`\varepsilon=\arctan(1/25)`$, the same two directions give evaluation **above 1.02531**. Even granting the full action $`2\pi`$ puts this candidate below **6.128069135391**. This test uses 32 subdivisions in each coordinate and no optimization. On each rectangle in the $`U,V`$ square, select $`f=4S(1-S)`$ if the separation cutoff is absent throughout the rectangle. Otherwise use $`f=4S(1-S)[1-4S(1-S)/7]`$ as a lower weight. The test for absence is $`\min D\ge5\max |1-S-D|`$. Both bilinear extrema are determined at the corners. Jensen's inequality gives

~~~math
 \int_{\rm rectangle} f D^{-2}\,dU\,dV
 \ \ge\ \frac{(\int f)^3}{(\int fD)^2}.
~~~

The two moments on the right are exact rational integrals of polynomials. The checker rounds each lower bound down before summing. The two-angle change removes the limiting obstruction at the equatorial scale while leaving an obstruction at a definite positive profile depth.

~~~sh
python3 issue163_zust_check.py
~~~

The replay also brackets the logarithm and trigonometric constants in the comparisons and checks the Fourier-mode example from the pair-weight theorem. The bounds on these continuum calibration families are independent of the finite all-genus area certificate.
