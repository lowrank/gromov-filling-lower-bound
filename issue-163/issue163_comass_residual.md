# Comparing the errors in the planar comass bounds

Every compact connected orientable Riemannian surface with one isometrically embedded boundary circle of length $`2\pi`$ satisfies

~~~math
 A=\mathrm{Area}(M)\ \ge\ C_*=
 \frac{2213639035555078034608195815563}{3583999641600000000000000000000}\pi^2
 >6.095910645232136335 .
~~~

The gain over the previous bound is $`7.362050168\ldots\,10^{-7}`$. It comes from using the **same vector of gradients** in the four comass comparisons. A separate estimate on the directions themselves gives a test at the larger scale of $`6.15`$. A filling below that value must have weighted root mean square directional imbalance less than $`0.132362`$. A small quadrature on the round hemisphere gives about $`0.156`$. [Previous bound and distance coordinates](issue163_detour_comparison.md) · [Integer replay](issue163_comass_residual.cjs)

## The error in two comparisons cannot vanish simultaneously

Work in one of the three bisected-gap chambers and its signed frame. Write $`z_j=dP_j(X)+i\,dP_j(Y)`$ for the gradients of the distance coordinates in an oriented orthonormal frame. The argument applies to any separately 1-Lipschitz antiperiodic profile with the triangular boundary trace. Let $`K=-iY_0/2`$, where $`Y_0`$ is the raw skew matrix of the chamber, so its evaluation is $`Q=z^*Kz`$. The old unnormalized diagonal $`D_0`$ satisfies $`D_0\pm K\succeq0`$ and has trace at most $`U=0.9999999`$.

Use $`p=3`$, $`k=110`$, $`t=1/1000`$, and $`q=(3+4i)\overline z_p z_k/5`$. For $`\sigma\in\{1,i,-1,-i\}`$ write $`H_\sigma`$ for the Hermitian matrix giving $`z^*H_\sigma z=t\Re(\sigma q)`$. It is supported on the two pivot indices. The twelve existing witnesses, four per chamber, prove

~~~math
 R_\sigma=D_\sigma-K-H_\sigma\succeq0,\qquad
 R_\sigma\preceq L_\sigma=D_\sigma+D_0+
        (t/2)(E_{pp}+E_{kk}).
~~~

The upper bound follows from $`-K\preceq D_0`$ and the two eigenvalues $`\pm t/2`$ of the pivot block. As $`0\preceq R_\sigma\preceq L_\sigma`$, conjugation by $`L_\sigma^{-1/2}`$ gives $`R_\sigma L_\sigma^{-1}R_\sigma\preceq R_\sigma`$. Thus the residual energy controls each squared coordinate of $`R_\sigma z`$, summed with weight $`1/(L_\sigma)_{jj}`$. [Original matrices and positive-definiteness checks](issue163_planar_comass.md)

Take the two signs $`\sigma=-1`$, $`\nu=-i`$, with weights $`\alpha`$ and $`\beta=1-\alpha`$. Away from the pivots their residual coordinates are $`d_{\sigma j}z_j-(Kz)_j`$ and $`d_{\nu j}z_j-(Kz)_j`$. The same unknown $`(Kz)_j`$ occurs twice. Minimizing the two weighted squared errors over this one complex number gives

~~~math
 \alpha z^*R_\sigma z+\beta z^*R_\nu z \ge
 \sum_{j\ne p,k} v_j |z_j|^2,\qquad
 v_j=\frac{\alpha\beta(d_{\sigma j}-d_{\nu j})^2}
 {\beta d_{\sigma j}+\alpha d_{\nu j}+d_{0j}} .
~~~

Set $`v_p=v_k=0`$. The averaged phase comparison therefore has effective diagonal entries $`e_j=\alpha d_{\sigma j}+\beta d_{\nu j}-v_j`$. It gives an extra half-plane for $`q`$ whenever $`Q`$ is large and the gradients are unit vectors. The choices $`\alpha=1/2`$ and $`3/4`$ cut off the corner of the previous rectangle that first reached the unit circle. All six vertices of each new polygon have squared norm strictly less than one. The checker enumerates the intersections of the six rational lines and checks this inequality at every feasible vertex. Rounding each variance weight downward keeps the test rigorous.

| Chamber | Old raw comass gain | New certified gain $`\delta`$ | Fraction of compulsory projected area |
|---|---:|---:|---:|
| Parent | 0.000216362770 | 0.000224200 | 1/2 |
| First child | 0.000264087651 | 0.000272380 | 1/4 |
| Second child | 0.000249909075 | 0.000259360 | 1/4 |

The six comparisons also work on the full product of disks. The effective diagonal in each retains $`(19/20)d_{0j}`$ plus a reserve $`t`$ on both pivots. For $`q=|q|q_0`$ with $`|q_0|=1`$, one of the six half-planes gives its strict gain at $`q_0`$. Substitution of $`q`$ costs at most $`t(1-|q|)\le t(1-|z_p|^2)+t(1-|z_k|^2)`$, including $`q=0`$ by choosing any $`q_0`$. Thus $`Q\le U-\delta-(19/20)\sum_jd_{0j}(1-|z_j|^2)`$. Conjugation handles the opposite sign of the skew evaluation, and the signed reversal handles the reflected chambers.

The normalized bisected-gap form has action $`B=6.095889052386098292\ldots`$. Each gap has a triangular projection of signed degree one in its two extreme coordinates. The area fractions in the table follow by bisecting that triangle. Summed over the 224 gaps, its projected area is $`\pi^2/112`$. Integrating the chamber gains with these fractions and dividing by $`U`$ gives the displayed $`C_*`$. With $`D_j=d_{0j}/U`$ the proof also gives

~~~math
 A\ge C_*+\frac{19}{20}\int_M\sum_jD_j(1-|\nabla P_j|^2)\,dA .
~~~

This retains the earlier estimates that charge a genuine detour between boundary antipodes. [Projected areas and detour estimates](issue163_detour_comparison.md#keeping-the-gradient-loss-in-the-planar-comparison)

## A constraint on how gradients are distributed over the filling

Use the normalized bisected-gap form of action $`B`$, with its diagonal $`D`$ in each cell. In an orthonormal frame put

~~~math
 T=\sum_jD_j\,\nabla P_j\otimes\nabla P_j,\qquad
 \tau=\mathrm{tr}(T),\qquad
 r=\frac{\lambda_{\max}(T)-\lambda_{\min}(T)}{\tau}
   =\frac{|\sum_j D_j z_j^2|}{\tau}.
~~~

Set $`r=0`$ when $`\tau=0`$. The statistic $`r`$ is zero for an isotropic weighted distribution of directions and equals one for parallel gradients of positive total weight. It detects a loss even when every gradient has unit length.

In any tangent frame the Hermitian diagonal bound applies homogeneously, with arbitrary complex inputs. Changing the frame by a real determinant-one matrix preserves the two-form evaluation. Taking the infimum of the transformed trace gives $`2\sqrt{\det T}`$, by diagonalizing $`T`$ and rescaling the two axes reciprocally. For a singular $`T`$ pass to the limit. The action consequently satisfies

~~~math
 B\le\int_M2\sqrt{\det T}\,dA
   =\int_M\tau\sqrt{1-r^2}\,dA .
~~~

Write $`m=\int_M\tau\,dA`$ and $`d\mu=\tau\,dA/m`$. Since $`m\le A`$, Cauchy–Schwarz gives the all-genus estimate

~~~math
 B^2\le m^2\Bigl(1-\int_M r^2\,d\mu\Bigr).
~~~

For $`A\lt6.15`$ this forces the root mean square of $`r`$ below $`\sqrt{1-(B/6.15)^2}\lt0.132362`$ for every grid rotation and every admissible profile with the prescribed trace. If $`r\ge0.30`$ on a fifth of the trace weight, then $`A\ge B/\sqrt{0.982}\gt6.151503`$. The denominator in the measure is the trace weight, so the test also applies when some gradients are short.

The directional loss can also be kept alongside the new constant. Let $`s_0=\sum_jD_j(1-|z_j|^2)`$, and set $`\delta=0`$ off the three chambers and their reflections. Taking the better of the two pointwise comparisons gives

~~~math
 A\ge C_*+\frac{19}{20}\int_M s_0\,dA
 +\int_M\bigl[\tau(1-\sqrt{1-r^2})-\delta/U\bigr]_+\,dA .
~~~

Indeed the trace comparison retains all of $`s_0`$ and the directional loss, while the chamber comparison retains $`19s_0/20`$ and $`\delta/U`$. The mandatory projected areas pay for $`C_*-B`$.

A single local test distinguishes this condition from a pointwise exclusion. In the previously constructed neighboring chamber, unit directions give raw value at least $`0.999701090`$. The tensor inequality forces $`r\le\sqrt{1-(0.999701090/U)^2}\lt0.025`$ there for *any* feasible diagonal of trace at most $`U`$. Such directions can occur on a small patch of an actual filling. A proof at $`6.15`$ along this route must control their occupation across the filling. [Neighboring planar test and its geometric realization](issue163_short_routes.md)

### Directional imbalance at a genuine boundary

There is positive trace weight with $`r`$ arbitrarily close to one in every filling. Take a closed boundary subarc $`J`$ of length $`\ell`$ avoiding the signed anchors. Each boundary coordinate has constant signed slope $`\epsilon_j\in\{-1,1\}`$ on $`J`$. In boundary normal coordinates write the metric as $`dv^2+G(s,v)^2ds^2`$, let $`T_v`$ be the unit tangent to the parallel arc, and let $`L(v)=\int_JG(s,v)\,ds`$. The endpoints of each parallel arc lie within $`v`$ of the original endpoints. For almost every sufficiently small $`v`$,

~~~math
 \int_J(1-\epsilon_j\langle\nabla P_j,T_v\rangle)G(s,v)\,ds
 \le L(v)-\ell+2v .
~~~

Indeed the integral of the signed derivative along the parallel arc is its signed endpoint increment, at least $`\ell-2v`$. If $`N_v`$ is the unit normal, then $`|\langle\nabla P_j,N_v\rangle|^2`$ and $`1-|\nabla P_j|^2`$ are each at most $`2(1-\epsilon_j\langle\nabla P_j,T_v\rangle)`$. Also $`\tau(1-r)=2\lambda_{\min}(T)\le 2T(N_v,N_v)`$. Consequently on that parallel arc the integral of $`\tau(1-r)`$ is at most $`4n(L(v)-\ell+2v)`$. Its total trace weight is at least $`L(v)/16-2n(L(v)-\ell+2v)`$ by the published diagonal floor $`D_j\ge1/(16n)`$. As $`v`$ decreases to zero, $`L(v)`$ tends to $`\ell`$. The trace-weighted mean of $`r`$ along the arcs tends to one through regular heights. In particular the last positive-part integral is strictly positive on each smooth filling. To see this, restrict to $`r\gt 0.9`$ and $`\tau\gt 1/32`$ on those arcs. The two preceding integral bounds give this set positive length at all sufficiently small regular heights, and its directional loss exceeds the largest $`\delta/U`$. The available collar width can depend on the metric. A quantitative lower bound on the trace weight of the region with appreciable imbalance would strengthen the area bound. [Diagonal floor](issue163_angular_energy.md#keeping-the-energy-of-the-angular-difference)

## A small check on the round hemisphere

On the unit hemisphere let $`s`$ be longitude and $`z`$ the height above the equator. Its area element is $`ds\,dz`$. For an equatorial anchor at longitude $`a`$, let $`\theta=a-s`$. The profile is $`P_a=\arcsin(\sqrt{1-z^2}\cos\theta)`$. Up to the fixed choice of signs of the orthonormal axes, its unit gradient has components proportional to $`(\sin\theta,-z\cos\theta)`$. Thus both entries needed for its doubled-angle moment are explicit.

The following midpoint quadratures use $`z=t^2`$ to resolve the boundary layer. Rotations and reflections reduce the angular variable to half of one grid gap. The intervals allow all three diagonal proposals in an inherited terminal cell whenever the old checker could have selected among them. They are rounded outward and describe the sampled sums. The calculation supplies no quadrature error estimate between sample points.

| Radial nodes | Angular nodes | Sampled root mean square $`r`$ |
|---:|---:|---:|
| 12 | 4 | 0.15799–0.15950 |
| 24 | 6 | 0.15590–0.15696 |
| 48 | 8 | 0.15588–0.15696 |
| 96 | 8 | 0.15581–0.15687 |

The hemisphere clears the $`0.132362`$ threshold in each of these tests. Establishing a sufficient integrated imbalance or trace loss on every putative smaller filling remains open. [Quadrature and diagonal reconstruction](issue163_hemisphere_moments.cjs) · [Exact limits on changes confined to anchor gaps](issue163_flat_collar.md)

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_planar_comass.cjs issue163_inputs
node issue163_comass_residual.cjs
node issue163_hemisphere_moments.cjs issue163_inputs
~~~

The first command verifies the original twelve Hermitian inequalities, the second checks the new scalar inequalities and area constant with integers, and the third runs the numerical hemisphere test. The Lean development covers the earlier Fourier theorem. [Lean theorem ledger](../docs/current-manuscript.md)
