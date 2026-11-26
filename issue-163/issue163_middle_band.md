# A necessary middle-depth gain for a calibration reaching 6.15

Put $`h=\pi/112`$. Consider closed calibrations on angular distance profiles, with planar comass at most one. Keep the normalized free field on the band of profiles of depth $`h\le\rho\le10h`$, and allow arbitrary changes on **both** sides. The boundary action is then at most **6.148325785606**. Keeping the field on the band through $`12h`$ lowers the ceiling to **6.141013708383**. These bounds concern a method for proving lower bounds on filling area. The sharp all-genus filling area remains open. [Free field](issue163_free_field.md) · [All-genus lower bound](issue163_anchor.md) · [Exact comparison](issue163_middle_band.cjs)

The comparison gives a direct test for any new calibration. A boundary action of at least $`6.15`$ requires the change in its integral on one explicit cylinder of profiles to be at least **0.008986291617** for the band through $`12h`$. Stokes reduces that integral to the difference of two loop integrals of a primitive. This test applies to coefficients depending on arbitrarily many labels. A proof using global constraints on the occupation of profiles by actual fillings could use information outside its hypotheses.

## Distance from the boundary profiles

Use all angular profiles $`P:S^1\to\mathbb R`$ which are 1-Lipschitz and satisfy $`P_{a+\pi}=-P_a`$. The triangular profile at boundary arclength $`s`$ is $`b_s(a)=\pi/2-d_{S^1}(a,s)`$. Angular Lipschitz continuity bounds $`b_s(a)-P_a\le\pi/2-P_s`$. Passing to the antipodal label bounds the opposite difference, and taking $`a=s`$ gives equality. Consequently

~~~math
 \rho(P)=\min_s\|P-b_s\|_\infty=\pi/2-\max_s P_s .
~~~

On a filling, spatial Lipschitz continuity bounds this profile depth above by intrinsic distance to the boundary. On the unit hemisphere they agree. Write $`\omega_0`$ for the normalized free field with action $`A_0=6.095000609501857507\ldots`$. The one-anchor and bisected-gap additions both vanish at depths greater than or equal to $`h`$, interpreted by pullback on the threshold. [One-anchor support](issue163_anchor.md) · [Profile comparison setting](issue163_flat_collar.md#which-corrections-does-the-test-cover)

The comparison applies to forms admitting Stokes on the following profile maps. Planar comass at most one means their evaluation on an oriented orthonormal frame has absolute value at most one whenever the coordinates are spatially 1-Lipschitz and obey the angular constraints. A candidate using this comass on genuine fillings via the distance map must accordingly pass the test if it claims the same pointwise estimate throughout profile space.

## Outer collar, middle cylinder and round cap

For $`0\le r\le h`$ let $`\lambda=2/3`$ and set

~~~math
 \phi_r(x)=\mathrm{sgn}(x)\min\{(|x|-\lambda r)_+,\ \pi/2-r\},
 \qquad P_a(s,r)=\phi_r(b_s(a)).
~~~

Use metric $`D^2 ds^2+dr^2`$ on this collar with $`D=3/\sqrt5`$. On a sloping piece the squared norm of a coordinate differential is $`D^{-2}+\lambda^2=1`$. On a plateau its radial derivative has magnitude at most one and its angular derivative vanishes. The scalar map preserves antipodality and the angular Lipschitz bound. Each level reaches its maximum $`\pi/2-r`$ at label $`a=s`$. The collar has area $`2\pi hD`$. Write $`O_s(a)=\phi_h(b_s(a))`$ for its inner loop.

At latitude $`t\ge h`$ the round hemisphere has profile loop

~~~math
 R_s^t(a)=\arcsin(\cos t\cos(s-a)).
~~~

Each round coordinate is $`\pi/2`$ minus spherical distance to its equatorial anchor, hence spatially 1-Lipschitz. The cap above this loop has area $`2\pi(1-\sin t)`$. Join the loops by

~~~math
 C_t(s,u)=(1-u)O_s+uR_s^t,\qquad 0\le u\le1 .
~~~

Both profiles achieve their maximum at the same label $`a=s`$. Their interpolant has depth exactly $`(1-u)h+ut`$. It remains angularly 1-Lipschitz and antipodal. The cylinder can be given a scaled flat metric to make all coordinates spatially 1-Lipschitz. Its metric area does not enter the bound.

Let $`J(O)`$ and $`J(R^t)`$ be the integrals of $`\omega_0`$ on disks spanning the indicated loops, oriented with $`s`$ increasing on their boundary. They are independent of the spanning disk by the pairwise primitives for the free field. The middle cylinder contributes $`J(O)-J(R^t)`$ for that field. Adding it to the outer collar and the round cap gives a test disk with the prescribed outer boundary. For any calibration $`\omega`$ of comass at most one on these profile maps, its boundary action therefore satisfies

~~~math
 A(\omega)\le
 \underbrace{2\pi hD+J(O)}_{\text{outer collar and inner loop}}
 +\underbrace{2\pi(1-\sin t)-J(R^t)}_{\text{round cap slack}}
 +\int_{C_t}(\omega-\omega_0).
~~~

In particular, agreement on the middle cylinder suffices for the last term to vanish. The first bracket is at most **6.126074095352**. If changes are allowed only at depths greater than $`t`$, using the genuine hemisphere for the whole disk instead gives $`A_0`$ plus the second bracket. The table rounds every ceiling upward.

| Depth $`t`$ | Round cap slack | Ceiling for changes only deeper than $`t`$ | Ceiling for changes both shallower than $`h`$ and deeper than $`t`$ |
|---|---:|---:|---:|
| $`6h\approx0.16830`$ | 0.048035003023 | 6.143035612525 | 6.174109098375 |
| $`10h\approx0.28050`$ | 0.022251690254 | 6.117252299756 | 6.148325785606 |
| $`12h\approx0.33660`$ | 0.014939613031 | 6.109940222533 | 6.141013708383 |

For an explicit proposed change $`\omega-\omega_0=d\beta`$, the required cylinder gain at $`12h`$ is $`\int_{O}\beta-\int_{R^{12h}}\beta\ge0.008986291617`$. At $`10h`$ it is at least $`0.001674214394`$. This supplies two inexpensive necessary checks before solving any local matrix problems. Agreement of the fields everywhere in the band is a sufficient condition for failure. The two loop integrals can also agree for a correction whose support meets the band.

## An inexpensive test of a proposed interior correction

Take the single separation of a quarter turn and the primitive
$`\beta=c\sum_a(P_a-\pi/2+mh)_+\,dP_{a+56}`$ for an integer $`2\le m\le10`$. Choose $`c`$ so that its boundary integral is $`\delta=6.15-A_0`$. This specifies its intended action exactly. On the round loop at $`12h`$ the primitive vanishes. On the outer inner loop the shifted quarter-turn coordinate is flat for $`|s-ah|\le2h/3`$. Farther along either side, it has derivative one wherever the tent is positive. There the tent height is $`(m-2/3)h-|s-ah|`$. Integrating gives the following middle-cylinder response.

~~~math
 \int_{C_{12h}}d\beta
 =224c(m-4/3)^2h^2
 =\delta\left(1-\frac{4}{3m}\right)^2 .
~~~

Width $`2h`$ gives about 0.00611 and fails the required 0.00898629. Widths $`3h`$ and $`6h`$ give about 0.01698 and 0.03327 and pass that test. A separate planar test rules out every one of these nonnegative corrections, even when all widths and offsets through $`12h`$ are combined and the free field is rescaled. Its ceiling is 6.095953461637. Thus a wider layer can supply the required integrated response while overspending the pointwise comass. [Two explicit planar tests](issue163_anchor_cone.md)

## Verifying the fluxes

For a pair of labels separated by $`kh`$, the two triangular boundary coordinates enclose the degree-one polygon $`|x-y|\le k`$, $`|x+y|\le112-k`$ in units of $`h`$. Applying $`\phi_h`$ to both coordinates maps this polygon onto the pair projection of an inner spanning disk with its multiplicity. The nonconstant preimage of an interior output bin is a unit interval translated by $`2/3`$ away from zero. The two extreme output bins have zero area. For each pair of interior bins, intersect the two preimage intervals with the polygon and multiply their area by the free coefficient in the output bins. The four excluded corners have disjoint interiors on the input square. In third-bin units all doubled intersection areas are integers. This gives $`J(O)`$ exactly as a rational multiple of $`\pi^2`$. [Pair polygon and coefficients](issue163_free_field.md#the-changed-form-and-its-boundary-action)

For the round loop, sample the scalar function $`g(s)=\arcsin(\cos t\cos s)`$ on $`q=4`$ equal subintervals per angular grid spacing and interpolate linearly. The 448 subintervals of a half-circle are shared by all pairs. The checker encloses each proposed vertex by integer cosine comparisons, to within $`2h/T`$ with $`T=10^5`$. Reflection and antipodality are exact. All interpolated slopes are checked to have magnitude at most one. Since

~~~math
 g''(s)=\frac{-\cos t\,\sin^2t\,\cos s}{(1-\cos^2t\,\cos^2s)^{3/2}},
 \qquad |g''(s)|\le\cot t ,
~~~

the interpolant has uniform error $`e\le\cot(t)(h/q)^2/8+2h/T`$. Along the straight homotopy to the true loop the two tangent vectors have coordinate magnitudes at most $`1`$ and $`e`$. Giving this homotopy metric $`2(ds^2+e^2du^2)`$ makes every coordinate 1-Lipschitz. The free comass estimate bounds the flux error by $`4\pi e`$. The checker uses $`\cot t\le1/t`$.

For each projected polygonal loop, integrate its winding against the old pair coefficient. At fixed first coordinate $`x`$, the second coordinate has an upper and a lower branch by evenness and monotonicity of the scalar interpolant. Use the primitive $`A(x,y)=\int_{-\pi/2}^y W_{ij}(x,z)\,dz/U`$, with $`W_{ij}`$ including the scalar weights. The integral is the integral in $`x`$ of the upper primitive minus the lower one. Split each edge at the scalar bin walls. The primitive on each resulting segment is affine in $`y`$, so the trapezoidal rule there is exact. The verifier rounds each signed rational contribution downward, includes the homotopy error, and rounds the area of the round cap upward. At latitude zero it independently recovers the archived free action to within $`5.4\times10^{-10}`$.

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_middle_band.cjs issue163_inputs
~~~

The replay uses the pinned field, rational polygon intersections, a directed enclosure of $`\pi`$, and directed cosine bounds. It uses no numerical optimization.
