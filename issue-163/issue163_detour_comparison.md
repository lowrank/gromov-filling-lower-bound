# Charging the excess length of antipodal routes

Let $`M`$ be a compact connected orientable Riemannian surface with one isometrically embedded boundary circle of length $`2\pi`$, in any genus. Write $`A`$ for its area. The unconditional bound here is

~~~math
 A\ge C=\frac{2213638768213206034608195815563}{3583999641600000000000000000000}\pi^2
 >6.095909909027119498 .
~~~

The increase over the previous planar result is $`0.0000032323456854\ldots`$. A more useful change is that the same inequality retains at least $`95\%`$ of the old diagonal weights for measuring the cost of detours through the filling. All matrix calculations use the twelve previously published witnesses. [Original planar comparison](issue163_planar_comass.md) · [Exact replay](issue163_planar_comass.cjs)

## A distance coordinate that measures detours

For an anchor $`a`$ and its antipode $`b`$ let $`r_a=d_M(\,\cdot\,,a)`$ and put

~~~math
 F_a=(r_b-r_a)/2,\qquad H_a=(r_a+r_b-\pi)/2,\qquad
 G_a=e^{-2H_a/\pi}F_a .
~~~

The shortest route from $`a`$ to $`b`$ through $`x`$ has length $`\pi+2H_a(x)`$. On the boundary $`H_a=0`$, so $`G_a`$ has exactly the triangular trace used in the calibration. It is antiperiodic in the label. It is 1-Lipschitz both in the point and in the angular label. Indeed, in either variable,

~~~math
 dG_a=\frac{e^{-2H_a/\pi}}2
 \big[(1-2F_a/\pi)\,dr_b-(1+2F_a/\pi)\,dr_a\big] .
~~~

The magnitudes of the two coefficients inside the brackets sum to two. This proves the stronger slope bound $`e^{-2H_a/\pi}`$ along every arclength-parametrized curve. The distance-ratio function $`\pi F_a/(\pi+2H_a)`$ also has a detour-dependent slope bound. The exponential gives a smaller bound at every positive detour. [Petitjean and Procházka, Theorem 1 and Lemma 5, for the distance-ratio function](https://arxiv.org/pdf/1810.12031)

At almost every interior point $`|\nabla r_a|=|\nabla r_b|=1`$. Hence $`\nabla F_a`$ and $`\nabla H_a`$ are orthogonal and their squared norms sum to one. In particular,

~~~math
 1-|\nabla G_a|^2
 =1-e^{-4H_a/\pi}
  +e^{-4H_a/\pi}(1-4F_a^2/\pi^2)|\nabla H_a|^2 .
~~~

Both terms are nonnegative. A constant excess on a region incurs the first cost even when its spatial derivative vanishes there.

## Keeping the gradient loss in the planar comparison

Take any separately 1-Lipschitz antiperiodic profile $`P_a(x)`$ with the same triangular boundary values. Fix any rotation of the 112-pair grid. On each cell let $`D_j(P)`$ be the earlier **normalized** bisected-gap diagonal. Its entries sum to at most one. Then

~~~math
 A\ge C+\frac{19}{20}
       \int_M\sum_j D_j(P)\big(1-|\nabla P_j|^2\big)\,dA .
~~~

In particular one may take $`P=G`$ and substitute the exact loss above. The weights are evaluated on the new profile. [Earlier diagonals and their positive lower bound](issue163_angular_energy.md)

To prove the inequality, use raw matrices until the last division by the old budget $`U=0.9999999`$. In one of the three corner chambers let $`d_j`$ be the raw bisected-gap diagonal and $`d_{\sigma j}`$ the four raw diagonals in the phase comparison. For $`p=3`$, $`k=110`$ and $`t=1/1000`$, the integer data give

~~~math
 d_{\sigma j}\ge (19/20)d_j+t\,\mathbf{1}_{\{p,k\}}(j)
~~~

for every index and all twelve comparisons. Write $`z_j`$ for the planar gradients, $`s_j=1-|z_j|^2`$ and $`q=(3+4i)\overline z_p z_k/5`$. For a unit complex number $`q_0`$ with $`q=|q|q_0`$, the four rectangle comparisons give at least one sign $`\sigma`$ for which

~~~math
 \sum_j d_{\sigma j}-t\Re(\sigma q_0)\le U-\delta .
~~~

Take any $`q_0`$ if $`q=0`$. The conclusion follows from the same unit-circle test as in the previous proof, now with a different $`\delta`$ for each chamber. Replacing $`q_0`$ by $`q`$ costs at most $`t(1-|q|)`$. For $`0\le u,v\le1`$ one has $`1-uv\le(1-u^2)+(1-v^2)`$, since $`u^2+v^2-uv`$ has maximum one on the square by separate convexity. Thus the two selected diagonal entries absorb the entire cost. The Hermitian certificate gives, for every vector in the product of disks,

~~~math
 Q_Y(z)\le U-\delta-(19/20)\sum_j d_js_j .
~~~

Conjugation proves the corresponding absolute bound, and signed reversal gives the reflected chambers. Outside the corner the old inequality retains the full diagonal loss.

| Chamber | Certified $`\delta`$ | Fraction of the projected triangle |
|---|---:|---:|
| Parent, including its reflection | $`0.000216362770`$ | $`1/2`$ |
| First child matrix and its reflection | $`0.000264087651`$ | $`1/4`$ |
| Second child matrix and its reflection | $`0.000249909075`$ | $`1/4`$ |

For the area fractions write $`x=e_0`$, $`y=e_{111}`$ in the signed gap frame and $`R=\pi/224`$. Its pair projection covers the triangle $`-R\lt x\le y\lt R`$ with signed degree one. The rectangle $`x\lt 0\lt y`$ uses the parent or its reflection. The triangles $`y\lt 0`$ and $`x\gt 0`$ carry the two children. The line $`x+y=-R`$ bisects the former into equal areas and $`x+y=R`$ does the same for the latter. These are exactly the switch lines of the child tents. Subregion by subregion, the signed integral of the extreme pair Jacobian is its projected area. Its absolute density is at most one. Preimages of subdivision edges may have positive area but their pair Jacobian vanishes almost everywhere, and all the chamber estimates still hold there by the tent tie rule. Summing over all 224 gaps gives $`\pi^2/112`$ times the fractions in the table. The old normalized action $`B`$ and the improved constant are

~~~math
 B=\frac{737877064811692678202731938521}{1194666547200000000000000000000}\pi^2,\qquad
 C=B+\frac{67623019}{31999996800000}\pi^2 .
~~~

This proves the inequality. One may equivalently add the corresponding $`\delta`$ times the extreme pair form over each of the projected subtriangles. The three coefficients vanish outside the old corner support. The neighboring planar test still puts global rescaling of this corrected form below $`6.09774`$. [Corner definitions and tie rules](issue163_midpoint.md) · [Boundary degree and neighboring witness](issue163_planar_comass.md)

## A test stated entirely in distances

For any fixed antiperiodic 1-Lipschitz reference profile $`k_a`$, form $`P_a`$ by projecting the number $`k_a`$ onto the interval

~~~math
 I_a(x)=[\,\pi/2-r_a(x),\,r_b(x)-\pi/2\,] .
~~~

The interval has center $`F_a`$ and half-width $`H_a`$. Its two endpoints coincide on the boundary. The median of the endpoints and $`k_a`$ is separately 1-Lipschitz and antiperiodic. When the interval contains $`k_a`$ in its interior the spatial gradient is zero. On the remaining open pieces the function is a signed distance plus a constant and its spatial gradient has norm one. At ties a Lipschitz function has zero differential almost everywhere on a set where it is constant.

Normalize $`D_j(P)dA`$ on point-index pairs to a probability measure with total weight $`T=\int_M\sum_j D_j(P)dA`$. The old diagonal comparison already gives $`B\le T(1-p)\le A(1-p)`$, where $`p`$ is the probability of strict containment of $`k_j`$ in the interval. Any filling of area below $`6.15`$ must therefore satisfy

~~~math
 p<1-B/6.15<0.00879853
~~~

for **every** reference profile and every grid rotation, each with its own evaluated weights. With $`k=0`$, a pair is counted precisely when both boundary points are farther than $`\pi/2`$ from $`x`$. A weighted fraction of $`0.88`$ percent would already give $`A\gt 6.15`$.

There is also a test directly on the sum $`r_a+r_b`$. Fix $`0\lt s\le1`$ and use
$`P_a=(1-\min(2H_a/\pi,s))F_a`$. Below the threshold its differentials have coefficients $`(1-2H_a/\pi\mp2F_a/\pi)/2`$ on the two distances, up to sign. The sum of the absolute coefficients is $`\max(1-2H_a/\pi,2|F_a|/\pi)\le1`$. Above the threshold the spatial gradient norm is at most $`1-s`$, including almost every point of the equality set. This again supplies an admissible profile with exactly the original trace. The weight fraction carried by $`r_a+r_b\ge(1+s)\pi`$ is less than $`0.00879853/(2s-s^2)`$ if $`A\lt 6.15`$. Examples rounded upward are $`9.025`$ percent for $`s=0.05`$ and $`4.631`$ percent for $`s=0.1`$. These tests constrain the global distribution. A universal lower bound on one of these fractions sufficient for $`6.15`$ remains open.

The threshold contraction is sharp within scalar laws $`P=\Psi(F,H)`$ that fix the trace and are 1-Lipschitz in each scalar variable on the whole strip. At $`H=s\pi/2`$, the two values at $`F=\pm\pi/2`$ can each have moved by at most $`s\pi/2`$. Their difference is at least $`(1-s)\pi`$. The Lipschitz constant of this slice in $`F`$ is therefore at least $`1-s`$, which the threshold law attains. This bounds the improvement available from a uniform contraction at a fixed route length.

## Metric compression on a whole region

The preceding constructions also give an estimate without choosing a grid. Write $`I`$ for the all-genus filling infimum and $`m(x)=\min_a H_a(x)`$. Every filling satisfies

~~~math
 A-I\ge\int_M(1-e^{-4m(x)/\pi})\,dA .
~~~

Indeed all $`G_a`$ stay 1-Lipschitz for the length metric $`e^{-4m/\pi}g`$ by the curve inequality above. Their boundary traces protect all boundary distances, and the boundary metric is unchanged because $`m=0`$ there. Smooth the positive continuous length multiplier from above, setting it equal to one on successively thinner boundary collars. Uniform approximation on the compact surface makes the smoothed areas tend to the stated integral of $`e^{-4m/\pi}`$. Thus in a sequence approaching the infimum, the area of the set where **every** antipodal route has a fixed positive excess goes to zero.

For a fixed reference $`k`$ the common open set on which $`k_a`$ is strictly inside $`I_a(x)`$ for all $`a`$ has area at most $`A-I`$. Compactness of the label circle gives a uniform strict margin locally. All the projected profiles are constant on this open set, so the metric can be shrunk on compact subsets of it with smooth positive multipliers arbitrarily close to zero there. Every boundary distance stays protected. Exhaustion gives the claimed area bound. Both comparisons allow arbitrary topology.

The same local tests can still be approached on arbitrarily small patches of actual fillings, with uniformly small detours. This explains why the fractions above have to be estimated over the surface. [Construction and the continuum comass test](issue163_short_routes.md)

## Replay

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_planar_comass.cjs issue163_inputs
~~~

It checks the twelve Hermitian inequalities, the retained diagonal entries, the three chamber gains, the exact area factor, the weight threshold and the fixed-form ceiling. The distance and metric comparisons are analytic. The repository's Lean project verifies the earlier Fourier result.
