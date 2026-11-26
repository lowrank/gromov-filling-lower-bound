# How much area must the high anchors occupy?

For every compact connected orientable Riemannian surface with one isometrically embedded boundary circle of length $`2\pi`$, in every genus,

~~~math
 \mathrm{Area}(M)\ge
 \frac{4900807299305452903120181318626856678763424416160470713006969}
      {7934171039896083567183835951925211702220800000000000000000000}\pi^2
 >6.096292737690900167 .
~~~

With $`n`$ antipodal anchor pairs at spacing $`h=\pi/n`$, write $`K=\pi^2/n`$. On each fixed grid with $`n\ge3`$, the region where at least one anchor is high has area at least $`2K/\sqrt3`$. The signed neighboring-pair projection alone requires area $`K`$. At $`n=112`$, averaging the grid rotation makes the required area **more than $`1.491567K`$**. Applying the unused trace in the preceding 58 matrices gives the displayed bound. The numerical gain is $`0.000005958109530370\ldots`$. [One-anchor calibration](issue163_anchor.md) · [Integer replay](issue163_anchor.cjs)

## A far coordinate must serve both adjacent levels

Use the antiperiodic 1-Lipschitz distance coordinates $`P_a`$ with triangular boundary trace. A grid label is high when $`P_a\gt\pi/2-h`$. At most two labels are high and when there are two they are adjacent, since $`P_a+P_b\le\pi-d_{S^1}(ah,bh)`$. Denote the areas with exactly one and exactly two high anchors by $`S_1,S_2`$. Express all gradients $`g_a=\nabla P_a`$ in an oriented orthonormal tangent frame. Define

~~~math
 R=\sum_{a\ \mathrm{high}}\frac1{n-1}
       \sum_{j=1}^{n-1}\det(g_a,g_{a+j}).
~~~

Every summand at a fixed high anchor and fixed separation has signed integral $`h^2`$, by Stokes applied to $`(P_a-\pi/2+h)_+\,dP_{a+j}`$. Hence $`\int R=2K`$. On a two-anchor region let $`u=g_a,v=g_{a+1}`$ in increasing cyclic order, and $`J=\det(u,v)`$. The signed integral of $`J`$ over all such regions is $`K`$. Indeed the adjacent-coordinate boundary polygon has degree one, and the projected triangle with both values high has area $`h^2/2`$ per gap in the signed frame. [Degree and triangular regions](issue163_planar_comass.md#how-the-shortest-distances-make-the-comass-gain-contribute-area)

On a single-anchor region $`R\le1`$. With two high anchors, the two sums share $`n-2`$ gradients. The remaining terms are $`\det(u,v)`$ and $`\det(v,-u)`$. Thus with $`c=(n-2)/(n-1)`$,

~~~math
 R\le c|u+v|+\frac2{n-1}J,\qquad
 |u+v|+J\le\frac{3\sqrt3}{2}.
~~~

For the second inequality maximize the convex function of each vector separately on the unit disk. At two unit vectors with smaller angle $`\theta\in[0,\pi]`$, the expression is at most $`2\cos(\theta/2)+\sin\theta`$, with maximum at $`\theta=\pi/3`$. Integrating gives

~~~math
 S_2+\frac{2S_1}{3\sqrt3\,c}\ge\frac{2K}{\sqrt3}.
~~~

The coefficient of $`S_1`$ is at most one for $`n\ge3`$. This quantifies the incompatibility of saturating the two adjacent level identities independently.

## Rotating the grid over the actual metric collar

Put $`v(x)=d_M(x,\partial M)`$, and take a closest boundary point of arclength $`s`$. The trace and spatial Lipschitz bound give $`P_a(x)\ge\pi/2-|s-ah|_{S^1}-v(x)`$. Rotate the grid uniformly through one mesh spacing, writing $`ah`$ for the rotated label in this inequality. Whenever $`v\lt h/2`$ a grid anchor is high almost surely. When $`h/2\le v\lt h`$ the probability is at least $`2(h-v)/h`$. These estimates are uniform in the closest boundary point. With $`V(t)=\mathrm{Area}\{v\lt t\}`$, integration gives

~~~math
 \mathbb E(S_1+S_2)\ge \frac2h\int_{h/2}^h V(t)\,dt .
~~~

Let $`A_1=c_1\pi^2=6.096286779581369797\ldots`$ be the preceding all-genus constant. The collar theorem, obtained by cutting level sets and capping the resulting curves, gives $`V(t)\ge2\pi t-\pi^2t^2/A_1`$ throughout this integration interval for $`n=112`$. Therefore

~~~math
 \mathbb E(S_1+S_2)\ge qK,\qquad q=\frac32-\frac{7}{12nc_1}.
~~~

This gives $`q=1.491567950877708\ldots`$. The argument uses all boundary distances and the topology-free collar inequality. It requires no assumption about uniqueness of minimizing paths or smoothness of the distance level. [Metric collar theorem](issue163_metric_collars.md)

## Turning compulsory area into a lower bound

Write $`U=0.9999999`$ for the raw trace budget. In billionths, the three already verified two-anchor diagonal traces have respective reserves under $`U`$ of $`19010,175116,19935`$. Denote those raw reserves by $`d_0,d_1,d_2`$, including the factor $`10^{-9}`$. All 58 matrices on the high-anchor union have reserve at least $`d_0`$. The two-anchor parent chamber and its two children carry compulsory projected areas in proportions $`1/2,1/4,1/4`$, including reflected chambers. This follows by bisecting the degree-one triangle in its two extreme coordinates. [Chamber fractions](issue163_comass_residual.md)

For each rotation, charge $`d_0`$ throughout the union, then $`d_i-d_0`$ on the compulsory projected area of each chamber. The normalized calibration has integral $`A_1`$ at every rotation. Averaging yields

~~~math
 \mathrm{Area}(M)\ge A_1+
 \frac{K}{U}\left[\frac{2d_0+d_1+d_2}{4}+(q-1)d_0\right].
~~~

Substitution gives the exact number above. The replay verifies the original matrices, reads the three trace reserves and the maximum over all high regions, and evaluates this formula with the directed enclosure of $`\pi`$. The Lean development covers the earlier Fourier theorem. [Certificate](issue163_anchor.cjs) · [Earlier Lean theorem](../docs/current-manuscript.md)
