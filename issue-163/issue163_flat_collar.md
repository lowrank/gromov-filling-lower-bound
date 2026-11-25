# How far can a comass correction near boundary anchors go?

Write $`n=112`$, $`h=\pi/n`$, and let $`\omega_0`$ be the normalized free finite field, whose boundary action is $`A_0=6.095000609501857507\ldots`$. A closed form of planar comass at most one that agrees with $`\omega_0`$ off the adjacent-anchor regions of the current grid has boundary action **below 6.107523028**. The same test still excludes 6.15 after widening the grid gaps fourfold. Here are upper bounds on the **calibration's boundary action**. [Free field and normalization](issue163_free_field.md) · [Earlier hemisphere lens test](issue163_midpoint.md#which-supports-leave-room-for-615)

| Gap width | Pairs of antipodal anchors on the aligned grid | Aligned supports | Union over all rotations |
|---|---:|---:|---:|
| $`h`$ | 112 | 6.107523028 | 6.120073216 |
| $`2h`$ | 56 | 6.119731292 | 6.145244034 |
| $`4h`$ | 28 | 6.142450184 | 6.185707234 |
| $`8h`$ | 14 | 6.177826871 | 6.268961721 |

Each entry uses one explicit comparison surface. The larger entries leave the attainable bound undetermined. [Exact checker](issue163_flat_collar.cjs)

## Which corrections does the test cover?

Use the convex space of continuous angular profiles $`P`$ with $`P_{a+\pi}=-P_a`$ and angular Lipschitz constant at most one. On the boundary the profile at arclength $`s`$ is $`b_s(a)=\pi/2-d_{S^1}(s,a)`$. For $`H=kh`$ and an aligned grid with spacing $`H`$, the allowed support is the union over its adjacent labels $`a,a+H`$ of the regions

~~~math
 P_a>\pi/2-H,\qquad P_{a+H}>\pi/2-H .
~~~

In the last column any real angle $`a`$ is allowed. Fine aligned supports are contained in coarse aligned supports. Each endpoint of the enclosing coarse gap lies within $`H-h`$ of the corresponding fine endpoint. The current bisected-gap and chamber corrections are all supported in the fine union.

The comparison applies to forms for which Stokes holds on the profile chains below, with pointwise norm at most one on separately 1-Lipschitz profile maps from Euclidean surfaces. The coefficients or primitives can use other angular labels and depend nonlinearly on the profile. Behavior on scalar walls is interpreted by pullback, as for the existing Lipschitz primitives. An argument that uses information about the distribution of distance profiles on an entire Riemannian filling can go beyond this comparison.

## An explicit flat triangle for each aligned gap

On $`0\le u\le v\le H`$ give the domain its Euclidean metric and the orientation $`du\wedge dv`$. For the gap beginning at zero set

~~~math
 P_t=\begin{cases}
 \pi/2-\max(t-u,v-t),&0\le t\le H,\\ \pi/2-t+(1-\lambda(t))u+\lambda(t)v,&H\le t\le\pi .
 \end{cases}
~~~

Take $`w=\lceil k/2\rceil`$, $`c=\lfloor(n+k-w)/2\rfloor`$, and let $`\lambda(t)`$ be $`(t/h-c)/w`$ clipped to $`[0,1]`$. Extend by antipodality. The formulas match at $`H`$ and across $`\pi`$. Each spatial gradient has length at most one. The outer formula has angular slope $`-1+\lambda'(t)(v-u)`$ in $`[-1,1]`$ since $`wh\ge H/2`$. The diagonal $`u=v=s`$ traces exactly $`b_s`$ for every label.

On $`u=0`$ the right anchor has value $`\pi/2-H`$. On $`v=H`$ the left anchor has that value. All other signed coarse labels outside this pair have value at most $`\pi/2-H`$ throughout the triangle. This follows from the affine formula and $`0\le u\le v\le H`$, including the antipodal labels. Thus these two edges stay outside the allowed support. Cone them to the zero profile by multiplying by a scalar in $`[0,1]`$. The cones stay outside too. The rotated triangles and cones form an oriented chain with the prescribed boundary loop. The rays at successive boundary vertices cancel. The triangles need only test the norm of a form. Their diagonal arclength is $`\sqrt2 H`$.

There are $`2n/k`$ triangles of area $`H^2/2`$. If $`q_k`$ is the mean evaluation of $`\omega_0`$ on one triangle, Stokes and the unit comass on the triangles bound the new action by

~~~math
 A_0+\frac{k\pi^2}{n}(1-q_k).
~~~

In increasing gap width the mean densities are approximately 0.857896, 0.859678, 0.865386 and 0.882511. In units of $`h`$ the scalar walls and the switches of the maximum are straight lines with integer coefficients. They partition one triangle into 1, 4, 14 and 108 polygons respectively. The checker uses their exact areas and a rational interior point in each to reconstruct and integrate the constant field.

## A collar that tests every rotation at once

Use $`s\in S^1`$ and $`0\le r\le H/2`$, with metric $`2(ds^2+dr^2)`$. On this cylinder put

~~~math
 P_a(s,r)=\mathrm{sgn}(b_s(a))\bigl(|b_s(a)|-r\bigr)_+ .
~~~

Where a coordinate moves, its two ordinary partial derivatives have magnitude one, so its metric gradient has length one. At $`r=H/2`$ the positive high labels $`P_a\gt \pi/2-H`$ form an open arc of length $`H`$. It contains no two labels at distance $`H`$. The entire inner loop can therefore be coned to zero outside the union over all rotations. The collar has area $`2\pi H`$. The action of the new form is at most this area plus the old action on the inner cone.

For a pair with angular separation $`d`$, the boundary polygon of the original pair coordinates $`(x,y)`$ is $`|x-y|\le d`$, $`|x+y|\le\pi-d`$, with degree one. The inner loop applies the scalar map $`x\mapsto\mathrm{sgn}(x)(|x|-H/2)_+`$ to both coordinates. For every open output bin the map has derivative one on its preimage interval. Integrating the old coefficient over the two preimage intervals intersected with this polygon gives its flux. The collapsed axes have zero planar area. With half-grid units the four excluded corners have exact triangular areas. At depth zero the checker recovers the original action exactly. [Pair-polygon and boundary-degree calculation](issue163_free_field.md)

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_flat_collar.cjs issue163_inputs
~~~

The checker uses hash-pinned inputs, integer polygon areas and rational enclosures of $`\pi`$. It prints the exact rational multiple of $`\pi^2`$ for each comparison.
