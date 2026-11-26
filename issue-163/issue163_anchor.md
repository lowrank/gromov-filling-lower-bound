# A one-anchor correction to the all-genus filling bound

For every compact connected orientable Riemannian surface whose single boundary is an isometrically embedded intrinsic circle of length $`2\pi`$, the area satisfies

~~~math
 \mathrm{Area}(M)\ \ge \frac{2213775623134282058736195815563}{3583999641600000000000000000000}\pi^2
 >6.096286779581369797 .
~~~

The gain over the previous all-genus bound is $`(2134180925062877/55999994400000000000)\pi^2\gt0.000376134349233462`$. The previous gap correction requires two adjacent distance coordinates to be high. A single high coordinate already determines the signed integral against every other coordinate along its levels. Using these identities simultaneously gives a correction with positive boundary integral on the original grid. Only 58 local matrix tests change. [Level identities](issue163_slice_comass.md) · [Previous all-genus bound](issue163_comass_residual.md) · [Integer replay](issue163_anchor.cjs)

## A primitive with positive boundary integral

Write $`n=112`$, $`h=\pi/n`$, let $`a`$ run through the $`2n`$ signed anchor indices modulo $`2n`$, and use the antipodal distance differences

~~~math
 P_a(x)=\tfrac12\big(d_M(x,\gamma(ah+\pi))-d_M(x,\gamma(ah))\big),
 \qquad P_{a+n}=-P_a .
~~~

The coordinates are 1-Lipschitz in position and angular label. The isometric boundary condition prescribes $`P_a(\gamma(s))=\pi/2-d_{S^1}(ah,s)`$. Put $`L_a=(P_a-\pi/2+h)_+`$ and define

~~~math
 \alpha=\sum_{a=0}^{223} L_a\sum_{i=0}^{110} c_i\,dP_{a+i+1},
 \qquad c_{110-i}=c_i .
~~~

The seven distinct nonzero coefficients are given below.

| Index $`i`$ in the first half | $`10^6 c_i`$ |
|---|---:|
| 0 | 6500 |
| 1 | −2040 |
| 2 | −800 |
| 3 | −200 |
| 4 through 6 | 0 |
| 7 | −900 |
| 8 through 19 | −60 |
| 20 through 54 | −4 |
| 55 | 0 |

On the boundary $`L_a`$ is a triangle of height $`h`$ and base $`2h`$. Every $`P_{a+i+1}`$ in the displayed sum has boundary derivative $`+1`$ along its open base. Consequently $`\int_M d\alpha=2nh^2\sum_i c_i`$, with $`\sum_i c_i=3400/10^6`$. The same identity for a general weight on $`P_a`$ prescribes the signed transverse flux separately at almost every level. A local choice of gradients that spends too much flux on one label and too little on another can be charged using coefficients of either sign. Stokes for these Lipschitz functions follows by approximation. [Lipschitz Stokes and triangular traces](issue163_midpoint.md#the-closed-correction-and-its-norm)

Let $`W`$ denote the raw free field, $`U=9999999/10^7`$ its certified comass bound, and $`\eta`$ the raw bisected-gap addition. Use

~~~math
 \frac{W+f\eta+d\alpha}{U},\qquad f=1933/2500 .
~~~

If $`A_0`$ and $`B`$ denote the normalized free and bisected-gap boundary actions, its action is

~~~math
 A_0+f(B-A_0)+\frac{2\pi^2}{112U}\sum_i c_i .
~~~

Substituting the two known fractions gives the exact lower bound above once the comass is checked. [Free action](issue163_free_field.md) · [Bisected-gap action](issue163_midpoint.md#bisecting-the-same-boundary-gap)

At the original scale, even arbitrary nonnegative weights at widths through one grid step on top of the full old gap term have action at most **6.096013896656**. This certifies a benefit from allowing signed weights at the same boundary scale. [Two-profile obstruction](issue163_anchor_cone.md)

## Why 58 matrices cover every filling

Call a signed anchor high when $`P_a\gt55h`$. Any two high anchors have circular separation strictly smaller than $`2h`$, by $`P_a+P_b\le\pi-d_{S^1}(ah,bh)`$. Thus a point has zero, one, or two adjacent high anchors. With zero the old free-field bound applies. With a high anchor, rotate the frame so that $`-1`$ is high. Write $`b_i=dP_i`$ and $`P_i/h=55-i+e_i`$ for $`0\le i\le111`$. Angular Lipschitz continuity, including the edge from $`-1`$ to zero, gives

~~~math
 0\le e_{111}<1,\qquad -e_{111}\le e_0\le e_1\le\cdots\le e_{111}.
~~~

With only anchor $`-1`$ high, its two neighbors give $`e_0\le0\le e_{110}`$. The bin indices of the old field therefore have the form $`111-i-\mathbf1_{\{i\lt k\}}`$ with $`1\le k\le110`$. Ties can be assigned so the first $`k`$ entries are nonpositive and the remaining entries nonnegative. On the preimage of any tied scalar value its differential vanishes almost everywhere, so this assignment preserves the pulled-back form. All gap terms vanish, and the new contribution is

~~~math
 \sum_{i=0}^{110}c_i\, b_i\wedge b_{111}.
~~~

Reflection about anchor $`-1`$ fixes coordinate 111 in the signed frame and sends $`P_i`$ to $`-P_{110-i}`$ for the other indices. It interchanges $`k`$ and $`111-k`$ and changes the sign of the form. The symmetry of $`c`$ leaves 55 cases. The checker also reconstructs the reflected matrices entry by entry.

With two adjacent anchors high, take them to be $`-1,0`$. All old scalar bins are $`111-i`$. Both anchor terms occur, giving

~~~math
 \sum_{i=0}^{110}c_i\big(b_i\wedge b_{111}+b_0\wedge b_{i+1}\big).
~~~

This addition changes sign upon coordinate reversal, just as the old gap field does. Up to reflection across the gap midpoint, the old additions in the three chambers are $`b_0\wedge s`$, $`b_0\wedge(s+u)`$, and $`b_0\wedge s-b_{111}\wedge u`$, using the previously published parent and child coefficient vectors. The replay multiplies these by $`f`$ before adding the two anchor terms. On equality sets the competing Lipschitz branches have the same differential almost everywhere. This covers the three remaining cases. [Gap chambers and symmetry](issue163_midpoint.md#bisecting-the-same-boundary-gap)

For each changed skew matrix $`Y`$ a nonnegative rational diagonal $`D`$ certifies $`D+iY/2\succeq0`$. Its trace is at most $`0.999980890\lt U`$ in all 58 cases. Evaluating on $`z_i=dP_i(X)+i\,dP_i(Y_0)`$ for an oriented orthonormal frame $`(X,Y_0)`$ gives a bound of $`\sum_i D_{ii}|z_i|^2\le U`$ for the absolute raw density. The field, primitive and area comparison work in every genus.

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_anchor.cjs issue163_inputs
~~~

The replay reconstructs the old coefficients from pinned inputs, checks the integer Gram residual and trace for each new matrix, and computes the exact action and its decimal floor. Floating-point Cholesky only proposes a factor. Each accepted positive semidefinite inequality is verified over the integers. The proof uses the established free-field theorem elsewhere. The Lean development covers the earlier Fourier result. [Diagonals](issue163_anchor_diagonals.json) · [Global free-field certificate](issue163_free_field.md) · [Earlier Lean theorem](../docs/current-manuscript.md)
