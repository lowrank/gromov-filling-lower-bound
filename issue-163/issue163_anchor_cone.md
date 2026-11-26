# A two-profile obstruction to nonnegative anchor corrections

Start from the normalized bisected-gap field and allow an arbitrary nonnegative rescaling of it. Add any combination of one-anchor corrections with nonnegative weights on arbitrary label separations and arbitrary real widths through $`38\pi/112\approx1.066`$. A comass-one field in this class has boundary action at most **6.097700344081**. Allowing all widths through $`\pi`$, with the original scale fixed, gives **6.098884806758**. This upper bound on a class of calibrations uses two explicit choices of planar gradients. [Signed construction](issue163_anchor.md) · [Integer replay](issue163_anchor_cone.cjs)

Write $`h=\pi/112`$ and $`n=112`$. For a real width $`0\lt r\le n`$ in bins and $`1\le j\lt n`$, consider the primitive

~~~math
 \beta_{r,j}=\sum_{a=0}^{2n-1}(P_a-\pi/2+rh)_+\, dP_{a+j}.
~~~

The tested fields are $`s\omega_{\rm ref}+\sum_j\int d\beta_{r,j}\,d\mu_j(r)`$, where $`s\ge0`$ and each $`\mu_j`$ is a finite nonnegative measure. This includes independently chosen nonnegative coefficients at individual anchors before averaging. Rotating by one grid step preserves the reference field and the oriented boundary action. Averaging all $`224`$ rotations preserves the comass bound and gives the displayed form. The results apply both to the free reference and to the bisected-gap reference. The table uses the latter.

| Allowed widths | Certified cost per unit of added action | Ceiling at the original scale | Ceiling with arbitrary nonnegative scale |
|---|---:|---:|---:|
| $`0\lt r\le1`$ | 2.393930 | 6.096013896656 | 6.096419866740 |
| $`0\lt r\le12`$ | 0.439759 | 6.096568671085 | 6.096841968041 |
| $`0\lt r\le38`$ | 0.165322 | 6.097696848319 | 6.097700344081 |
| $`0\lt r\le112`$ | 0.099764 | 6.098884806758 | — |

At the original scale, the first ceiling even allows the full old bisected-gap action. It is already smaller than the single-width **6.096286779581369797** obtained with signed coefficients and a reduced gap term. The third row shows that broadening a nonnegative mixture well into the interior still has little room. A general signed combination, a weight which turns off in a deeper layer, or a term depending jointly on additional scalar coordinates has a different test.

## A lower cost for every width and separation

Integrating $`\beta_{r,j}`$ over the boundary gives

~~~math
 A_{r,j}=2nh^2 M(r,j),\qquad
 M(r,j)=r^2-(r-j)_+^2-(r-n+j)_+^2 .
~~~

This follows by integrating the triangular weight on the boundary. The two subtractions occur where the derivative of the shifted coordinate reverses at its maximum or minimum. The function $`M(r,j)`$ increases on $`[0,n]`$. Its derivative is $`2\min(r,n-r,j,n-j)`$.

For a large real $`L`$ take a profile approaching the boundary anchor at $`-h`$ and use the previously recorded planar vectors $`z_i`$ in the unit disk,

~~~math
 P_i/h=55-i+(2i-55)/L,\qquad
 z_{i+n}=-z_i,\quad P_{i+n}=-P_i .
~~~

All angular inequalities between neighbors are strict. The first 28 offsets are negative and the others positive. Hence the free field is always in the same scalar cell, with only the anchor at $`-h`$ high at width one. Every bisected-gap term is zero. On these gradients either normalized reference evaluates to at least $`q_b=0.999701131561`$. The positive layer response is

~~~math
 D(r,j)=\lim_{L\to\infty}\ \sum_{a:\ P_a>\pi/2-rh}\det(z_a,z_{a+j}).
~~~

Let $`m=\lceil r\rceil`$. At noninteger widths the active set in this limit consists of the anchors at integer distance strictly below $`m`$ from $`-1`$, measured in grid steps. At $`r=m`$, the signs of the explicit offsets decide which of the tied endpoints enter. These are just two masks per integer. The replay computes each signed sum as an integer determinant sum and divides its lower bound by $`2nh^2 M(m,j)`$. This denominator bounds $`A_{r,j}`$ above throughout the interval. Taking the minimum over separations, integer widths, and the two masks gives the cost $`\kappa`$ in the table, with $`D(r,j)\ge\kappa A_{r,j}`$.

For arbitrary finite measures, choose the sequence of $`L`$ to avoid all atoms at the finitely many changing profile coordinates. The atomic radii form a countable set. The masks converge as stated at every fixed width, and each determinant sum is bounded by $`224`$. Dominated convergence proves the same cost estimate for the mixture. The inequalities use an open scalar cell, and the strict angular inequalities allow arbitrary disk-valued gradients on a sufficiently small planar patch. [Rational planar vectors](issue163_planar_witness.json) · [Tests on small genuine filling patches](issue163_short_routes.md)

If $`G\ge0`$ is the added boundary action, the near-anchor test gives $`sq_b+\kappa G\le1`$. At the original scale the total is bounded by $`A_{\rm ref}+(1-q_b)/\kappa`$.

## Testing a change of scale

Use the central scalar profile $`P_i=h/4`$ for $`0\le i\lt n`$ and extend by antipodality. Give label $`i`$ the planar direction $`(\cos(ih),\sin(ih))`$. The field is constant in the open positive central bin for every independent coordinate. All rotations of the gap terms vanish. Pair $`(i,j)`$ has determinant $`\sin((j-i)h)`$, and integer coefficient summation with directed sine bounds gives normalized evaluation at least $`q_p=0.999928509990`$. Every width through $`38h`$ in angular units vanishes on this profile, so $`s\le1/q_p`$.

Combining the two tests bounds the total by the maximum of $`1/\kappa+(A_{\rm ref}-q_b/\kappa)s`$ on $`[0,1/q_p]`$. Its slope is positive for each of the first three rows. The checker uses rational upper bounds throughout the last substitution. The central test and the near-anchor test involve no optimization.

~~~sh
node issue163_anchor_cone.cjs issue163_inputs
~~~
