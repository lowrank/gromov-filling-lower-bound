# A transverse moment on intrinsic boundary balls

For a compact connected orientable isometric filling of the circle of length $`2\pi`$, of arbitrary genus,

~~~math
 \mathrm{Area}(M)>6.096298010216328189 .
~~~

The increase over the preceding bound is $`0.000005272525428022\ldots`$. Its geometric source is a prescribed transverse derivative on an actual metric ball. Two row-sum tests on previously certified matrices suffice. This gain leaves the requested unrestricted target of $`6.15`$ open. A separate projective-line argument reaches the hemisphere bound on a family of conformal structures in every positive genus from two onward. [Preceding all-genus bound](issue163_anchor_occupation.md) · [Projective-line comparison](issue163_projective_lines.md) · [Integer replay](issue163_anchor.cjs)

## A moment in a radial frame

Use the previous signed-anchor form on a rotated grid with $`n=112`$ and $`h=\pi/n`$. Its raw comass budget is $`U=0.9999999`$. Divide each of the $`2n`$ boundary gaps into four equal intervals. Around the arclength midpoint $`s`$ of each interval take the intrinsic open ball of radius $`r=h/8`$. The $`8n`$ balls have disjoint interiors by the boundary distance condition. Their metric areas are denoted by $`m_s`$.

In the signed frame of a gap all $`n`$ coordinates $`P_j`$ have boundary slope one throughout it. Each ball lies in one of the two child chambers or its reflection. Indeed the common boundary offset $`t`$ runs from $`-h/2`$ to $`h/2`$ over the gap. At a ball center it is one of $`-3h/8,-h/8,h/8,3h/8`$. On the ball each coordinate offset stays within $`r`$ of this value by spatial Lipschitz continuity. The two extreme offsets therefore stay in the same open quarter interval. Their signs and the comparisons of their sum with $`\pm h/2`$ select the same child differential throughout the ball. Write $`Y`$ for its constant raw skew coefficient matrix and $`D`$ for its certified positive diagonal, so $`D+iY/2`$ is positive semidefinite. [Chamber formulas](issue163_midpoint.md#bisecting-the-same-boundary-gap) · [Raw anchor matrices](issue163_anchor.md)

Set $`T_s=(r-d_M(s,\cdot))_+`$. Almost everywhere in the ball use an oriented orthonormal frame with first vector $`\nabla T_s`$. Write $`p_j,q_j`$ for the two components of $`\nabla P_j`$. Stokes gives a vector identity, up to a common orientation sign,

~~~math
 \int_{B(s,r)} q_j\,dA
 =\int_M dT_s\wedge dP_j
 =\int_{\partial M}T_s\,dP_j=r^2
 \qquad\text{for every }j .
~~~

The first equality uses the distance eikonal identity in the ball, and the last uses the area of the boundary tent on an interval of length $`2r`$. Lipschitz Stokes follows by smoothing in charts, as in the original gap computation.

Write $`\omega`$ for the raw form evaluated in this frame and put $`z=p+iq`$. Since $`|z_j|\le1`$,

~~~math
 U-\omega\ \ge\ U-\mathrm{tr}(D)+z^*(D+iY/2)z .
~~~

Minimizing the last quadratic over $`p`$ at fixed $`q`$ gives $`q^{\mathsf T}S q`$, where $`S=D+YD^{-1}Y/4`$ is positive semidefinite. For $`\mathbf1`$ the all-ones vector, the two child matrices satisfy

~~~math
 \mathbf1^{\mathsf T} S\mathbf1
 =\mathrm{tr}(D)-\sum_j\frac{((Y\mathbf1)_j)^2}{4D_{jj}}
 \ \ge\ s_*=\frac{478}{100000}.
~~~

Reflection preserves this value because the common signed tangent changes at most by an overall sign and permutation. The replay rounds each rational subtrahend upward. The resulting two lower bounds are $`0.004780071311`$ and $`0.004947550296`$. Jensen's inequality and the ball moment give an integrated reserve of at least $`s_* r^4/m_s`$ **in addition to** the trace reserve already counted on that ball. No search for new matrices enters this estimate.

## Summing over the balls

It suffices to treat $`A=\mathrm{Area}(M)\le6.09631`$. The sum $`m=\sum_s m_s`$ is less than $`11/100`$. To check this, use the previous phase estimate with the set of all boundary triangles. Its arclength map has Lipschitz constant one, and the full angular profile of every point of these balls is within $`r`$ of the triangle at its center. The estimate gives

~~~math
 m\le A-6.09628\,\kappa(r)^2,\qquad
 \kappa(r)=1-\frac4\pi(r+d_r),\qquad
 d_r=\frac{2r}{1+\sqrt{1-4r/\pi}} .
~~~

At $`r=\pi/896`$, $`d_r\lt1.01r`$ and $`\kappa(r)\gt0.991`$. The upper bound on $`m`$ follows. [Phase estimate and extension of the triangular coordinates](issue163_profile_occupation.md)

By Cauchy–Schwarz, $`\sum_s r^4/m_s\ge(8nr^2)^2/m`$. This holds at each rotation. Averaging the original trace reserves over rotations pays for the preceding constant $`C`$. The new quadratic reserve is disjoint from that accounting and is divided by $`U\lt1`$ when the form is normalized. Keeping the weaker factor one gives

~~~math
 A\ \ge\ C+\frac{478}{100000}\frac{100}{11}
             \left(\frac{\pi^2}{896}\right)^2
 \ >\ 6.096298010216328189
 \qquad(A\le6.09631).
~~~

The numerical conclusion also holds above the cutoff. From the repository's `issue-163` directory, `node issue163_anchor.cjs issue163_inputs` checks the previous matrices, the two Schur complement inequalities and the new decimal floor using integer arithmetic. This is a written geometric proof with finite arithmetic checks. The Lean endpoint is the earlier Fourier theorem. [Lean verification status](../docs/current-manuscript.md)
