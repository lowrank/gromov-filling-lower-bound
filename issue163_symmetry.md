# A symmetry test for the 6.15 circle filling bound

Consider a compact connected orientable Riemannian surface $M$ whose single boundary is an isometrically embedded circle of length $2\pi$. Identify antipodal boundary points and take the orientation double cover $X$ of the resulting closed nonorientable surface. Write $G$ for its lifted metric and $\tau$ for the deck transformation. Its area is twice the area of $M$.

**A sufficient condition in every positive genus.** Suppose $X$ admits a smooth orientation-preserving involution $J$ commuting with $\tau$, with sphere quotient and $2\,\mathrm{genus}(X)+2$ fixed points. If the ratio of the largest to smallest singular value of $dJ$ in $G$ is everywhere at most $1.6$, then

$$
 \mathrm{Area}(M)>6.155019283 .
$$

A topological involution with these properties exists in every positive genus. The hypothesis is the quantitative distortion estimate for a suitable choice. There is a stronger area-weighted criterion, including a gain when the regions exchanged by $J$ have different area densities. A flat-collar example below distinguishes two choices of $J$ with identical boundary markings.

## A length estimate from the branched cover

Every curve on $X$ from $p$ to $\tau p$ has $G$-length at least $\pi$. Its projection is an orientation-reversing loop in the antipodal quotient. A transverse representative crosses the glued seam an odd number of times. Split at the crossings and bound each segment by the intrinsic boundary distance between its endpoints in $M$. Translating alternate boundary arcs by $\pi$ concatenates the comparison arcs into a path from a circle point to its antipode. Length approximation gives the result for rectifiable curves. The two copies of $M$ give a continuous metric in seam normal coordinates, sufficient for this argument.

If $M$ has genus $g$, then $X$ has genus $2g$. One model for its topological double cover is the smooth compactification of

$$
 w^2=-\prod_{j=1}^{2g+1}\big((z-a_j)^2+b_j^2\big)
$$

with distinct nonreal roots and real $a_j$, $b_j>0$. Conjugation acts freely, including at the two points at infinity. The involution $w\mapsto-w$ commutes with conjugation and has sphere quotient. Classification of closed nonorientable surfaces identifies the quotient with the one from $M$, and the identification lifts to the orientation covers. Transporting this involution provides an initial $J$.

Define the reversible norm
$$
 F_x(v)=\tfrac12\bigl(|v|_G+|dJ_x v|_G\bigr).
$$
It is invariant under $J$ and $\tau$. Its length on a curve is the arithmetic mean of the $G$-lengths of that curve and its image under $J$. In particular its least length between deck partners is at least $\pi$.

Choose any smooth $J$- and $\tau$-invariant Riemannian reference metric $h$. Let $m_h(x)$ be the average of $F_x(v)$ on the $h$-unit circle, with uniform angular probability. The density $m_h^2 dA_h$ depends only on the conformal structure of $h$. Put $I(h)=\int_X m_h^2 dA_h$. Then
$$
 \inf_p d_F(p,\tau p)^2\ \le\ \frac{\pi}{4} I(h),
 \qquad I(h)\ge4\pi .
$$

Here is the extension of the Bangert–Croke–Ivanov–Katz argument needed for a direction-dependent norm. In the complex structure of $h$, the map $X\to X/J$ is a hyperelliptic double cover. The induced involution on its quotient sphere is a reflection, with an odd number of branch points in each hemisphere. For each branch point in one hemisphere use the conformal football of their Lemma 7.1. Pull the descended norm back under the football's round-sphere double cover. The integral of the squared angular mean on that sphere equals $I(h)$, since each of the two covers of the quotient has degree two and the density is conformally invariant. Finite branch sets do not affect the integral. [Bangert, Croke, Ivanov and Katz, §§5–7 and Appendix B](https://arxiv.org/pdf/math/0405583)

For a uniformly rotated round great circle, its expected length in the pulled-back norm is $\tfrac12\int_{S^2}m\,dA_{\rm rd}$. Indeed its unit tangent has uniform direction conditional on its basepoint, and its round length is $2\pi$. Cauchy–Schwarz bounds the square of this expectation by $\pi I(h)$. We may choose a generic circle of length at most $\sqrt{\pi I(h)}+\epsilon$. It projects to a figure eight. The round antipodal map exchanges its two halves and projects to the reflection, so the two hoops have equal lengths. This supplies a loop of length at most $(\sqrt{\pi I(h)}+\epsilon)/2$ based on the equator winding once around the selected branch point. The odd-winding argument of Lemmas 7.2–7.3 cuts and exchanges arcs while preserving their combined length. It applies to the reversible norm and produces an equator-based loop of at most that length whose lift joins deck partners. Letting $\epsilon$ tend to zero proves the estimate. The argument applies to continuous positive metrics by approximation from above with the finite symmetries preserved.

An independent check already reaches $6.15$ at smaller distortion using the Riemannian metric $H=(G+J^*G)/2$. Its lengths dominate those for $F$, it makes $J$ an isometry, and the original hyperelliptic theorem gives $\mathrm{Area}(X,H)\ge4\pi$. If $a,b$ are the two area densities relative to a common measure, direct evaluation of the determinant gives
$$
 \frac{dA_H}{(dA_G+dA_{J^*G})/2}
 =\sqrt{1+\frac{ab}{(a+b)^2}(K+K^{-1}-2)}
 \le\frac{\sqrt K+1/\sqrt K}{2}.
$$
Thus $K\le3/2$ throughout already gives $\mathrm{Area}(M)\ge4\pi\sqrt6/5>6.15623$. Averaging lengths gives the stronger constants below.

## The local calculation

Use any common $J$- and $\tau$-invariant area element $d\mu$. Write $a=dA_G/d\mu$, $b=dA_{J^*G}/d\mu$, $q=b/a$, and $K\ge1$ for the singular-value ratio of $dJ$. The normalized tensors $G/a$ and $J^*G/b$ have determinant one relative to $d\mu$. In an area-preserving frame they are $I$ and $\mathrm{diag}(K,K^{-1})$. Write
$$
 p(s)=\frac1{2\pi}\int_0^{2\pi}\sqrt{e^s\cos^2\theta+e^{-s}\sin^2\theta}\,d\theta,\qquad k=\log K .
$$
The determinant-one reference tensor $\mathrm{diag}(e^s,e^{-s})$ has angular mean $(\sqrt a\,p(s)+\sqrt b\,p(k-s))/2$. Consequently define
$$
 C(K,q)=\min_{0\le s\le k}\frac{(p(s)+\sqrt q\,p(k-s))^2}{2(1+q)},\qquad
 R_J=\frac{1}{\mathrm{Area}(X)}\int_X C(K,q)\,\frac{a+b}{2}\,d\mu .
$$
Then
$$
 \boxed{\mathrm{Area}(M)\ge\frac{2\pi}{R_J}.}
$$

To check the minimization, $p$ is even and strictly convex. The second derivative of each positive square-root integrand is at least one quarter of that integrand. For determinant-one tensors the distance $d(A,B)=\log\lambda_{\max}(A^{-1}B)$ is symmetric and obeys the triangle inequality by the order comparison $B\preceq e^{d(A,B)}A$. For any reference shape the two distances to the given shapes therefore sum to at least $k$. The displayed diagonal interpolation realizes all splits $(s,k-s)$, so it minimizes among all reference shapes. The unique minimizer changes to $k-s$ when the tensors are interchanged. This yields a $J$- and $\tau$-invariant reference metric globally. At $k=0$ the shapes coincide. The minimizing shape is continuous by uniqueness and can be approximated by smooth invariant metrics. Finally $I(h)=R_J\mathrm{Area}(X)$ in the limit and $\mathrm{Area}(X)=2\mathrm{Area}(M)$.

At $q=1$ the minimizing $s$ is $k/2$. For every $q$ the same trial gives
$$
 C(K,q)\le p(k/2)^2\frac{(1+\sqrt q)^2}{2(1+q)}\le p(k/2)^2 .
$$
This proves the $1.6$ criterion. More generally a $\tau$-equivariant smooth marking of dilatation at most $\sqrt{1.6}$ from $X$ to an ovalless real hyperelliptic reference surface suffices because conjugating its conformal involution gives $K\le1.6$. The result covers a neighborhood of the hyperelliptic locus. Area concentrated on regions of smaller $C(K,q)$ also improves the estimate.

| Paired tensors | Conditional area from this computation |
|---|---:|
| $K\le1.5$, arbitrary area ratios | $>6.187432160$ |
| $K\le1.6$, arbitrary area ratios | $>6.155019283$ |
| Model $K=1.62$, $q=1$ | $6.148263562\ldots$ |
| Model $K=2$, $q=1$ | $6.009286552\ldots$ |
| Model $K=2$, exchanged area ratio $2:1$ | $>6.194202176$ |
| Model $K=3$, exchanged area ratio $4:1$ | $>6.327370211$ |

The model rows report the value if the indicated pair type supplies the entire averaged density. Interchanging the members replaces $q$ by $1/q$ and preserves the cost. For an actual surface one integrates the pair costs with their area weights. The balanced threshold for $6.15$ lies strictly between $K=1.61488$ and $1.61489$.

**A sufficient condition for the sharp $2\pi$.** Suppose that wherever $J$ fails to preserve angles, its distortion satisfies $K\le3$ and the larger of the two area densities is at least four times the smaller one. Then $R_J\le1$ and $\mathrm{Area}(M)\ge2\pi$.

Indeed $C$ is nondecreasing in $K$ because any split of a larger $k$ can be shortened while decreasing both angular costs weakly. It is symmetric under $q\mapsto1/q$. For $q\ge1$ a minimizing split can be chosen with $s\ge k/2$, so $A=p(s)\ge B=p(k-s)$. The derivative of $(A+tB)/\sqrt{1+t^2}$ has the sign of $B-tA$, which is nonpositive for $t=\sqrt q\ge1$. Taking minima shows that $C$ is nonincreasing as the larger area ratio grows. At $(K,q)=(3,4)$ even the simple trial $e^s=2$ gives $C<0.994$ by the rational series test. On the conformal region $C(1,q)=(1+\sqrt q)^2/(2(1+q))\le1$. Integrating proves the claim. This supplies an explicit sharp-bound criterion on angle-distorting involutions as well as a reason to test the area Jacobian along with the dilatation.

## A collar test with the same total twist

Consider two exchanged flat collars of width $w$, circumference $L$, and a tangential marking offset $d$ between their ends. Use a shear $(x,y)\mapsto(x+f(y),y)$ on one collar and its inverse on its partner. Write $u=f'(y)$, so that the mean shear is $d/w$. For this map $q=1$ and $\tfrac12\log K=\mathrm{arsinh}(|u|/2)$. The local cost is
$$
 H(u)=p(\mathrm{arsinh}(u/2))^2 .
$$

**Uniform shear minimizes the cost among all shear interpolations of this offset.** To prove this, put $s=\mathrm{arsinh}(u/2)$. For $s>0$ integration in $\theta$ gives $p''+\coth(s)p'=3p/4$. In detail, with $A=\cosh s+\sinh s\cos\theta$ and $\nu=1/2$, applying $\partial_s^2+\coth(s)\partial_s-\nu(\nu+1)$ to $A^\nu$ gives $(\nu/\sinh s)\partial_\theta(\sin\theta\,A^{\nu-1})$. Its angular mean is zero.

Set $v=\tanh s$ and $l=p'/p$. Then $0\le l\le v/2$ because $p/\sqrt{\cosh s}$ is the angular mean of $\sqrt{1+v\cos\theta}$, an even concave function of $v$. The sign of $H''(u)$ is the sign of $l^2+3/4-(v+1/v)l$. On this interval the latter is at least its value at $v/2$, namely $(1-v^2)/4>0$. At zero $H(u)=1+3u^2/32+O(u^4)$. Evenness and Jensen's inequality finish the proof.

For $d/w=0.4$, distributing the twist across the collar gives $2\pi/H(0.4)>6.191171839$. Placing the same twist in one tenth of its width gives $2\pi/(0.9+0.1H(4))=5.737643430\ldots$. These values use a full area weight for the collar test. If collars with uniform shear occupy a fraction $m$ of the cover and the complement has $C\le1$, the denominator becomes $1+m(H(d/w)-1)$.

There is also a dimensional estimate. The large-shear limit is $H(u)/|u|\to4/\pi^2$, obtained by dividing the angular integrand by $e^{|s|/2}$ and averaging $|\cos\theta|$. Convexity and $H(0)=1$ imply $H(u)-1\le4|u|/\pi^2$. Jensen applied to the square root gives the second upper estimate $H(u)-1\le\sqrt{1+u^2/4}-1\le u^2/8$. Thus, if the complement has $C\le1$ and the comparison involution is glued using these flat collars, then
$$
 \mathrm{Area}(M)\ge 2\pi-\frac12\sum_j L_j
       \min\left\{\frac{d_j^2}{8w_j},\frac{4|d_j|}{\pi^2}\right\}.
$$
The sum counts collars on $X$, including both members of each pair. Piecewise smooth shear interpolations may be smoothed in arbitrarily thin end strips with their cost converging to the displayed value.

## What the calculation decides

A sufficient target on a general filling is $R_J\le 2\pi/6.15=1.021656\ldots$ for some comparison involution. The test suggests spreading twists over available collar width and pairing regions with different area densities when constructing one. The missing step is a geometric estimate on the integrated cost of such a pairing for every putative filling below $6.15$. The sharper target $R_J\le1$ would yield $2\pi$.

The entire numerical experiment has one scalar variable. The program uses rational bounds on the angular integral and on $\pi$ for each quoted inequality. With $x=\tanh^2s$, the mean $p(s)/\sqrt{\cosh s}$ has initial terms $1-x/16-15x^2/1024$. The absolute successive term ratio from index $m\ge1$ is $x(16m^2-1)/(16(m+1)^2)$. A geometric tail bound encloses the integral. The unequal-area search selects a rational trial reference and verifies its cost independently. From the branch root run

~~~sh
python3 issue163_symmetry.py
~~~
