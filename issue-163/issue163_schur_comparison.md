# A Hilbert-transform comparison with the full hemisphere action

A triangular distance trace has an extra extremal property under harmonic conjugation. It gives a comparison form with limiting boundary action $`2\pi`$ and an exact criterion for its pointwise comass to be one. The criterion includes higher angular harmonics far from the round hemisphere. For an actual filling of area at most $`6.15`$, the argument forces more than **0.1331853** of an explicit integral depending only on its scalar profiles. Controlling that integral for all fillings remains open. [Finite all-genus area certificate](issue163_anchor_occupation.md) · [Numerical diagnostics on fixed profiles](issue163_schur_check.py)

## A sharp strip for the harmonic conjugate

Let $`F(a+\pi)=-F(a)`$, $`\mathrm{Lip}(F)\le1`$ and $`\|F\|_\infty\lt h=\pi/2`$. The Hilbert transform $`H`$ on the angular circle has multiplier $`-i\,\mathrm{sgn}(k)`$ and kills constants. Set

~~~math
 u=\tfrac12\log\frac{1+\sin F}{1-\sin F},\qquad V=Hu,\qquad
 U(z)=2\sum_{k\gt0}\widehat u_k z^k,\qquad S(z)=\tanh(U(z)/2).
~~~

The boundary values of $`U`$ are $`u+iV`$. At every angular label, $`|V(a)|\lt\pi/2`$. To prove this fix $`v=F(a)`$. On $`[a-\pi,a]`$ the greatest 1-Lipschitz graph joining $`-v`$ to $`v`$ is the tent with peak $`h`$ at $`s=a-(h-v)`$. Its antipodal extension $`b_s(t)=h-d_{S^1}(s,t)`$ is below $`F`$ on the following half. The transformation from $`F`$ to $`u`$ is increasing. The Hilbert kernel $`\cot((a-t)/2)`$ is positive on the preceding half and negative on the following half. Thus the transformed triangle gives an upper bound at $`a`$. The difference is bounded by a constant times the distance to $`a`$, so comparison of the principal values is valid. Its logarithmic poles at $`s,s+\pi`$ are integrable. The triangle has analytic extension

~~~math
 U_{b_s}(z)=\log\frac{1+e^{-is}z}{1-e^{-is}z}.
~~~

Its boundary imaginary part is $`\pi/2`$ on the open half beginning at $`s`$. The comparison is strict for an interior profile because it differs on a neighborhood of the tent peak. Apply the same argument to $`-F`$ for the opposite bound. The values vary continuously since the Hilbert transform of a Lipschitz function is Hölder continuous of every exponent below one. This also follows by splitting the difference of the two principal-value integrals at twice the separation of their poles. The maximum principle now puts $`S`$ strictly inside the unit disk up to the circle. The map is odd and holomorphic. At the round profile $`F(a)=\arcsin(R\cos(a-s))`$ it is $`S(z)=r e^{-is}z`$, where $`R=2r/(1+r^2)`$. This follows by taking the real part of the same logarithm with $`z`$ replaced by $`rz`$.

## Exact action and the surplus on every filling

Write $`\langle\cdot\rangle`$ for uniform angular probability and set

~~~math
 D=\sec F=\cosh u,\qquad c=\cos V,\qquad m=Dc,\qquad
 d=D/c=\frac{1+|S|^2}{1-|S|^2}.
~~~

Here and below $`S`$ on the right denotes its boundary values. Both $`D,c`$ are positive. The mean $`\langle m\rangle=1`$ is exact, since $`m=\Re\cosh U`$ and $`U(0)=0`$. For an antiperiodic measurable family $`z_a=\partial_1F_a+i\partial_2F_a`$ in the unit disk the comparison is

~~~math
 Q_F(z)=-\Im\langle c\,\overline z\,H(Dz)\rangle,\qquad
 |Q_F(z)|\le 1+\Gamma(F),\qquad
 \Gamma(F)=\sqrt{\langle D^2\rangle\langle c^2\rangle}-1 .
~~~

Cauchy–Schwarz and the $`L^2`$ Hilbert isometry on antiperiodic functions prove the bound. The entire surplus comes from variation of a single positive scalar in the angular label. Precisely,

~~~math
 (1+\Gamma)^2=1+
 \tfrac12\left\langle m_a m_b\,\frac{(d_a-d_b)^2}{d_a d_b}
               \right\rangle_{a,b}.
~~~

This follows by expanding $`\langle m d\rangle\langle m/d\rangle`$. For example $`1+\Gamma\le\cosh(\tfrac12\mathrm{osc}(\log d))`$. For $`l\le d\le L`$, average $`d+lL/d\le L+l`$ against the probability $`m`$ and bound the product by the square of the arithmetic mean.

On an actual filling use its antipodal half-distance differences $`F_a(x)`$ and regularize them by $`F^{(q)}_a=\arcsin(q\sin F_a)`$ for $`0\lt q\lt1`$. This scalar change has derivative between zero and one. Apply the comparison to its spatial gradients. The pulled-back form is $`-\langle dF^{(q)}_a\wedge d\sin V^{(q)}_a\rangle`$. By Stokes its integral is $`\langle\int_{\partial M}\sin V^{(q)}_a\,dF^{(q)}_a\rangle`$. On the boundary, writing $`t=a-s`$ with boundary arclength $`s`$, the round logarithm gives

~~~math
 \sin V^{(q)}_a=\partial_s F^{(q)}_a
     =\frac{q\sin t}{\sqrt{1-q^2\cos^2t}} .
~~~

Integrating the square gives $`2\pi(1-\sqrt{1-q^2})`$, since the angular mean of $`(1-q^2\cos^2t)^{-1}`$ is $`(1-q^2)^{-1/2}`$. One can first replace $`V^{(q)}`$ by the Hilbert transform of a finite Fejér mean of $`u^{(q)}`$. These finite sums are spatially Lipschitz. At fixed $`q`$ the derivatives converge in $`L^2(M\times S^1)`$ by the bounded Hilbert multiplier, their cosine factors are uniformly bounded and converge in measure, and the smooth boundary data converge uniformly. This justifies Stokes without any boundary regularity assumption on the unregularized transform. Consequently, in every genus,

~~~math
 A+\liminf_{q\uparrow1}\int_M\Gamma(F^{(q)}(x))\,dA(x)\ \ge\ 2\pi .
~~~

For example the estimate would reach $`6.15`$ if the limiting integrated surplus were at most $`2\pi-6.15`$. A sufficient uniform angular oscillation bound for $`\log d`$ throughout the regularized profiles as $`q\uparrow1`$ is 0.41548. The strip theorem alone gives no such bound.

## Exactly which profiles have pointwise comass one?

The supremum of $`Q_F`$ over independent disk gradients is one **if and only if** $`|S(e^{ia})|`$ is constant in $`a`$. Complex conjugation of a test changes the sign of $`Q_F`$, so this also classifies the absolute comass.

To prove it, form the zero-free analytic outer function $`O`$ with boundary values $`D\exp(iH\log D)`$. It is obtained by exponentiating the analytic extension of $`\log D+iH\log D`$. The function $`D`$ is half-turn invariant, hence $`O`$ is even. Write $`w=e^{ia}O`$ and take the unit gradient $`z=w/D`$. It is antiperiodic, and $`H(Dz)=-iDz`$ by positive Fourier support. This test gives $`Q_F=\langle m\rangle=1`$ for **every** interior profile. If the modulus of $`S`$ is constant, $`d=D/c`$ is constant and $`\Gamma=0`$, proving sufficiency.

Conversely suppose this unit test is a maximizer. Vary it to $`z\exp(i\varepsilon h)`$ for smooth real half-turn invariant $`h`$. Skew-adjointness of $`H`$ gives derivative

~~~math
 \Re\left\langle h\overline z\,[cH(Dz)+D H(cz)]\right\rangle .
~~~

The first term has zero real part. Write $`P_-`$ for projection onto strictly negative frequencies. On odd functions $`H=-iI+2iP_-`$. Vanishing for all $`h`$ therefore says $`\overline w P_-(cz)`$ is real almost everywhere. This is a function with strictly negative Fourier support, so it vanishes. Thus $`cz`$ is the trace of an odd analytic function. The quotient $`(cz)/w=c/D`$ extends analytically into the disk since both vanish at zero and $`w(z)=z O(z)`$ has no further zero. It is continuous up to the boundary (equivalently use bounded analytic boundary values), and its boundary values are real. It is constant. This proves necessity and gives a first-order ascent direction at every variable-modulus profile.

For example, $`F(a)=\arcsin(R\cos(ka))`$ for any positive odd $`k`$ and $`kR\le1`$ is admissible and has $`S(z)=r z^k`$. Its pointwise comass is exactly one at every allowed amplitude. More generally the criterion includes any constant multiple of an odd finite Blaschke product whenever its recovered scalar profile is 1-Lipschitz. A finite Blaschke product is a product of disk factors $`(z-\alpha)/(1-\overline\alpha z)`$ of unit boundary modulus, times a constant of modulus one.

If $`S=rB`$ with $`|B|=1`$ on the circle and $`B(0)=0`$, then $`\sin F=R\Re B`$. The scalar regularization replaces $`R`$ by $`qR`$ and preserves $`B`$, by the analytic logarithm used in the strip proof. Thus if these profiles occur almost everywhere on a filling, allowing the inner function and radius to vary with the point, the full area inequality gives $`A\ge2\pi`$. The boundary triangle is included by the same regularization.

## Fixed tests against the 6.15 budget

Global normalization of a full-action form would reach $`6.15`$ at comass at most $`2\pi/6.15=1.021656\ldots`$. Use the single phase $`z=e^{ia}\exp(iH\log(Dc)/2)`$ without fitting any parameters. On the eroded triangle $`F=\mathrm{sgn}(b_0)(|b_0|-e)_+`$ at $`e=0.20`$, its values on 256 and 512 equally spaced midpoint labels are approximately **1.0184** and **1.0185**. At $`e=0.05`$ the 512 and 1024 label readings lie on opposite sides of the budget. The scalar Cauchy upper majorant is already above 1.05 at this latter width. The checker reports the actual grid values. These are quadrature tests on one prescribed phase. The strict failure of unit comass follows independently from the analytic criterion whenever the Schur modulus varies. The finite-width results do not certify a continuum ceiling or an improved area lower bound.

Run the fixed phase tests with NumPy from the repository's <code>issue-163</code> directory.

~~~sh
python3 issue163_schur_check.py
~~~
