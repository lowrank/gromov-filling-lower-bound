# An annular Fourier calibration for orientable circle fillings

For a compact connected orientable Riemannian surface with one boundary component isometrically filling the intrinsic circle of length $2\pi$, the following computer-assisted bound holds in every genus.

$$
\mathrm{Area}(M)\ \ge\
\frac{616679280604206359}{10^{18}}\,\pi^2
\ >\ 6.086380541911894628 .
$$

The input theorem is the finite transported $112$-anchor certificate in the 25 November 2026 circle-filling bundle. The additional certificate below has an integer-arithmetic replay. This result extends the research bundle. The Lean repository verifies the earlier Fourier theorems of Chen, Li and Zhong. A Lean formalization of the present certificate is open. [Earlier manuscript](https://arxiv.org/abs/2609.08251) · [Lean manuscript ledger](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/docs/current-manuscript.md)

## The finite input and the new form

Write $N=112$, $h=\pi/N$, $Q_D=32\cdot10^{12}$, $T=31970639125404$ and $U=T/Q_D$. The archived finite form $\Omega$ alone has comass at most $U$ and normalized action
$
\int_M\Omega/U=A\pi^2,\quad A=2182536605945/3552293236156.
$
The input includes its boundary orientation, closedness, complete profile coverage, matrix witnesses and exact inheritance. The new calculation starts from this finite action before any archived Fourier disk is added.

Let $F_k$ be the antipodal distance difference at angle $kh$. Put $F_{k+N}=-F_k$. The angular sample sequence is $1$-Lipschitz in arclength, and each spatial coordinate is $1$-Lipschitz. Form the planar map
$$
Y=\frac2N\sum_{k=0}^{N-1}g(F_k)e^{ikh}.
$$
The odd nondecreasing map $g$ has $g(0)=0$. At the consecutive positive-grid knots (including zero), in units of $h$, and with its slopes in units of $1/1000$, the data are

~~~
knots    0  8  16  24  32  36  40  42  44  46  48  50  52  54  56
slopes   1000 988 997 1036 1043 1213 1200 1222 1144 1000 700 650 500 1000
~~~

Define the polygonal radius $\rho(z)=\max_{0\le k<N}|\Re(e^{-ikh}z)|$. Use the dimensionless coordinate $r=\rho(Y/\pi)$. The correction is $\beta(r)\,d\Re Y\wedge d\Im Y$, where the nonnegative density $\beta$ is constant on the shells $j/5000<r<(j+1)/5000$ and vanishes for $r\ge1953/5000$. Each shell is the difference of two concentric regular $224$-gons. The density of each shell is chosen from those source profile cells that could actually meet it. This changes the admissible calibration family in the earlier frozen-family ceiling.

## Two-sided cap and winding

Let $c=48,52,54$ or $56$ and $C=ch$. If a sampled value has absolute value at least $C$, a rotation and antipodality place a positive peak of at least $C$ at zero. For $0\le t\le\pi/2$ write $f_C(t)=\max(C-t,t-\pi/2)$, $\delta=\pi/2-C$. Then
$$
\frac{g(F(t))+g(F(-t))}{2}\ \ge\ g(f_C(t))
$$
at sample angles. Both inputs are at least $C-t$. For $t\ge(C+\pi/2)/2$, let $u=\pi/2-t$. The inputs are at least $u-\delta$ and their sum is at least $-2u$, by the Lipschitz inequality between $t$ and $\pi-t$. If both are in $[-\delta,\delta]$, use linearity of $g$ there. If either exceeds $\delta$, monotonicity and oddness give a nonnegative sum. All four $\delta$ are at most the first knot $8h$.

The first Fourier projection on the peak direction is consequently bounded below by the sampled projection of $g(f_C)$. The even, antiperiodic extension of $f_C$ attains this bound. The checker computes directed lower enclosures in bin units. In particular, a point on a positive-density shell has every fine coordinate strictly below the $54h$ cap in absolute value. The archived inheritance identity then decomposes $\Omega$ into a weighted average of terminal $56$-, $28$- and $14$-point forms. A terminal $56$-block requires a sample at or beyond $52h$, and a terminal $28$-block requires one at or beyond $48h$. Each block of size $n$ occurs with weight $n/N$.

On the boundary $F_k(\gamma(s))=\pi/2-d_{S^1}(s,kh)$. On each interval between consecutive sample angles every $g(F_k(\gamma(s)))$ is affine, since all knots are multiples of $h$. Therefore $Y/\pi$ traverses the regular $224$-gon once with circumradius given by the $c=56$ projection. The checker verifies that the last shell lies inside it, using its inradius and the circumradius of the support polygon.

## Locating a terminal cell on the Fourier plane

The signed endpoints of each leaf cell give lower and upper bounds on the coarse samples. Express all endpoints in units of $h$. Extend the intervals antiperiodically. The verifier propagates the inequalities $L_i\ge L_{i-1}-m$ and $H_i\le H_{i-1}+m$ and their reversals around the cycle, where $m=N/n$. Here propagation means taking the maximum of necessary lower bounds and the minimum of necessary upper bounds. Between nodes $i,i+1$, at fine offset $u=0,\ldots,m-1$, the fine value in units of $h$ lies in
$$
 [\,\max(-56,L_i-u,L_{i+1}-m+u),\
     \min(56,H_i+u,H_{i+1}+m-u)\,].
$$
Monotonicity encloses each $g(F_k)$. For every polygon normal, sum signed interval endpoints with directed cosine errors to obtain a lower and upper bound on the projection of $Y/\pi$. Taking absolute projection bounds and then their maxima encloses $r$. Rotation of a block, antiperiodic reindexing and reflection preserve $\rho$. The test safely allows the individual fine coordinates to vary independently within those intervals. This enlarges the interval of possible shells and makes the norm test more conservative.

## Local norm and averaging

Write $z_i=(\nabla F_i)_1+i(\nabla F_i)_2$ in an oriented orthonormal frame. On a terminal cell the finite quadratic form is $Q_W(z)=z^*(-iW/2)z$, with $|z_i|\le1$. The finite input gives $D+iW/2\succeq0$ with $D=\mathrm{diag}(d_i)$, $\mathrm{tr}D\le U$. For this paragraph $d_i$ have their physical scale. With $\mathrm i=\sqrt{-1}$, put $v_j=g'(F_j)e^{\mathrm i\pi j/n}/n$. The certificate for shell density $b$ is
$$
 Q_W(z)+b|v^*z|^2\le U .
$$
One admissible rate is $(U-\mathrm{tr}D)/(\sum_i |g'(F_i)|/n)^2$, by the triangle inequality. For a sharper rate put $H=D+(U-\mathrm{tr}D)I/n+iW/2$ and $\mu=(U-\mathrm{tr}D)/n$. For $\mu>0$ the rank-one update criterion gives any $b\le1/(v^*H^{-1}v)$. To verify an inverse vector, round a numerical proposal $x$ to a rational vector. If each real and imaginary residual component of $v-Hx$ is bounded by $\epsilon$, then
$$
 v^*H^{-1}v \le \Re(v^*x)+2\max_i|g'(F_i)|\,\epsilon/\mu .
$$
This follows from Cauchy–Schwarz, $\|H^{-1}\|\le1/\mu$ and $\|v\|\le\max|g'|/\sqrt n$. Both the dot product and residual include the trigonometric enclosure. All accepted rates are rounded downward to multiples of $10^{-9}$.

Let $P=N^{-1}\sum_k e^{-ikh}g'(F_k)z_k$. It is the weighted average of the leaf quantities $v^*z$ with unit rotation factors. Under reflection the corresponding reversal of $W$ is compensated by conjugating the test gradients, preserving the squared modulus. Jensen's inequality and the terminal matrix bounds give $\Omega+b|P|^2\le U$. The Jacobian of $Y$ is $|P|^2-|N^{-1}\sum_k e^{ikh}g'(F_k)z_k|^2$. Thus the positive density gives the required upper comass bound. Conjugating all spatial gradients gives the lower bound. On scalar grid facets the affected coordinate differentials vanish almost everywhere, as in the finite source's zero-coordinate extension. Closed interval enclosures include these facets. On each polygon boundary the Jacobian vanishes almost everywhere on the preimage of its line segments, so densities there may be set to zero.

## Action and replay

A bounded planar shell density has a Lipschitz primitive here. For each convex polygon containing the origin one may use $\tfrac12\min(1,r_0^2/\rho(y)^2)(y_1\,dy_2-y_2\,dy_1)$ for its indicator, with $r_0$ in physical units. Differentiating on the sectors gives the indicator times planar area, using the homogeneity of $\rho$. Subtract primitives for nested polygons. Stokes' theorem and the boundary winding give each shell's Euclidean area. If $b_j$ is its density, the result is
$$
 \mathrm{Area}(M)\ge
 \pi^2\left[A+
 \frac{2N\tan(\pi/(2N))}{U\,5000^2}\sum_{j=0}^{1952}(2j+1)b_j\right].
$$
The replay gives $\sum_j(2j+1)10^9 b_j=18103006738917$. It reconstructs all $53{,}100+29{,}410+14{,}562=97{,}072$ terminal rows, checks each reconstructed diagonal array against the finite source hash, and uses $630+47+176=853$ inverse-vector attempts. A failed or numerically unusable inverse proposal falls back to the trace allowance. The final comparison uses Machin's formula and directed Taylor bounds.

Run the standalone checker with Node.js and the supplied finite certificate directory.

~~~sh
node issue163_fourier_caps.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The checker pins its four source files by SHA-256. The bundle's separate command for the finite input theorem is <code>python3 verify_improved.py</code> in that same certificate directory. The new replay reconstructs its inputs and proves the annular extension. The original finite hierarchy supplies its PSD and coverage theorems. The calculation gives no upper bound for the full family of calibrations or for the filling area.
