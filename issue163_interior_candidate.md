# A closed interior correction with boundary action above 6.22

There is a family of closed forms whose boundary action is at least

$$
 2\pi\left(1-\frac{1}{\sqrt{10001}}\right)=6.22035659546\ldots .
$$

For these forms the independent-gradient comass is at most one on the hemisphere profiles, on **every** profile with zero nonlinear Fourier coordinate, and on the folded and clipped families throughout $1\le |G|\le100$. The estimates also give comass below $1.011$ for every profile with $|G|\le1/40000$. The action would require a global comass bound of $1.0114$ to reach $6.15$. A rotating path of profiles forces the global independent-gradient comass above $491$ for every choice of the prescribed cutoffs. The local estimates below still hold. [Rotating-path obstruction](#a-rotating-path-obstruction)

## The primitive and its boundary value

Use $g'(s)=\sec^3s$, $g(0)=0$, $e_t=(\cos t,\sin t)$ and $G(f)=\pi^{-1}\int g(f(t))e_t\,dt$. Integrals cover a full turn, and $\langle\cdot\rangle$ denotes the average over that turn. Use an odd, smoothly bounded increasing extension $g_C$ agreeing with $g$ on $[-C,C]$, for $C<\pi/2$ sufficiently close to $\pi/2$. Use this extension in $G$ on the entire profile space. For a profile with maximum absolute value $M$, rotate its positive maximum to angle zero. The Lipschitz condition gives

$$
 \ReG\ \ge\ \frac4\pi\int_0^{\pi/2}g_C(M-t)\cos t\,dt .
$$

Indeed the projection folds onto $[-\pi/2,\pi/2]$ by antiperiodicity. At $M=C>\pi/4$ the right side equals the expression for $g$ and tends to infinity as $C\uparrow\pi/2$, by the quadratic pole of $g$ near the endpoint. Choose it greater than $105$. Then $|G|\le105$ forces $M<C$, so all calculations there use the original $g$. The boundary triangles have $|G|>105$ and their images wind once.

Put $s=|G|^2$, $x=G/\sqrt{1+s}$ and

$$
 E=\big\langle(\sin f-x\cdot e_t)^2\big\rangle,\qquad D=2(1+s)^3 E.
$$

Both quantities are smooth functions of finitely many Lipschitz moments on a filling. In fact, $E=\langle\sin^2 f\rangle-2x\cdot\langle\sin f\,e_t\rangle+|x|^2/2$. Let $\rho(s)$ equal $(1+s)^{-3/2}$ through radius $100$ and taper smoothly to zero by radius $101$, with $0\le\rho(s)\le(1+s)^{-3/2}$. Define

$$
 b(s)=\frac12\int_0^s\rho(v)\,dv,\qquad c=b(\infty),\qquad
 \alpha_0=\frac{b(s)}s\,\Im(\overline G\,dG).
$$

The smooth quotient at $s=0$ equals $1/2$, and $d\alpha_0=\rho(s)\,dG_1\wedge dG_2$. Choose smooth cutoffs with values in $[0,1]$, depending smoothly on $s$ when expressed through the radius:

- $\kappa=1$ through radius $102$, and $\kappa=0$ at radii at least $104$.
- $\eta=1$ on radii $[1,100]$. It is zero at radii at most $1/8$ and at radii at least $102$.
- $\xi(D)=0$ for $D\le1/32$ and $\xi(D)=1$ for $D\ge1/16$.

Write $\chi=\eta\,\xi(D)$ and $a=1+\kappa((1+4E)^{-2}-1)$. The proposed one-form is

$$
 \boxed{\displaystyle
 \beta=(1-\chi)a\,\alpha_0
       +\chi\left(\frac23\alpha_0+\frac c3\,d\arg G\right).}
$$

The term involving $d\arg G$ is supported away from $G=0$. On the boundary $\beta=c\,d\arg G$, so Lipschitz Stokes gives the action $2\pi c$ on every oriented filling. This is at least the integral of the hemisphere density through radius $100$, giving the stated $6.22035659546\ldots$. The freedom in the transition functions has no effect on the following local conclusions.

## The hemisphere and all centered profiles

On the unit hemisphere $\sin f=x\cdot e_t$ where the untruncated $G$ is in use. Consequently $E=dE=0$, $\chi=0$ near that profile and $d\beta=d\alpha_0$ there. On longitude zero put $z=(1+s)^{-1/2}$ and $q(t)^2=z^2\cos^2t+\sin^2t$. The kernel of $dG$ is $q^{-3}e_t/\pi$. Multiplication by the ellipse matrix $\mathrm{diag}(z,1)$ gives an integrated kernel length $(1/\pi)\int q^{-2}=2/z$. For any unit-disk gradients the nuclear norm of the resulting two-by-two matrix is at most this length. Its determinant is at most a quarter of its squared nuclear norm. Dividing by the ellipse determinant $z$ gives comass at most $z^{-3}$ for $dG_1\wedge dG_2$, canceled by $\rho\le z^3$. Where the truncation changes the profile calculation, $|G|>105$ and $d\beta=0$.

For any profile with $G=0$, its maximum absolute value is less than $\pi/4$. In fact at $M=\pi/4$ pairing $t$ with $\pi/2-t$ in the lower projection above gives a lower bound $4/\pi-1>1/4$, since $g(\pi/4-t)\ge\pi/4-t$ for $0\le t\le\pi/4$. Monotonicity gives the same restriction on $M$ whenever $|G|\le1/4$. For $v=\sin^2 f\le1/2$, the chord upper bound for the convex function $(1-v)^{-3/2}$ gives $\sec^3 f\le1+(4\sqrt2-2)v\le1+4v$. On $G=0$ we have $E=\langle\sin^2 f\rangle$. With the identity ellipse, the independent-gradient comass of $dG_1\wedge dG_2$ is at most $\langle\sec^3 f\rangle^2$. There $\alpha_0=0$ as a covector and $\chi$ vanishes nearby. Thus $d\beta=(1+4E)^{-2}d\alpha_0$ has comass at most one, for every centered profile.

An explicit neighborhood estimate is available. For $R=|G|\le1/40000$ one has $\langle\sin^2 f\rangle\le E+2R$ and $\|dG\|_{\rm op}\le6$ on every independent unit-gradient test. The latter follows by integrating the kernel with $\sec^3 f<3$. From the squared-residual formula, $\|dE\|\le2(1+R)(1+6)<16$, and $\|\alpha_0\|\le3R$. Differentiating $a$ now gives

$$
 \|d\beta\|\le(1+8R)^2+384R<1.011.
$$

## Two entire families away from the center

To see why the residual distinguishes the troublesome profiles, take their third sine-profile harmonic $Y_3=\pi^{-1}\int\sin f(t)e^{3it}\,dt$. Orthogonal projection gives $2E\ge|Y_3|^2$. With the maxima oriented along the real axis, elementary product-to-sum integration gives

| Profile in the first quadrant | $R$ | $Y_3$ |
|---|---:|---:|
| Folded, $f(t)=\max(A-t,t-\pi/2)$ | $\frac2\pi(2\sin A-1)/\cos A$ | $\cos A(1+\sin A)/\pi$ |
| Clipped, $f(t)=\min(A,\pi/2-t)$ | $\frac4\pi\tan A$ | $-4\cos^3 A\sin A/(3\pi)$ |

For example, in the folded row put $m=(A+\pi/2)/2$. On $[0,m]$ the sine profile is $\sin A\cos t-\cos A\sin t$, and afterwards it is $-\cos t$. The quadrant integral against $\cos3t$ gives the table. For the clipped row subtract the pure first harmonic $\cos t$ and integrate only up to $\pi/2-A$.

For the folded row write $u=\sin A\in[1/2,1)$. Then

$$
 (1+R^2)|Y_3|^2
 =\frac{(1+u)^2}{\pi^4}\big[\pi^2(1-u^2)+4(2u-1)^2\big]
 \ge \frac9{\pi^4}>\frac1{16}.
$$

The bracket decreases to four on this interval. For the clipped row with $R\ge1$,

$$
 (1+R^2)^3|Y_3|^2=
 \frac{16}{9\pi^2}\sin^2 A\left(\cos^2 A+\frac{16}{\pi^2}\sin^2 A\right)^3
 \ge\frac{16}{9(\pi^2+16)}>\frac1{16}.
$$

Thus $\chi=1$ with zero derivative on both families at radii $1\le R\le100$. Since $d(d\arg G)=0$ there, $d\beta=\tfrac23d\alpha_0$ on *all* their independent planar gradients. The integer ellipse test gives bounds of $1.454743493396$ and $1.361929744282$ for the full uncorrected hemisphere-weighted norm, respectively. After multiplication by $2/3$ the folded norm is below $0.970$ and the clipped norm below $0.908$.

For each amplitude interval the replay chooses a fixed ellipse $L=\mathrm{diag}(l,1)$ with $l$ a rational lower approximation to the cosine of the left endpoint. The nuclear-norm bound from above gives

$$
 \|\,(1+R^2)^{-3/2}dG_1\wedge dG_2\,\|
 \ \le\ \frac{4z^3}{l}\left(\frac1\pi\int_0^{\pi/2}\sec^3 f(t)\,|Le_t|\,dt\right)^2 .
$$

The amplitude intervals halve in width towards $\pi/2$. On each of 256 angular intervals the replay bounds the full scalar range, the kernel, the angular ellipse length and the upper height by directed integer arithmetic. The intervals cover radius $100$ for both profiles. [Integer norm and obstruction replay](issue163_radial_ceiling.cjs) · [Folded and clipped profile construction](issue163_continuum_tests.md)

## The transition terms

For the proposed forms one must still bound the full derivative. With $\alpha_1=2\alpha_0/3+(c/3)d\arg G$, the terms on $G\ne0$ are

$$
 d\beta=\big((1-\chi)a+\tfrac23\chi\big)d\alpha_0
        +(1-\chi)\,da\wedge\alpha_0
        +d\chi\wedge(\alpha_1-a\alpha_0).
$$

In particular the transition terms are part of the comass problem. The integral over the following cylinder bounds the size of this expression from below, including all three terms.

## A rotating-path obstruction

For a rotation-invariant one-form $\beta$ on profile space, write $P(f)$ for its integral around the rotated copies $f(t-\theta)$ divided by $2\pi$. Suppose $d\beta$ has independent planar-gradient comass at most $K$. Every smooth path $f_\lambda$ of admissible profiles, $0\le\lambda\le1$, obeys

$$
 |P(f_1)-P(f_0)|
 \le 2K\int_0^1\|\partial_\lambda f_\lambda\|_\infty
                         \|\partial_t f_\lambda\|_\infty\,d\lambda .
$$

Indeed pull back $\beta$ to the cylinder $(\lambda,\theta)\mapsto f_\lambda(t-\theta)$. At a fixed point divide its two profile derivatives by $\sqrt2$ times their respective supremum norms. For each $t$ the resulting two components form an admissible vector in the unit disk. The comass bound and bilinearity bound the pullback of $d\beta$ by the integrand on the right. A vanishing derivative gives zero directly. Stokes and integration in $\theta$ give the claim.

Take $R_0=64$, $r=64/\sqrt{4097}$ and $\varepsilon=64^{-3}$. With $u=\cos t$ set

$$
 f_\lambda(t)=\arcsin\bigl((r+\lambda\varepsilon(1-u^2))u\bigr).
$$

These profiles are even and antiperiodic. We have $r+\varepsilon<100/\sqrt{10001}<1$. For example $1-r>1/(65\cdot129)$ while $1-100/\sqrt{10001}<1/20000$. The denominator in the derivative of the arcsine is therefore at least $|\sin t|$. Direct differentiation gives

$$
 \|\partial_\lambda f_\lambda\|_\infty\le
 \varepsilon\sup_t|\cos t\sin t|=\varepsilon/2,
 \qquad
 \|\partial_t f_\lambda\|_\infty\le r+\varepsilon<1 .
$$

In the second estimate the remaining factor is $|r+\lambda\varepsilon(1-3u^2)|\le r+\varepsilon$. All profiles on the cylinder are admissible. The radial coordinate $R_\lambda=|G(f_\lambda)|$ lies in $[64,100)$. To see this, bound the positive-cosine projection integrand between those for hemisphere profiles with sine coordinates $ru$ and $(r+\varepsilon)u$, and use antiperiodicity on the other half. The underlying $g$ is unchanged on this scalar range. Indeed the cutoff criterion above also applies to the untruncated hemisphere of radius $100$ and gives maximum strictly below $C$. The hemisphere identity gives output radius $v/\sqrt{1-v^2}$ at sine amplitude $v$. The angular coordinate along every orbit is $\theta$.

At $\lambda=0$ the residual vanishes, so $P(f_0)=b(64^2)$. At $\lambda=1$, the identity $u(1-u^2)=(\cos t-\cos3t)/4$ gives $Y_3=-\varepsilon/4$. Orthogonality gives $2E\ge|Y_3|^2$ and hence

$$
 D\ge (1+64^2)^3\varepsilon^2/16>1/16.
$$

The prescribed cutoffs give $\chi=1$ there. Thus $P(f_1)=(2b(R_1^2)+c)/3$. Monotonicity of $b$ and its known density through radius $100$ imply

$$
 P(f_1)-P(f_0)\ge \frac{c-b(64^2)}3
 \ge \frac13\left(\frac1{\sqrt{4097}}-\frac1{\sqrt{10001}}\right).
$$

The cylinder inequality bounds this difference above by $K\varepsilon$. In particular

$$
 K\ge \frac{64^3}{3}\left(\frac1{\sqrt{4097}}-\frac1{\sqrt{10001}}\right)
 >\frac{64^3}{3}\left(\frac{100}{6401}-\frac1{100}\right)>491.
$$

This obstruction uses only the values of the primitive on the two end orbits and applies to every smooth interpolation between them. It concerns the independent-gradient norm. Whether a filling realizes the offending test plane is a separate geometric question.

The same calculation gives a quantitative design constraint. If the first orbit still has period $b(64^2)$ and the second uses $(1-\gamma)b(R_1^2)+\gamma c$, with $0\le\gamma\le1$, a target $K\le1.0114$ requires $\gamma\le 1.0114\varepsilon/(c-b(64^2))<0.00069$. The proposed choice was $1/3$. Any new primitive using this model can be tested on these periods before estimating its derivatives on the whole profile space.
