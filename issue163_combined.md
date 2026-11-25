# A Fourier correction for the signed 224-point calibration

Let $M$ be a compact connected orientable Riemannian surface with one boundary component. Assume its ambient distance restricted to the boundary is the intrinsic distance of a circle of length $2\pi$. In every genus,
$$
 \operatorname{Area}(M)\ge \frac{617166391098385050}{10^{18}}\pi^2
 >6.091188129789057449 .
$$
The signed finite field with 224 antipodal anchor pairs gives $6.091181920033558876$ on its own. The additional term is the average of two polygonal Fourier corrections. This proof takes the transported finite hierarchy in the 25 November bundle as input. [Finite 224-point proof](issue163_dyadic_lift.md) · [Fourier shell construction](issue163_fourier_caps.md)

## Why the corrections coexist

Put $h=\pi/112$ and use the even and odd 112-point grids inside the 224-point grid. Write $\Omega_e,\Omega_o$ for the signed finite forms on these grids. The refined finite form is $(\Omega_e+\Omega_o)/2+\Delta$, where the three endpoint orbits supporting $\Delta$ require some $|F_k|\ge55h$. The angular distance-difference function is $1$-Lipschitz. Every anchor lies within $h/2$ of an anchor of each parity. Thus on the support of $\Delta$, both parity grids have a sample of magnitude at least $54.5h$.

On each parity grid form $Y=(2/112)\sum_j g(F_j)e^{i\pi j/112}$ and use the polygonal radius and shells from the Fourier construction. In units of $h$, the successive breakpoints of the odd function $g$ are
$$
 0,8,16,24,32,36,40,42,44,46,48,50,52,54,56 .
$$
Its slope is $1$ on $[0,8]$, zero on $[8,16]$, $1/2$ on $[16,40]$, and $1$ thereafter. The shell density vanishes once the parity grid has a sample of magnitude at least $54h$, by the two-sided Fourier projection estimate. Consequently both corrections vanish wherever $\Delta$ contributes. Elsewhere each parity form plus its own correction has comass bounded by the common budget, so their average does also. The two boundary actions agree by rotation. This adds one full shell action to the refined finite action.

## Certifying the shell densities

Write $U/Q$ for the finite norm budget, with $U=639413036587531299403539588646$ and $Q=640000000000000000000000000000$. The raw finite action divided by this budget gives the 224-point bound above. The Fourier support lies inside the region controlled by the $14$, $28$ and $56$ levels. At each terminal cell the signed-field replay retains the diagonal actually used in the finite certificate. Congruence by the scalar multipliers gives a diagonal $D$ and a skew matrix $W$ satisfying $D+iW/2\succeq0$. Their entries here are in physical units. For slope vector $v_j=g'(F_j)e^{i\pi j/n}/n$ the checker certifies
$$
 z^*(-iW/2)z+b|v^*z|^2\le U/Q,\qquad |z_j|\le1 .
$$
It uses the better of the triangle estimate and the rank-one criterion with $H=D+(U/Q-\operatorname{tr}D)I/n+iW/2$. A floating-point solve proposes an inverse vector. The replay rounds that vector to rationals, encloses the trigonometric coefficients, and bounds the residual in integer arithmetic. It adjusts the rounding denominator when the vector has a large component. The shell and block averaging argument then applies to each parity grid. [Local norm and winding proof](issue163_fourier_caps.md)

The computation covers 97,072 coarse cells and 1,047 shells of width $1/5000$. For the downward-rounded densities $b_j$ it gives $\sum_j(2j+1)10^{12}b_j=5001933659384$. The common replay also checks all 214,058 terminal cells of the signed finite field and 1,898,400 rooted child profiles at level 224.

## How much can the same shell rule gain?

Freeze the shape $g$, polygon, shell partition and support, profile-to-shell ranges, finite coefficients and witnesses, and common norm budget. Allow arbitrary nonnegative shell densities up to $1/40$ certified by the better of the same two local bounds. The resulting normalized area certificate is at most $6.091188129791$. Its distance from the displayed lower bound is less than $2\cdot10^{-12}$.

Indeed the triangle allowance is explicit. For the other allowance one needs $bvv^*\preceq H$. Any test vector $x$ with $\Re(v^*x)>0$ gives
$$
 b\le \frac{x^*Hx}{\Re(v^*x)^2}.
$$
The checker uses the rational inverse proposal as $x$, obtains $x^*Hx$ exactly and rounds $\Re(v^*x)$ downward. It takes the larger local upper allowance from the two rules. On each shell, every profile retained by the fixed range test imposes its allowance. Taking the minimum over even a subset of these profiles gives an upper bound. Integrating the resulting shell envelope uses upward rational enclosures of $\tan(\pi/224)$ and $\pi^2$. This ceiling concerns density selection within the stated rule. Changing the Fourier shape, the finite field, or the local norm certificate remains possible.

## Replay

Place the four lower-bound JavaScript files together. From the bundle root run

~~~sh
node research/issue163_combined.cjs research/output/improve112_6081_certificate
~~~

In the Git branch, run the same entry point from its root with the absolute path to the supplied certificate directory. It uses Node.js built-ins and checks the five input hashes. The new result is an integer-verified extension of the finite source theorem. The public Lean development covers the earlier Fourier result. [Lean manuscript ledger](https://github.com/lowrank/gromov-filling-lower-bound/blob/main/docs/current-manuscript.md)
