# Testing two continuum retractions at every output radius

Write $e_t=(\cos t,\sin t)$ and $b(t)=\pi/2-d_{S^1}(t,0)$. A profile is an antiperiodic $1$-Lipschitz function of $t$. The independent planar test permits a measurable antiperiodic vector field $u(t)\in\mathbb R^2$ with $|u(t)|\le1$ as its spatial gradient. Actual distance differences in a filling satisfy these constraints. The ceilings below concern certificates using all such tests. An actual filling need not realize a chosen pair $(f,u)$.

## A folded triangle for the gnomonic Fourier coordinate

Take $g(0)=0$, $g'(s)=\sec^3s$, and define

$$
 G(f)=\frac1\pi\int_0^{2\pi}g(f(t))e_t\,dt.
$$

On the hemisphere of unit radius its value is the gnomonic coordinate of radius $R=\sqrt{1-z^2}/z$ at height $z$. For example, on longitude zero $f(t)=\arcsin(\sqrt{1-z^2}\cos t)$, and integration by parts gives $G_1=\sqrt{1-z^2}/z$. Its actual Jacobian relative to hemisphere area is $z^{-3}$. Thus any nonnegative density $\rho$ on the output plane giving independent-gradient comass at most one satisfies $\rho\le z^3$. The optimistic action in a shell of height $dz$ is $2\pi\,dz$ before accounting for other profiles. This normalization also applies to compactly supported densities and truncated targets.

For $\pi/6\le A<\pi/2$, prescribe on $0\le t\le\pi/2$

$$
 f_A(t)=\max\{A-t,\ t-\pi/2\}.
$$

Extend evenly about zero and antiperiodically by $\pi$. At the left endpoint this is the three-wave $b(3t)/3$. At the right limit it is the boundary triangle $b(t)$. Put $t_*=(A+\pi/2)/2$ and $v=(\pi/2-A)/2$. Integration by parts on the two linear pieces gives

$$
 \begin{aligned}
 R(A)&=\frac4\pi\left(\int_0^{t_*}\sec^3(A-t)\sin t\,dt
                    -\int_{t_*}^{\pi/2}\csc^2t\,dt\right)\\
 &=\frac{2}{\pi}\frac{2\sin A-1}{\cos A}.
 \end{aligned}
$$

For the last equality use $\tan v=(1-\sin A)/\cos A$. The radius increases strictly from zero to infinity. Rotations of this family test every point of the output plane.

For nonnegative quadrant test directions $(u_1,u_2)$ of length at most one, reflect their components as for $(\cos t,\sin t)$ in the other quadrants. The resulting Jacobian matrix for $G$ is diagonal, with determinant

$$
 D=\frac{16}{\pi^2}
 \left(\int_0^{\pi/2}\sec^3(f(t))\cos t\,u_1(t)\,dt\right)
 \left(\int_0^{\pi/2}\sec^3(f(t))\sin t\,u_2(t)\,dt\right).
$$

Hence $\rho(R)\le1/D$ there. In height coordinates the action of any such density is at most
$2\pi\int_0^1\min\{1,1/(D z^3)\}\,dz$, where any verified lower bound for $D$ on each band suffices. Rotational symmetry of the tests gives the same bound for angularly dependent densities. Signed densities cannot increase this upper bound on positive oriented action.

The integer replay partitions the folded amplitudes into 512 intervals and uses 96 rational unit-disk directions in each quadrant. On an angular interval $[a,b]$ and amplitude interval $[A_0,A_1]$ the value of $f_A$ lies between $\max(A_0-b,a-\pi/2)$ and $\max(A_1-a,b-\pi/2)$. The smallest possible absolute value bounds $\sec^3(f_A)$ from below. The remaining two integrals of sine and cosine are elementary. Directed height bounds use the displayed radius formula. The resulting ceiling for the whole gnomonic coordinate with any target density is

$$
 \boxed{5.786100794611.}
$$

A second test uses the clipped triangle $f_A=\mathrm{clip}(b,-A,A)$. It has $R(A)=(4/\pi)\tan A$, since $R'(A)=(4/\pi)\sec^3(A)\cos A$. Its weight in the quadrant is $\sec^3A$ until $\pi/2-A$ and $\csc^3 t$ thereafter. Integrating the two moments on 32 angular sectors gives the independent upper bound $6.111821294544$. Neither calculation assumes a proposed density. These tests can also be made with strictly Lipschitz profiles by multiplying by $1-\varepsilon$ and adjusting $A$ to keep the same finite radius. Continuity, strict increase of the unperturbed radius, and bracketing by adjacent amplitudes justify the limit.

All acceptance comparisons use integers, including the unit-vector checks, trigonometric enclosures and directed square roots. The overly optimistic estimate obtained just by testing the hemisphere would be $2\pi$. Run the following from the branch root. [Integer radial replay](issue163_radial_ceiling.cjs)

~~~sh
node issue163_radial_ceiling.cjs
~~~

## A Lorentz-equivariant alternative

The folded profile suggests using more information than $G(f)$. Here is a candidate that includes a second scalar moment. It retracts hemisphere profiles to the correct point. A different family tests it at every point of the disk and also puts its independent-gradient ceiling below $6.15$.

Use the Lorentz product with signs $(-,+,+)$. To the profile assign the de Sitter curve $n(t)=(\tan f(t),\sec f(t)e_t)$. Its oriented Lorentz normal area vector $C(t)$ is characterized by orthogonality to $n,n'$ and time component $\det(n_{\rm sp},n_{\rm sp}')=\sec^2 f$. Explicitly,

$$
 C=\sec^2 f\,(1,\xi),\qquad
 \xi=\sin f\,e_t+\cos f\, f'e_t',\qquad |\xi|\le1.
$$

The vector density $C(t)\,dt$ transforms as a Lorentz vector under any orientation- and time-orientation-preserving boost. This follows from its definition by the ambient volume determinant. In particular its new time component is positive, so the spatial argument of the transformed graph increases. Antipodal symmetry and degree one persist under continuous boosts. A spacelike or null tangent remains spacelike or null, giving $|df_{\rm new}/dt_{\rm new}|\le1$.

Write $V=\int C\,dt$ and $x=V_{\rm sp}/V_0$. Integration by parts in the term $\sec f\, f'e_t'$ gives

$$
 V_0=\int\sec^2 f\,dt,\qquad V_{\rm sp}=2\int g(f)e_t\,dt.
$$

Both integrals range over the full circle. For $\sin f=y\cdot e_t$ one has $\xi=y$ at every $t$, so $x=y$ throughout the open hemisphere. Away from the hemisphere the denominator depends on the entire profile. We need the map only at profiles with timelike $V$, which include all the tests below.

Take the centered five-wave $f(t)=b(5t)/5$. Its fivefold rotational symmetry gives $V=(L,0)$, where $L=\int\sec^2 f$. A boost of velocity $y$ sends this center to disk coordinate $y$. Set $\gamma=(1-|y|^2)^{-1/2}$. If $t'$ and $f'$ here denote the new angle and profile value, the transformed normal gives
$\sec^2(f')\,dt'=\gamma\sec^2(f)(1+y\cdot\xi)\,dt$.
The de Sitter area element in graph coordinates is $\sec^2 f\,dt\,df$. Thus a vertical variation $u(t)$ prescribed at the boosted graph corresponds to $\gamma(1+y\cdot\xi)u(t)$ at the centered graph. This follows by taking the area determinant of the graph tangent and a vertical variation; tangential changes of parametrization drop out.

At the centered graph the derivative of $x$ in a direction $h$ is $(2/L)\int\sec^3 f\, e_t h(t)\,dt$. The projective boost of the disk has derivative at zero with eigenvalues $\gamma^{-2}$ and $\gamma^{-1}$ parallel and perpendicular to $y$. The hemisphere area density at $y$ is $\gamma$ times Euclidean area. The two factors of $\gamma$ from the input variations therefore cancel the boost and target factors. Use the two-component test $u(t)=e_t$ indexed by the original angle. Its evaluation in hemisphere area units is the determinant of

$$
 \frac2L\int\sec^3 f\, e_t e_t^{\mathsf T}(1+y\cdot\xi(t))\,dt .
$$

The term linear in $y$ is zero. Indeed $\xi(t+2\pi/5)$ and $e_{t+2\pi/5}$ are the corresponding rotates of $\xi(t)$ and $e_t$. A rank-three tensor of the standard plane representation has complex rotation weights $\pm1,\pm3$, none divisible by five. The constant term is a scalar matrix by the same rotational invariance. With $a=\pi/10$ the matrix is $kI$, where

$$
 k=\frac{\int_0^a\sec^3 s\,ds}{\int_0^a\sec^2s\,ds}
 =\frac12\left(\sec a+\frac{\mathrm{artanh}(\sin a)}{\tan a}\right).
$$

The gradients in the test are antiperiodic. Strict versions follow by taking $(1-\varepsilon)f$ before boosting. Consequently any target density for this retraction certified by independent planar gradients has total action at most $2\pi/k^2=6.07098103\ldots$. The strict comparison with $6.15$ also follows from $k\ge1+a^2/6$: the increasing weight $\sec^2s$ raises the average of $\sec s$, and $\sec s\ge1+s^2/2$ on the interval. The construction concerns this explicit choice of center and leaves other equivariant choices open.

## Comparing other changes of shape

As an exploratory test, take $g'(s)=\sec^p(s)(1+\beta\cos^2s)$. For $(p,\beta)=(3,1.5)$ a numerical radial integration using just the hemisphere and clipped profiles permits approximately $6.210$. Adding the folded family reduces this numerical upper estimate to approximately $5.255$. For those diagnostics, on each symmetric profile one minimizes the ellipse expression $(2/\pi)^2(\int_0^{\pi/2}g'(f)\sqrt{e^{2u}\cos^2t+e^{-2u}\sin^2t}\,dt)^2$ in $u$, then integrates the reciprocal of the largest tested norm at each output radius. The integer conclusions above use the original $g'(s)=\sec^3s$ and the explicitly stated witnesses.

One further finite construction uses the independent increment coordinates $(1+(F_i-F_{i+1})/h)/2$ on a cube, with $F_n=-F_0$. A multiaffine edge potential gives a closed form depending jointly on all anchors. Its coefficients are multiaffine, so interpolating the vertex witnesses bounds its norm everywhere. A small 11-anchor diagonal SDP gave a numerical objective of about $5.569$. The large-anchor rate and compatibility with the published interior field remain open.
