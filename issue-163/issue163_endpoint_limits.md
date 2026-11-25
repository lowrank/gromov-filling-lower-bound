# Which endpoint changes can reach 6.15?

The all-genus lower bound supplied by the signed finite field and its Fourier correction is $6.091188129789057449$. This note proves upper bounds on the area that specific modifications of that construction can certify. The first uses only two outer profiles and one central profile. The second uses the round hemisphere itself. [Lower-bound proof](issue163_combined.md)

| Allowed modifications | Upper bound on the certificate |
|---|---:|
| All 666 signed 224-point endpoint coefficients, fresh diagonal PSD witnesses | $6.137425468261$ |
| The same coefficients, independent planar unit gradients | $6.147258810636$ |
| Any unit-comass closed form agreeing with the scaled published field outside all endpoint bands from 448 onward | $6.145994304998$ |
| The same geometric test, allowing changes in all endpoint bands from 224 onward | $6.168642868649$ |

The first two bounds include the previously published Fourier correction, scaled with the parent field. They allow the signed 112-point field an arbitrary nonnegative overall scaling. They keep its interior coefficient shape fixed. The last two bounds impose no particular coefficient representation or diagonal-witness rule on changes inside the specified bands. The last row leaves room for $6.15$ when changes at 224 and later levels are coordinated.

## Two outer rows and a central row

Let $N=224$ and $p=112$. Normalize the earlier signed field by its certified budget. Write the child field as $\lambda W^0+\sum_o x_o E_o$, with $\lambda\ge0$ and $x_o\in\mathbb R$. Here $W^0$ is half the parent field on each parity grid. The classes $E_o$ have at least one scalar coordinate in an outermost pair of cells at either end. This includes all three increments of the published 224-point lift. In units of $\pi^2$ its finite boundary action is $\lambda\alpha+\sum_o\omega_o x_o$, where

$$
 U=639413036587531299403539588646,\quad
 A=2475080672199852607407123768951328,\quad
 \alpha=\frac{2A}{p^2 U}.
$$

The checker reconstructs $A$ from the integer parent coefficients. For an orbit of triples $(k,a,b)$, its boundary weight $\omega_o$ is the sum of $(N-k)/(2N^2)$ times the number of contributing half-cells. That number is one if $|a-b|=k$ or $|a+b-N+1|=N-k$, and two otherwise. Each distinct triple contributes once. The orbit generators are interchange of the scalar labels, simultaneous complementation, and $(k,a,b)\mapsto(N-k,b,N-1-a)$. [Inherited field and pair weights](issue163_dyadic_lift.md)

Use the two outer rows

$$
 R_A=(0,0,1,2,\ldots,222),\qquad R_B=(1,1,1,1,2,\ldots,221).
$$

All 666 orbits occur on these rows. The central row has labels $112$ for $0\le i\le112$ and $111$ thereafter. On all three rows the scalar cell midpoints satisfy the angular Lipschitz and antipodal inequalities. A slight contraction towards zero makes the inequalities strict while keeping the same open labels. On the central row an integer planar test of unit-disk vectors bounds $`\lambda\lt 50019/50000`$. All its pair determinants are nonnegative. The fixed Fourier term has nonnegative slopes, nonnegative density and positive oriented sine weights, so it can only strengthen this test. On the two outer rows that term vanishes because each parity has a sample in its excluded outer band. Testing two perpendicular unit vectors on one edge and zero elsewhere gives $|x_o+\lambda W^0_{ij}|\le1$. Checking an occurrence for every class yields $|x_o|\le11/10$.

For a rational complex test matrix $Z$ on an outer row let $h_{ij}=\sum_k\Im(\overline{Z_{ik}}Z_{jk})$. Put $`b=\sum_{i\lt j}W^0_{ij}h_{ij}`$ and $`g_o=\sum_{i\lt j}(E_o)_{ij}h_{ij}`$. If a fresh diagonal $D+iW/2\succeq0$ has trace at most one, positivity tested against each column gives

$$
 \lambda b+\sum_o x_o g_o\le m,\qquad m=\max_i\sum_k |Z_{ik}|^2.
$$

Indeed $D_{ii}\ge0$. With only independent planar gradients the inequality holds with $m=\sum_k\max_i|Z_{ik}|^2$, by testing each normalized column separately. Add the inequalities across the supplied matrices, retaining the same symbols for the totals. The finite action divided by $\pi^2$ is at most

$$
 m+\frac{50019}{50000}\max(0,\alpha-b)+\frac{11}{10}\sum_o|\omega_o-g_o|.
$$

The stored integers give finite-only ceilings of $6.137419165867$ for the PSD model and $6.147252508242$ for independent planar gradients. The two PSD matrices use 54 columns in total. The four groups of planar tests use 150 columns. Adding the fixed Fourier correction costs at most $0.0000063\lambda$ in area by the published two-sided shell calculation. The certificates consist of the integer matrices themselves. Their validity is independent of the numerical optimization that suggested them. [Integer replay](issue163_signed_endpoint_ceiling.cjs) · [Rational witnesses](issue163_signed_tests.json.gz) · [Fourier support and action](issue163_combined.md)

## Testing any later endpoint changes on the hemisphere

Write $z$ for height on the unit upper hemisphere and $h=\pi/p$. The actual profiles are $F_i=\arcsin(\sqrt{1-z^2}\cos(\theta-ih))$. If the freedom begins with the two outer scalar cells at level $n_0$, it is confined to the belt $z\le \sin(2\pi/n_0)$. Every later dyadic endpoint band lies inside this belt. A globally valid closed calibration with a boundary action can spend at most the belt's geometric area $2\pi\sin(2\pi/n_0)$ there. On the complementary cap its value is fixed. This test applies even to methods which estimate comass only on genuine filling tangents.

At the north pole approach along longitude $\pi/448$. The limiting parent labels are those of the central row above, and the actual unit-gradient determinants tend to $\sin((j-i)\pi/224)$. The positive Fourier term and the vanishing endpoint changes allow the same $`\lambda\lt 50019/50000`$, this time directly on the hemisphere. Each published 224-point increment and the fixed Fourier term is nonnegative on the hemisphere. Their combined action on any cap is at most their total action, below $0.0000063$ per unit of scale. The baseline cap actions of the two 112-point parity grids agree by rotation.

| First free level $n_0$ | Upper bound on baseline cap action | Upper bound on belt area | Total at $\lambda=1$ |
|---:|---:|---:|---:|
| 224 | $5.990140487515$ | $0.176219825354$ | $6.166366612869$ |
| 448 | $6.055568307662$ | $0.088118578985$ | $6.143693186647$ |

For the quadrature write $r=\cos(2\pi/n_0)$ and $X(t)=p/2+\arcsin(r\cos t)/h$. In scalar grid units, the image of the cap under two coordinates at separation $k$ has horizontal position $X(t)$ and vertical range $[X(t+kh),X(t-kh)]$, $0\le t\le\pi$. Indeed projecting the cap to the equatorial plane gives the disk of radius $r$. The two linear projections have positive Jacobian $\sin(kh)$, and applying the increasing scalar arcsines preserves orientation and multiplicity one. Each separation occurs $p-k$ times. The physical area element of a scalar box in these coordinates is $`h^2\,dx\,dy`$.

Divide $[0,\pi]$ into 114,688 equal intervals. The mesh contains the turning points of all three translated boundary curves. At each mesh point the replay encloses $X$ on a $10^{-9}$ grid by verifying $\cos(hX)=-r\cos t$ with directed Taylor bounds. Each vertical slice lies in its outer bounding rectangle and contains the common inner rectangle between both endpoint ranges. Integrate the positive part of the upward-rounded coefficient on the outer rectangle and its negative part on the inner one. Prefix sums give the exact integral of the step functions on each rectangle. Summing these upper bounds and adding the belt and the published corrections gives the last two ceilings in the first table. [Cap quadrature and pole test](issue163_hemisphere_cap.cjs)

## Reproduction

From the <code>issue-163</code> directory, with Node.js and the supplied inputs, run

~~~sh
node issue163_signed_endpoint_ceiling.cjs issue163_inputs
node issue163_hemisphere_cap.cjs issue163_inputs
~~~

Both computations check SHA-256 hashes of the coefficient and orbit archives. The cap checker needs no witness file or solver. New interior coefficients, or geometric constraints coupling actual gradients to their distance profiles, fall outside the first two ceilings. The geometric genus-reduction estimate supplies a different sufficient condition for exceeding $6.15$. [Genus reduction](issue163_genus_reduction.md)
