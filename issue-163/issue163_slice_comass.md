# A comass comparison from the changes along a distance level

The published planar near-maximizer gives two transverse derivatives of about **0.159** and **1.000**. In an actual filling their signed integrals must agree on every sufficiently high level of the anchor coordinate. Two terms using this conservation law reduce the raw comass to **at most 0.9909 on an open neighborhood of every grid anchor profile**, including every choice of the gradients there. The width and the obstruction farther inside the same scalar cell are explicit. The raw threshold for a global area bound of 6.15 is **0.9912013728…**. The unrestricted all-genus area bound on this branch is still **6.095910645232136335…**. [Original planar test](issue163_short_routes.md) · [Integer checker](issue163_slice_comass.cjs)

## What a level has to carry

Work on a compact connected orientable isometric filling of the circle of circumference $`2\pi`$. Take the prescribed triangular boundary values $`P_j(\gamma(s))=\pi/2-d_{S^1}(s,jh)`$ at spacing $`h=\pi/112`$. The coordinates are 1-Lipschitz both in position and in boundary label, with $`P_{j+112}=-P_j`$. The antipodal distance differences are one such choice. Use the orientation for which $`s`$ increases around the boundary. Write $`u=\pi/2-P_0`$. Its boundary level $`u=r`$ meets the circle at $`-r`$ and $`r`$. For Borel $`S\subset(0,\pi)`$ and $`1\le j\le111`$,

~~~math
 \int_{\{u\in S\}}dP_0\wedge dP_j
 =\int_S \big(P_j(\gamma(r))-P_j(\gamma(-r))\big)\,dr
 =2\int_S\min(r,\pi-r,jh,\pi-jh)\,dr .
~~~

For a smooth weight on $`u`$, this follows by applying Stokes to a primitive times $`dP_j`$ and integrating by parts on the boundary circle. Approximation gives the identity for Borel sets through equality of finite signed measures. The same argument works for Lipschitz coordinates. It uses no regularity of their individual level sets. [Lipschitz Stokes in the finite construction](issue163_midpoint.md#the-closed-correction-and-its-norm)

In particular when $`0\lt r\lt 7h`$, coordinates 7 and 83 both have boundary increment $`2r`$. Put $`G=P_{83}-P_7`$. For all Borel sets $`S\subset(0,7h)`$ and $`T\subset\mathbb R`$,

~~~math
 \int_{\{u\in S,\ G\in T\}}dP_0\wedge dG=0 .
~~~

Indeed the two boundary values of $`G`$ are identical. Apply the previous argument with any smooth primitive $`K(G)`$ and use $`dK(G)=K'(G)dG`$. Product tests determine the signed measure in the two scalar variables. Thus positive and negative evaluations have to balance even within a prescribed range of $`G`$.

At a differentiability point with $`dP_0\ne0`$ write $`t_j=\det(\nabla P_0,\nabla P_j)/|\nabla P_0|`$. These are the oriented derivatives along the level. Normalize the directions of the published neighboring planar witness to unit length. The checker gives $`t_7\lt 0.160`$ and $`t_{83}\gt 0.999`$ there. Let $`E`$ consist of the points where gradients 0, 7 and 83 all lie within $`1/200`$ of those unit vectors after one common orientation-preserving rotation. Normalizing the first perturbed vector changes its distance from the first reference direction to at most $`2/200`$. Hence $`t_7\lt 9/50`$ and $`t_{83}-t_7\gt 4/5`$ on $`E`$.

Use the measure $`d\mu=|\nabla P_0|\,dA`$. For any of the two-variable sets above, the share of $`\mu`$ in $`E`$ is at most $`5/7`$, since $`t_{83}-t_7\ge-2`$ everywhere. There is also an **absolute** size requirement. Write $`X,Y`$ for the masses inside and outside $`E`$ over $`u\in S`$, allowing all values of $`G`$. Then $`4X/5\le2Y`$ and $`2\int_S r\,dr\le9X/50+Y`$. It follows that $`Y\ge(20/29)\int_S2r\,dr`$.

Apply this result to all 224 signed anchors with $`S=(0,7h)`$. Any two contributing anchors at a point have angular separation less than $`14h`$ since $`P_a+P_b\le\pi-d_{S^1}(a,b)`$ by angular Lipschitz continuity and antipodality. They lie in one arc of length less than $`14h`$. Indeed, lifting about any one of them puts all lifts within $`14h`$ on each side, and $`28h\lt \pi`$ makes the separation of the extreme lifts their circular distance. There are at most 14 contributing grid labels, and each $`|\nabla P_a|\le1`$. Consequently the area of the set where at least one contributing anchor lies outside its rotated copy of $`E`$ is at least

~~~math
 \frac{224}{14}\frac{20}{29}(7h)^2=\frac{5\pi^2}{116}>0.425413 .
~~~

Other gradient configurations can still have high comass on this area. The estimate limits the occupation of this specific near-maximizer.

## Two corrections and their range

For each signed anchor $`a`$ (indices are modulo 224) set $`u_a=\pi/2-P_a`$, $`s_{a,j}=P_{a+j}-(\pi/2-jh)`$ and

~~~math
 G_a=\frac{17}{1000}(s_{a,2}-s_{a,110})
     +\frac{2}{1000}(s_{a,4}-s_{a,108}).
~~~

Let $`\chi`$ be the indicator of $`(1/2,3/2)`$. Let $`S(y)`$ equal one up to $`-1/2`$, minus one from $`1/2`$ onward and interpolate linearly between. The correction to the **raw** bisected-gap form is

~~~math
 \eta=\sum_a \chi(u_a/h)\,dP_a\wedge
       d\big[S(P_{a+56}/h)G_a\big].
~~~

For a smooth cutoff the primitive is $`-\sum_a\chi(u_a/h)S(P_{a+56}/h)G_a\,dP_a`$. Wherever the cutoff is nonzero on the external boundary, the four $`s_{a,j}`$ have the same value, the signed displacement from $`a`$. The primitive thus vanishes on that boundary. Approximate the indicator by bounded smooth cutoffs supported in $`0\lt u_a/h\lt 2`$. Their derivatives wedge with $`dP_a`$ and drop out. Dominated convergence applies since $`dP_a=0`$ almost everywhere on the preimages of the two jump heights. The limiting form is also exact, by writing $`\chi(u_a/h)dP_a=d\Psi(P_a)`$ for a Lipschitz primitive $`\Psi`$. Adding $`\eta`$ preserves the integrated raw action $`UB`$, where $`U=0.9999999`$ and $`B=6.095889052386098292\ldots`$. The sign from the middle anchor distinguishes the two sides of the boundary vertex.

Consider the grid anchor at boundary coordinate $`-h`$. Write

~~~math
 P_j/h=55-j+e_j,\qquad 0\le j\le111.
~~~

On the entire open set $`\max_j|e_j|\lt 1/2`$, only $`a=0,-2`$ have nonzero cutoffs. Both cutoffs equal one, and the middle-anchor signs are respectively plus and minus. With $`b_i`$ the standard coordinate covectors and $`c_2=17/1000`$, $`c_4=2/1000`$, $`c_{108}=-2/1000`$, $`c_{110}=-17/1000`$, the added matrix is the same throughout this set,

~~~math
 \sum_{j\in\{2,4,108,110\}}c_j
 \big(b_0\wedge b_j+b_{110-j}\wedge b_{110}\big).
~~~

The neighborhood includes the intrinsic metric ball of radius $`h/2`$ about the boundary anchor by spatial Lipschitz continuity. Each such ball has area at least $`(h/2)^2`$. To see this, apply the boundary-increment identity with $`P_0=\pi/2-d_M(x,a)`$ and the coordinate at angular distance $`\pi/2`$. The integral over the ball is $`(h/2)^2`$, and the wedge has absolute density at most one. These 224 metric balls are disjoint by the isometric boundary condition.

Angular Lipschitz continuity gives $`e_0\le\cdots\le e_{111}`$, and $`e_{111}\ge0`$ by the amplitude bound. When the offsets are nonzero, let $`k`$ count the negative entries. For $`1\le k\le110`$, exactly one signed label exceeds $`55h`$. All the old gap tents vanish, and the scalar bins are exactly $`111-j-\mathbf 1_{\{j\lt k\}}`$. For $`k=0`$ the gap between $`-h`$ and zero is active. Its two extreme coordinates in the old gap frame, in units of $`h`$, are $`-1/2+e_0`$ and $`-1/2+e_{111}`$. Both are negative. Their sum determines which of the two old child matrices applies, with the switch at $`-1/2`$. Reflection about $`-h`$ interchanges $`k`$ and $`111-k`$. It fixes index 111 and takes each other coordinate $`P_j`$ to $`-P_{110-j}`$. It reverses the sign of the two-form. This accounts also for the other active corner. On a scalar wall $`e_j=0`$, $`dP_j=0`$ almost everywhere on its preimage. Either adjacent assignment gives the same pulled-back scalar terms, and the vanishing tent on a switch has zero derivative almost everywhere there. Equivalently ties can be assigned to the nonnegative offsets. [Old corner matrices and ties](issue163_midpoint.md)

The replay uses 17 positive diagonal shapes. It interpolates the shapes in $`k`$, rounds the final entries down under the target trace, and verifies an integer Gram residual for each of the 57 matrices up to reflection. The off-diagonal residual is bounded by the sum of the absolute real and imaginary parts in each row. The checker also reconstructs the reflected free matrices from the original integer inputs. This proves the following pointwise budgets for all disk-valued gradients, in every rotated neighborhood.

| Region | Raw comass upper bound | Raw budget needed globally for 6.15 |
|---|---:|---:|
| Whole neighborhood of any grid anchor | 0.990900 | 0.9912013728… |
| Published near-maximizer's scalar cell within the neighborhood | 0.989360 | 0.9912013728… |

## What still obstructs a global comparison?

A correction using only $`dP_0\wedge d(P_{83}-P_7)`$ is too weak in the published cell, whatever its scalar coefficient. Copy gradient 7 onto gradient 83 in the old rational planar test. The correction vanishes and the raw value still exceeds **0.994961123**. The two comparisons above exploit several prescribed increments and both active anchors.

The same scalar cell has profiles farther from the vertex where the correction becomes arbitrarily small. For $`L\ge10^4`$ take

~~~math
 e_0=-0.60,\qquad e_{110}=0.61,\qquad e_{111}=0.62,\qquad
 e_j=(2j-55)/L\quad(1\le j\le109).
~~~

The offsets increase strictly, their successive differences are less than two, and $`0\lt e_0+e_{111}\lt 2`$, giving strict angular inequalities including the wrap. The scalar bins are exactly the same as in the published test. Only the central anchor $`a=-1`$ has an active cutoff, and the old corner tents vanish. For this anchor $`P_{55}/h=55/L`$ and $`G_{-1}/h=-4.088/L`$. Since $`|S'|=2`$ there and the sum of the absolute coefficients of $`G_a`$ is $`0.038`$, the added comass is at most $`(2\cdot55\cdot0.038+2\cdot4.088)/L=12.356/L`$. The same witness directions therefore give a limiting raw value above **0.999701031**. Uniform rescaling of this particular closed form gives at most **6.097712**. Such strict tests can be approached on small patches of genuine fillings. They identify the remaining problem even with a central distance level active. The other coordinates and their gradients must be controlled across those fillings. [Local realization on actual fillings](issue163_short_routes.md) · [An all-genus estimate on the area and directional loss of a metric collar](issue163_metric_collars.md)

Run the following from the repository's <code>issue-163</code> directory.

~~~sh
node issue163_slice_comass.cjs issue163_inputs
~~~

The new identities are analytic, and the local matrices and numerical thresholds have an integer replay. The repository's Lean development covers the earlier Fourier theorem.
