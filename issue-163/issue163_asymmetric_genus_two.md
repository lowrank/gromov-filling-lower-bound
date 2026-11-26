# An explicit genus-two conformal class with trivial automorphism group

**Result.** On the sphere quadric with ruling coordinates $`(u,v)`$ and real involution $`\tau(u,v)=(\bar v,\bar u)`$, put

~~~math
 \begin{aligned}
 F_0 & =1+(u^3+v^3)/2+u^3v^3,\\[2pt]
 F_1 & =8(1+uv)^3+(u+v)^3+2i^3(u-v)^3+3(1-uv)^3,\\[2pt]
 F_t & =(1-t)F_0+tF_1 .
 \end{aligned}
~~~

Homogenize in each coordinate to bidegree $`(3,3)`$. At $`t=1/401677001`$ the complex curve $`X_t=\{F_t=0\}`$ has **trivial holomorphic automorphism group**. Its two trigonal maps have twelve simple branch values each and are exchanged by $`\tau`$. Every genus-two circle filling with this orientation double has **area above 7.42**. This is a fixed-class statement. The proof first gives an explicit neighborhood of a symmetric class on which the hemisphere bound holds, then locates this asymmetric curve inside the neighborhood. [Exact checks of the constants and branch permutations](issue163_genus_two_check.py)

## A quantitative reference class

On $`X_0`$, the fixed-point-free action $`(u,v)\mapsto(\zeta u,\zeta v)`$, $`\zeta=e^{2\pi i/3}`$, is inverted by $`\tau`$. Its only possible fixed points in the quadric would be the four pairs of zeroes and infinities, all missed by the curve. The unbranched quotient $`Z`$ has genus two. The relative Pu comparison on $`Z/\tau'`$ transfers to $`X_0/\tau`$ by taking the largest of the three densities on each fiber. Every orientation-reversing loop on the base has a closed orientation-reversing lift, since its action on sheets is $`j\mapsto c-j`$. This transfer in fact applies to **any** free holomorphic order-three action inverted by the real involution on a genus-four double. [Covering and hyperelliptic comparison](issue163_cyclic_companions.md)

With $`x=u/v`$, $`V=v^3`$, the invariant equation is $`x^3 V^2+(x^3+1)V/2+1=0`$. Thus the hyperelliptic branch locus of $`Z`$ is $`x^6-14x^3+1=0`$, with real structure $`x\mapsto1/\bar x`$. In the unit disk $`H`$ the three marks are the rotations of $`r=(7-4\sqrt3)^{1/3}`$ through multiples of $`120`$ degrees. Let $`\lambda\,|dx|`$ be the metric obtained by averaging the two sheet densities on this disk. Its area satisfies $`2\int_H\lambda^2\le A`$, with Euclidean area in the integral. Every equator-based loop of odd total winding about the three marks costs at least $`\pi`$. We can average $`\lambda`$ over the three rotations of the marks. The winding constraint is preserved and the squared integral can only decrease.

Let $`\psi_i\,|dx|`$ be the metric whose round northern hemisphere double is branched at the $`i`$-th mark. In the disk coordinate $`z`$ sending that mark to zero by a disk automorphism it equals

~~~math
                  \frac{|dz|}{\sqrt{|z|}(1+|z|)} .
~~~

This follows by setting $`z=w^2`$ in the round length element $`2|dw|/(1+|w|^2)`$. The hemisphere comparison gives an index for which *every* generic northern half of a great circle has projected $`\lambda`$-length at least $`\pi`$. By the rotational symmetry of the averaged density all three indices work. Averaging these semicircles and changing variables gives $`\int_H\lambda\psi_i\ge\pi`$ for each $`i`$. Also $`\int_H\psi_i^2=\pi`$. Consequently

~~~math
 A\ge\frac{2\pi}{D},\qquad
 D=\frac1\pi\int_H\left(\frac{\psi_1+\psi_2+\psi_3}{3}\right)^2
    =1-\frac1{3\pi}\int_H(\psi_1-\psi_2)^2 .
~~~

To estimate the last integral, take the disk $`B_i`$ of pseudohyperbolic radius $`s=2/7`$ about mark $`i`$. The pseudohyperbolic separation between two marks is $`d`$, where

~~~math
      d^2=\frac{3r^2}{1+r^2+r^4},\qquad d\gt131/200 .
~~~

In the centered coordinate, radial integration gives $`\pi^{-1}\int_{B_i}\psi_i^2=2s/(1+s)=4/9`$. In a coordinate centered at mark $`j\ne i`$, $`B_i`$ is a Euclidean disk of radius $`R=s(1-d^2)/(1-d^2s^2)`$ whose closest modulus is $`h=(d-s)/(1-ds)`$. It follows that

~~~math
      \frac1\pi\int_{B_i}\psi_j^2
      \ \le\ \frac{R^2}{h(1+h)^2}\ \lt\ (69/400)^2 .
~~~

For the rational check, $`r\gt83/200`$, the expression for $`d^2`$ increases with $`r`$ on the unit interval, and the last upper bound decreases with $`d`$. The disks $`B_1,B_2`$ are disjoint since $`d\gt2s/(1+s^2)`$. The reverse triangle inequality in $`L^2`$ on each disk now gives

~~~math
    D\lt 1-\tfrac23(2/3-69/400)^2=\frac{1808351}{2160000},
    \qquad A\gt2\pi\,\frac{2160000}{1808351}\gt7.5050 .
~~~

Thus **any** marked conformal distortion at most **1.1944** from this reference class gives $`A\ge2\pi`$. This neighborhood criterion does not require the deformed curve to carry an automorphism.

## An explicit marking

Equip the quadric with the product of the two unit round metrics. Use the four charts obtained by inverting either coordinate as necessary so $`|u|,|v|\le1`$ at the point being estimated. In each trivialization $`F_0=a+b u^3+c v^3+d u^3v^3`$, with coefficients $`1`$ or $`1/2`$ and $`|ad-bc|=3/4`$. The sum of absolute coefficients of $`H_1=F_1-F_0`$ is at most 115 even after inversion, since each linear expression in the formula for $`F_1`$ has coefficient sum two. For $`0\le t\le10^{-4}`$, a point of $`X_t`$ has $`|F_0|\le115t\lt1/10`$. The identity

~~~math
          (c+d u^3)(b+d v^3)=d F_0-(ad-bc)
~~~

shows that each factor has modulus at least $`0.65/2`$. At least one of $`|u|,|v|`$ is at least $`1/2`$, since otherwise the constant term dominates with $`|F_0|\ge1/2-1/8-1/8-1/64\gt1/10`$. Hence one first partial of $`F_0`$ has modulus at least $`3(1/2)^2(0.65/2)`$. The first partials of $`H_1`$ have modulus at most 345, so some first partial of $`F_t`$ exceeds $`1/5`$ in modulus. This proves smoothness. Real points are excluded since both forms are positive on the real sphere in its diagonal chart and at infinity.

Along $`X_t`$ use the normal velocity $`W`$ satisfying $`dF_t(W)=-H_1`$. Normality is with respect to the product round metric, so this velocity is independent of chart and commutes with the real structure. Its flow identifies $`X_0`$ with $`X_t`$. To bound the distortion put

~~~math
  S=\tfrac12\,\mathrm{diag}(1+|u|^2,1+|v|^2),\qquad
  q=S\,\overline{(\partial_u F_t,\partial_v F_t)},\qquad
  W=-H_1 S q/|q|^2 .
~~~

All norms in this formula are Euclidean. The smallest diagonal entry of $`S`$ is at least $`1/2`$, so $`|q|\gt1/10`$. Each first partial of $`F_t`$ has modulus at most 10 and each second partial at most 28 by coefficient sums and bidegree. The Euclidean differential of $`q`$ has norm less than 70 because differentiating $`S`$ costs at most 10, and the Hessian has norm at most 56. Also $`\|dH_1\|\lt500`$. The differential of real Euclidean inversion $`q\mapsto q/|q|^2`$ has norm $`1/|q|^2`$. Consequently

~~~math
           |W|\le1150,\qquad
           \|dW\|\le500\cdot10+115(10+70\cdot100)\lt10^6 .
~~~

These derivative estimates use the displayed formula in a chart as an extension of the velocity off the curve to bound its tangent derivatives. The round product length of a tangent vector is between one and two times its Euclidean length at these chart points. For a transported tangent vector the absolute derivative of its log round length is at most $`2\|dW\|+2|W|\lt2.1\cdot10^6`$. The first term bounds the variation of the vector, and the second bounds the variation of the factors $`2/(1+|u|^2)`$, $`2/(1+|v|^2)`$ along the flow. The ratio of largest to smallest length singular value of the marking is therefore at most $`\exp(4.2\cdot10^6 t)`$. At the stated rational $`t`$ this is below $`1.011`$. Using the larger singular value to dominate lengths transfers the reference area estimate, giving $`A\gt7.5050/1.011\gt7.42`$.

## Checking that the complex curve has no symmetries

The smooth canonical curve on this quadric has exactly its two ruling pencils. Put $`B_u,B_v`$ for their branch sets. The two sets are complex conjugate. The choice $`401677001=1+1000\cdot41\cdot97\cdot101`$ makes $`t`$ equal to one in each of the three indicated residue fields. Thus the branch discriminants of $`F_t`$ reduce to those of $`F_1`$. Taking the binary cubic discriminant in $`v`$ and factoring it gives the following squarefree degree patterns over prime fields.

| Prime | Image of $`i`$ | Irreducible factor degrees for $`B_u`$ |
|---:|---:|---|
| 41 | 32 | 1, 11 |
| 41 | 9 | 5, 7 |
| 97 | 22 | 1, 1, 1, 2, 7 |
| 101 | 91 | 12 |

Each discriminant consequently has twelve distinct finite roots in characteristic zero. The Galois action on $`B_u`$ over $`\mathbb Q(i)`$ is the full symmetric group. Indeed the squarefree reductions supply Frobenius elements of the listed cycle types. The 12-cycle gives transitivity, and the 11-cycle makes a point stabilizer transitive on the other points. The seventh power of the permutation at 97 is a transposition. A doubly transitive group containing a transposition contains them all.

The group of Möbius transformations preserving $`B_u`$ acts faithfully on the twelve points and is normalized by this Galois action. Its order is at most $`12\cdot11\cdot10`$ because three images determine a projectivity. Every nontrivial normal subgroup of $`S_{12}`$ contains $`A_{12}`$, so the Möbius stabilizer is trivial. Conjugation gives the same conclusion for $`B_v`$. If a projectivity carried $`B_u`$ to $`B_v`$, it would be unique, hence Galois-invariant. But at the prime over 41 with $`i\mapsto32`$ the Frobenius cycle types on $`B_u,B_v`$ are respectively $`(1,11)`$ and $`(5,7)`$, with the latter computed using the conjugate embedding $`i\mapsto9`$. They cannot be isomorphic Galois sets. Every holomorphic automorphism of the curve acts on the two pencils. It cannot exchange them, and if it preserves both, the two trivial stabilizers make it the identity in both product coordinates. This proves the assertion. [Ruling argument](issue163_cyclic_companions.md) · [Factorization replay](issue163_genus_two_check.py)
