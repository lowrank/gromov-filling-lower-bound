# Which line tests are available on every genus-two filling?

The orientation double $`(X,\tau)`$ of the antipodal quotient of a genus-two filling has genus four and no real points. Some such doubles have no equivariant holomorphic degree-three map to the antipodal sphere. Every one has an equivariant degree-five map. For any chosen quintic map, checking the unweighted line estimate requires at most 29 regions in a projective plane. The choice of map and the resulting sheet permutations still matter.

## A curve where both cubic line estimates give exactly one third

Consider the smooth compactification

~~~math
  y^3=\frac{z^3-1}{z^3+1},\qquad
  \tau(z,y)=(-1/\bar z,-1/\bar y).
~~~

The zeros in the $`z`$-sphere are three equatorial vectors spaced $`120`$ degrees apart, with poles at their antipodes. Their vector sum is zero. Every open hemisphere bounded by a generic great circle contains either one or two zeros, and contains the antipodes of the remaining zeros. Its signed number of zeros minus poles is $`-1`$ or $`1`$. Continuation around the full circle therefore permutes all three cubic roots. That permutation is the square of the projective line permutation, which must itself be a three-cycle. Solving instead for $`z^3=(1+y^3)/(1-y^3)`$ interchanges the two equatorial triples, so the same proof works for the other projection. The unweighted line bound is exactly $`2\pi/3`$ for each. The cyclic companion argument gives the hemisphere bound on this very curve. [Proof using figure eights](issue163_cyclic_companions.md)

## What changes with ordinary branching

On a nonregular three-sheeted cover a meridian can be a transposition. In the figure eight with one-sided petal $`o`$ and disk petal $`e`$, consider permutations

~~~math
                         o=(123),\qquad e=(12).
~~~

To certify the arithmetic mean of the three sheet lengths of the figure eight by the previous argument, one would need three closed odd walks jointly using each lifted edge at most once. Each walk must use an odd edge, so each must use exactly one. The endpoints of that edge would then have to be connected by even edges alone. The even edges have sheet orbits $`\{1,2\}`$ and $`\{3\}`$, but two odd edges cross between them. Such a decomposition is impossible.

These permutations occur on actual genus-four doubles. Present the fundamental group of the projective plane punctured at six points by a crosscap loop $`c`$ and meridians $`t_j`$ with $`c^2t_1\cdots t_6=1`$. Use right-to-left permutation composition and take

~~~math
 c=(123),\qquad
 (t_1,t_2,t_3,t_4,t_5,t_6)=
 ((12),(23),(12),(12),(23),(23)).
~~~

The product relation holds and the action is transitive. Complete the covering at the six transpositions by simple branching. Its Euler characteristic is $`3-6=-3`$, and its orientation double has genus four. Pulling back the conformal structure off the branch values and using a square-root coordinate at each ramification point gives the equivariant holomorphic cover. A petal around the first mark based at the crosscap loop gives the indicated example. This locates the obstruction to the *three-walk decomposition of one figure eight* on the filling side.

## An explicit smooth double with no equivariant cubic

On the sphere quadric in real projective three-space, take the complex curve cut out by

~~~math
 \begin{aligned}
     x_1^2+x_2^2+x_3^2 &=x_0^2,\\[2pt]
     8x_0^3+x_1^3+2x_2^3+3x_3^3&=0 .
 \end{aligned}
~~~

It has no real points because on the unit sphere the absolute value of the last three cubic terms is at most $`3\sum|x_j|^3\le3`$. It is smooth over the complex numbers. Indeed if the gradients were proportional, the nonzero spatial coordinates would be $`a/b_j`$ with $`(b_1,b_2,b_3)=(1,2,3)`$ and a common $`a\ne0`$. For $`x_0=0`$ their squares cannot sum to zero. Otherwise $`a=-8x_0`$, and the quadric would give $`1=64\sum_{j:x_j\ne0}b_j^{-2}`$, which is impossible even for a single summand. The smooth divisor of type $`(3,3)`$ is connected and has genus four by adjunction.

In affine ruling coordinates use

~~~math
  (x_0,x_1,x_2,x_3)=(1+uv,\ u+v,\ i(u-v),\ 1-uv).
~~~

Conjugation takes $`(u,v)`$ to $`(\bar v,\bar u)`$. The rulings give the only two degree-three pencils by the canonical quadric argument, so neither descends. Moreover each has twelve simple branch values. For projection to $`u`$, take the binary cubic discriminant in $`v`$. Its reduction modulo 17 with $`i\mapsto4`$ is

~~~math
 \begin{aligned}
 D(u)={}&7u^{12}-7u^{10}-5u^9-8u^8+3u^7+3u^6\\[2pt]
        &+2u^5-6u^4+u^3-7u^2-5 .
 \end{aligned}
~~~

It has degree twelve and $`\gcd(D,D')=1`$ in $`\mathbb F_{17}[u]`$. Thus the characteristic-zero discriminant has twelve distinct finite zeros. By conjugation the same holds for the other ruling. This example exhibits both obstructions to applying the cyclic cubic theorem directly. The theorem does give the bound for simply branched exchanged rulings sufficiently near the following explicit curve. [Exact arithmetic check](issue163_genus_two_check.py) · [Real canonical quadrics, Gross and Harris, section 8](https://www.numdam.org/item/10.24033/asens.1401/)

Specifically, on the same quadric let $`F_0=1+(u^3+v^3)/2+u^3v^3`$ and $`F_1=8x_0^3+x_1^3+2x_2^3+3x_3^3`$ in the displayed coordinates, homogenizing both to bidegree $`(3,3)`$. For all sufficiently small positive $`t`$ both projections of $`(1-t)F_0+tF_1=0`$ have twelve simple branch values. Indeed the leading coefficient of the discriminant and its resultant with its derivative are polynomials in $`t`$, nonzero at $`t=1`$. At $`t=1/401677001`$ an explicit marking gives **area above 7.42** and a Galois calculation shows that the complex curve has trivial automorphism group. The computation of simple branching at $`t=1`$ by itself gives no comparable area estimate for that endpoint. [Area proof, marking and symmetry check](issue163_asymmetric_genus_two.md)

## A quintic test available on every double

**Existence.** Every genus-four Riemann surface with a fixed-point-free antiholomorphic involution admits a holomorphic map of degree five carrying the involution to antipodes. A quaternionic line bundle means a complex line bundle with an antilinear lift of the involution whose square is minus the identity. Such a smooth bundle of degree five exists since $`5+(4-1)`$ is even. Averaging a Dolbeault operator with its transported conjugate gives an invariant holomorphic structure since integrability is automatic on a curve. Quaternionic bundles form real components of the fixed Picard variety. Locally the fixed locus has real dimension four and is maximally totally real, as is seen on the tangent space $`H^1(X,\mathcal O_X)`$. The quaternionic type persists locally, or follows here from the impossibility of a real line bundle of odd degree on an ovalless curve. [Biswas, Huisman and Hurtubise, Propositions 4.2–4.3](https://arxiv.org/pdf/0901.3071) · [Gross and Harris, sections 1–2](https://www.numdam.org/item/10.24033/asens.1401/)

For any such holomorphic $`L`$, the bundle $`K_X L^{-1}`$ is quaternionic of degree one. Its space of sections has even complex dimension and at most one section up to scale (two would give a map of degree at most one). Thus $`h^0(L)=2`$ by Riemann–Roch. A basepoint at $`p`$ would give $`h^0(L(-p))=2`$, so $`K_X L^{-1}(p)`$ of degree two has a section by Riemann–Roch. Such $`L`$ lie in the image of $`(p,E)\mapsto K_X(p-E)`$ for $`E`$ an effective divisor of degree two. This image is a closed complex analytic subset of dimension at most three in the four-dimensional Picard variety. It cannot contain an open set of the maximally totally real fixed locus, by the identity theorem in real local coordinates. Choose a basepoint-free $`L`$ there. Its two sections $`s,Js`$ give a map of degree five, and $`J^2=-1`$ gives the antipodal real structure on their projective line.

**Finite test.** Riemann–Hurwitz gives total ramification $`2g_X-2+2\cdot5=16`$. In the projective quotient there are at most eight branch values. In the dual projective plane, draw the line of all test lines through each such value. The complement has at most $`1+\binom82=29`$ regions (after the first line, the next line adds at most as many regions as its number of intersections). On each region the sheet permutation is constant up to conjugacy and reversal. Its probability for a random test line is the round projective area of the region divided by $`2\pi`$.

Let $`p_\alpha`$ be the probability of cycle type $`\alpha`$. The previous projective-line estimate sums $`1/k`$ over odd cycles of length $`k`$. After subtracting one, the seven possible coefficients in degree five are

| Cycle lengths | $`1,1,1,1,1`$ | $`2,1,1,1`$ | $`2,2,1`$ | $`3,1,1`$ | $`3,2`$ | $`4,1`$ | $`5`$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| Coefficient | $`4`$ | $`2`$ | $`0`$ | $`4/3`$ | $`-2/3`$ | $`0`$ | $`-4/5`$ |

The line estimate would prove unrestricted genus two if each ovalless genus-four double admitted a quintic pencil satisfying

~~~math
 4p_{1,1,1,1,1}+2p_{2,1,1,1}+\tfrac43p_{3,1,1}
 \ \ge\ \tfrac23p_{3,2}+\tfrac45p_5 \,.
~~~

The existence proof supplies the map. Control of these probabilities through the choice of pencil on a *given* Riemann surface remains open. [Line-lift inequality](issue163_projective_lines.md)

## The same eight branch values can give opposite results

Put eight distinct projective points in a round disk of radius $`\varepsilon`$ with $`\sin\varepsilon\le1/20`$. In the punctured projective plane use the relation $`c^2t_1\cdots t_8=1`$ with $`c`$ the core of the complementary Möbius band. The following two transitive monodromies both have group $`S_5`$.

| Cover | $`c`$ | Eight meridians in order |
|---|---|---|
| First | identity | $`(12),(12),(23),(23),(34),(34),(45),(45)`$ |
| Second | $`(12345)`$ | $`(13),(15),(12),(14),(12),(12),(34),(34)`$ |

Completing the simple branch points gives Euler characteristic $`5-8=-3`$ in each case, hence an actual genus-four orientation double and an equivariant quintic. A round projective line misses the disk with probability at least $`19/20`$. Every such line represents its one-sided core up to orientation in the complementary Möbius band, so has the indicated type of $`c`$. On the exceptional lines the sum of reciprocals of odd cycle lengths lies between $`1/5`$ and $`5`$. The first cover's line estimate is therefore at least $`2\pi\cdot119/25`$, while the second cover's line estimate is at most $`2\pi\cdot11/25`$. These are bounds on the certificates. The two covers use exactly the same branch positions. Their very different results show why a test for unrestricted genus two must keep track of how the sheets are glued. [Permutation check](issue163_genus_two_check.py)
