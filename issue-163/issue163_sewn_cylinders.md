# Shortcuts across the edges of a Jenkins–Strebel cylinder

Every genus-two filling has a conformal cylinder presentation with at most nine paired edges on one end. The round metric that saturates the Möbius band comparison violates a shortest-distance constraint at these edges. At cylinder half-height $`T=1.3`$, the shortcut saves more than **0.34** in every genus-two diagram. There is also a family where the two separate area tests are each below **5.63** at that height, while imposing both gives **area above 6.57**. For this family the bound exceeds **6.23 at every height** and exceeds $`2\pi`$ throughout $`0\lt T\le1.6`$. The cylinder description and the shortcut apply to unrestricted genus two. The value 6.23 requires four transverse strips. [Rational checks](issue163_sewn_cylinder_check.py) · [Earlier band comparison](issue163_conformal_program.md#a-curve-family-test-in-every-genus)

## One cylinder contains the conformal data

Identify antipodes on the boundary of an orientable filling of genus $`g\ge1`$ and call the quotient $`N`$. Its orientation double $`X`$ has genus $`2g`$ and deck involution $`\tau`$. Every orientation-reversing loop on $`N`$ costs at least $`\pi`$. The lift of the glued seam is a separating simple closed curve $`c`$ cutting $`X`$ into two genus-$`g`$ sides. [Quotient distance argument](issue163_projective_lines.md#what-a-line-on-the-quotient-measures)

Apply the Jenkins–Strebel theorem to $`c`$ in its unoriented isotopy class. The unique differential with prescribed cylinder height has one open Euclidean cylinder and its complement is the critical graph. The antiholomorphic involution preserves this normalized differential after conjugation by uniqueness. Rescale so the cylinder circumference is $`2\pi`$. In flat coordinates the involution acts by

~~~math
   (\theta,u)\longmapsto(\theta+\pi,-u),\qquad
   \theta\in\mathbb R/(2\pi\mathbb Z),\quad -T\le u\le T .
~~~

Indeed it preserves the orientation of the lifted seam, exchanges its sides and is fixed-point-free. The two ends have separate critical graphs because the core is separating. Along the upper circle the two occurrences of each edge are glued by an arclength reflection $`\theta\mapsto m+m'-\theta`$, where $`m,m'`$ are the interval midpoints. The lower gluing is its translate by $`\pi`$. All the edges on one end form a connected spine of the genus-$`g`$ side. If the spine has $`V`$ vertices and $`E`$ edges then $`V-E=1-2g`$. Every vertex has valence at least three after regular points are suppressed. Hence $`E\le6g-3`$. The graph has zero area for any smooth physical metric. The cylinder core represents the seam class and its conformal location may differ from the physical seam. [Arana-Herrera and Calderon, Theorems 2.1–2.2 and the critical graph construction](https://arxiv.org/abs/2305.01717)

These diagrams admit actual fillings. Cut along the middle circle and use a smooth radial metric of length density $`b(u)\ge1`$ in $`0\le u\le T/2`$, with $`b=1`$ near zero and $`\int_0^{T/2}b(u)\,du\gt\pi/2`$. Extend it smoothly over the interior. A path confined to the collar costs at least its circular displacement. A boundary-to-boundary path leaving the collar costs more than $`\pi`$. The middle circle therefore has its prescribed intrinsic boundary distances.

## The missing short loop

On the cylinder take the conformal length density $`\sigma(u)=1/\cosh u`$. The orientation double of this round band has upper boundary points $`P(a)=(s\cos a,s\sin a,H)`$ on the unit sphere, where $`H=\tanh T`$ and $`s=1/\cosh T`$. Suppose $`a,b`$ are paired in the interior of an edge. Their spherical distance is

~~~math
     d=2\arcsin\!\left(s\,|\sin((a-b)/2)|\right).
~~~

The short great-circle arc between $`P(a)`$ and $`P(b)`$ lies in the omitted northern cap. Continuing on the same circle from $`P(a)`$ away from that cap to $`-P(b)`$ gives an arc of length $`\pi-d`$ in the closed band. Indeed the portions of that great circle in the two open caps are antipodal arcs of length $`d`$. The upper edge identification makes this path join a point of $`X`$ to its deck mate. Its projection to $`N`$ is an orientation-reversing loop. In the bordered model with round equatorial arclength it is an actual shortcut between boundary antipodes, obtained by cutting this loop at the equator.

The edge lengths sum to $`\pi`$. Choose an edge of length $`l\ge\pi/E`$. Its disjoint occurrences have midpoint distance $`D\in[l,\pi]`$ on the circle. Varying the paired point over the edge varies the signed angular difference over an interval of radius $`l`$ about a representative of $`D`$. Thus angular separations approach at least $`\min(\pi,2l)`$. In particular the supremum of the length saved satisfies

~~~math
 \sup d\ \ge\ 2\arcsin\!\left(\frac{\sin(\pi/(6g-3))}{\cosh T}\right).
~~~

The right side exceeds 0.34 at $`g=2,\ T=1.3`$. This tests the optimizer of the **band-only** relaxation. The independent Fourier calibration has different variables.

The same loop gives a strict area improvement over $`2\pi H`$ in **each fixed conformal class** with this cylinder. Write the physical length factor as $`r`$ relative to the round metric. The band path average gives $`A\ge2\pi H+\int(r-1)^2\,dA_{\rm rd}`$. Choose an interior paired point with $`d\gt0`$. Its loop avoids the graph vertices and is embedded, since an arc shorter than a great semicircle misses its antipodal arc. Round length is continuous across the interior edge. Smooth the corner and take a narrow Möbius tube about the loop. Parametrize the core by $`t\bmod 2\pi`$ with transverse coordinate $`v`$ changing sign after one circuit. The curves

~~~math
       v(t)=p\cos(t/2)+q\sin(t/2)
~~~

for $`(p,q)`$ uniform in a sufficiently small disk all have round length at most $`\pi-d/2`$. Their mean round arclength has a bounded density $`k`$ relative to round area. At each $`t`$ the projection of the uniform disk onto the transverse line has bounded density, speeds are bounded and the tube area element is bounded below. Every curve is one-sided. Thus $`\int(r-1)k\,dA_{\rm rd}\ge d/2`$ and

~~~math
               A\ \ge\ 2\pi H+\frac{d^2}{4\int k^2\,dA_{\rm rd}} .
~~~

The size of this last term depends on the tube. A bound on a single curve's length defect by itself would give no quantitative area gain.

For fixed $`g`$ and $`0\lt T_0\le T_1\lt\infty`$ there is a uniform $`\eta(g,T_0,T_1)\gt0`$ such that $`A\ge2\pi\tanh T+\eta`$ throughout $`T_0\le T\le T_1`$. Use the midpoints of a longest edge and rotate them to angular coordinates $`-D/2,D/2`$. Their separation and both interval lengths are at least $`l_*=\pi/(6g-3)`$. The short arc crosses the end transversely and its interior misses both ends. A narrow tube uses only the open cylinder and the two paired seam neighborhoods, which have a fixed available angular radius $`l_*/4`$. The local gluing in these coordinates is reflection about zero. For nearby $`(T,D)`$, shift the two seam neighborhoods by opposite angular translations and rescale the height. Interpolate the shifts in the cylinder interior, with the deck-translated choice at the lower end. On a closed smaller tube these identifications and the round lengths converge in the two smooth pieces up to the seam. Thus the same smoothed family retains a positive length defect and a uniform upper bound on its occupation density nearby. A finite cover of $`[T_0,T_1]\times[l_*,\pi]`$ proves the assertion, independently of the other edge lengths. The size of $`\eta`$ is open here.

## Two directions in the same physical metric

Let $`I,J`$ be the two occurrences of an edge of length $`l`$. Order their midpoints in a period so that $`0\lt m'-m\lt2\pi`$. The overlap of $`I`$ and $`J-\pi`$ about their common overlap midpoint $`a_0`$ has half-width

~~~math
                    h=\tfrac12\bigl(l-|m'-m-\pi|\bigr)_+ .
~~~

If $`h\gt0`$, the column $`|\theta-a_0|\lt h,\ -T\le u\le T`$ is a second flat Möbius band in $`N`$. Its top is attached to its bottom by $`\theta\mapsto2a_0-\theta`$ and its one-sided core has flat length $`2T`$. The column and its antipodal column in $`X`$ are the two parts of its lift. Distinct edge pairs give disjoint transverse bands because their two column interiors use disjoint intervals on the upper boundary. The horizontal band intersects all of them.

Use flat area on $`N`$ and write $`\rho`$ for the physical length density. On the full horizontal band use $`\sigma=1/\cosh u`$. On transverse band $`i`$ use $`\sigma_i=\beta/\cosh(\beta(\theta-a_i))`$, with $`\beta=\pi/(2T)`$, extended by zero outside. The functions are well-defined on the quotient up to sets of area zero. The band average gives $`\langle\rho,\sigma\rangle\ge\|\sigma\|^2`$ and $`\langle\rho,\sigma_i\rangle\ge\|\sigma_i\|^2`$. Put $`v=\sum_i\sigma_i`$ and $`f(x)=\arctan(\sinh x)`$. Direct integration gives

~~~math
 \begin{aligned}
 U&=\|\sigma\|^2=2\pi\tanh T,\\[2pt]
 V&=\|v\|^2=2\pi\sum_i\tanh(\beta h_i),\\[2pt]
 C&=\langle\sigma,v\rangle=4f(T)\sum_i f(\beta h_i).
 \end{aligned}
~~~

The last equality integrates over each full transverse rectangle once in $`N`$, using $`f'(x)=1/\cosh x`$. For **any** $`a,b\ge0`$, expanding $`\|\rho-a\sigma-bv\|^2\ge0`$ gives

~~~math
        A\ \ge\ (2a-a^2)U+(2b-b^2)V-2abC .
~~~

When $`C\lt\min(U,V)`$, the best right side is $`U+(V-C)^2/(V-C^2/U)`$. Only a two-by-two linear system is involved.

**Four-strip criterion.** In any genus, if four distinct transverse bands have $`h_i\ge3\pi/50`$, then $`A\gt6.23`$ for every $`T\gt0`$, and $`A\gt2\pi`$ for $`0\lt T\le8/5`$. At $`T=13/10`$, trimming each of these bands to half-width $`3\pi/50`$ gives $`U,V\lt5.63`$ and a combined bound above **6.57**.

Here are details verifying the full height range. Trim to equal widths and put $`c=3\pi^2/100,\ x=c/T`$. Then $`V=8\pi\tanh x`$ and $`C=16 f(T)f(x)`$. For $`T\le1.10`$, monotonicity gives $`V\gt2\pi`$. For $`T\ge2.78`$, $`U\gt6.23`$. On the remaining interval use 42 intervals of length $`1/25`$. On each, use nonnegative rational weights rounded to hundredths from the midpoint system, with $`a,b\le1,\ 2ab\le1`$. The second derivative of the displayed lower bound is at most 24. Indeed $`U''\le0`$, $`V''\le16\pi c/T^3`$, and $`f\le\min(x,\pi/2)`$ at argument $`x`$, $`0\lt f'\le1`$, $`|f''|\le1/2`$ give

~~~math
      -C''\le16\left(\frac{c}{2T}+\frac{2c}{T^2}
                          +\frac{\pi c^2}{4T^4}\right).
~~~

The two upper bounds sum to less than 24 already at $`T=1.10`$. Linear interpolation between endpoint certificates therefore costs at most $`24(1/25)^2/8`$. The replay checks each endpoint with rational bounds for exponentials and arctangents. [Scalar certificate and topology checks](issue163_sewn_cylinder_check.py)

## Two genus-two diagrams

Number sixteen consecutive intervals from 0 to 15. Glue the following pairs by reflection.

~~~text
 (0,8)  (1,9)  (2,15)  (3,6)  (4,12)  (5,13)  (7,10)  (11,14)
~~~

Use length units of $`\pi/800`$. Give intervals 2 and 15 length 101, intervals 7 and 10 length 99, and each other interval length 100. If $`p`$ is the pairing permutation, the cycles of $`j\mapsto p(j)+1\bmod16`$ give the vertex valences $`3,3,3,3,4`$. There are five vertices and eight edges, giving the required genus two on this side. The four positive half-widths in the same units are $`50,50,49,49`$. All exceed 48. The four-strip criterion therefore applies for every height and survives small changes of the paired lengths. These lengths break the half-period symmetry of the edge data. The proof uses no automorphism of the conformal surface.

The estimates cover a neighborhood in unrestricted conformal moduli as well. A marking of distortion $`K`$ transfers a metric by dominating its two length singular values, at an area cost of at most $`K`$. Hence every class within $`K\le1.012`$ of any height of this family has area above 6.15. At height 1.3 every class within $`K\le1.045`$ has area above $`2\pi`$. [Conformal transfer proof](issue163_thin_genus_two.md#from-cylinders-to-compactness)

There are also genus-two diagrams with **no open band of vertical one-sided trajectories**, even when multiple passages through the graph are allowed. Use eight equal intervals and pairs $`(0,2),(1,3),(4,6),(5,7)`$. The vertex permutation is one eight-cycle, giving genus two. A vertical trajectory meeting the upper end in interval $`j`$ returns to the bottom in interval $`p(j)+4\bmod8`$. This permutation exchanges the two blocks of four and has four two-cycles. Traversing a full column uses the sheet exchange once. Every regular closed vertical trajectory therefore preserves orientation. In particular at $`T=1.3`$ the two-direction method on this diagram gives only $`2\pi\tanh(1.3)\lt5.42`$. The oblique shortcut proved above still applies. A bound for general diagrams needs information beyond the vertical trajectories.

## A countable reduction for the original filling problem

For the **bordered filling itself**, use its conformal double across the actual boundary. The reflected double has the same single-cylinder construction for the boundary class. Reflection preserves orientation along the core and exchanges ends. Since it fixes the boundary, it acts by $`(\theta,u)\mapsto(\theta,-u)`$. The filling thus occupies $`0\le u\le T`$, with its genuine external boundary at zero and the same kind of paired-edge graph at $`T`$. The physical arclength marking on the external circle is free. Keeping that marking and **all** boundary distance inequalities gives the original problem.

For fixed $`g\ge1`$, the infimum is unchanged if one restricts to diagrams with $`l_i/\pi`$ and $`T`$ rational. Approximate the positive lengths with their sum fixed at $`\pi`$. On the upper circle choose an increasing smooth reparametrization sending each occurrence to its new interval. Use translations near all endpoints, interpolate with derivative tending uniformly to one, and reflect the reparametrization on the paired occurrence. It respects every edge gluing. Interpolate it to the identity in the lower third of the cylinder, also changing the height by a small vertical translation near the graph. The resulting marking has distortion $`K\to1`$, is the identity near the external boundary and is a flat translation in vertex sectors. It consequently extends conformally across each cone point. On the orientation double of an antipodal quotient one makes the lower interpolation the deck translate of the upper one.

On the new surface take a conformal length element equal to the larger singular value of the transported physical metric's length map, measured in any smooth target reference metric. It dominates transported lengths and its area is at most $`K A`$. It agrees with the old metric on the external collar. Smooth majorants can be taken with arbitrarily small area cost, equal to the given factor on a smaller external collar. Thus the boundary length and every boundary distance constraint survive. The reverse inequality for the infima follows by restriction. This reduction also applies to the stronger orientation-reversing loop problem on closed quotients, with no external marking. The two problems have distinct feasible metrics.

The integer diagrams have a further description. Write $`l_i=n_i d`$ with positive integers $`n_i`$ and $`d=\pi/\sum_i n_i`$. The double maps conformally to the sphere obtained from the rectangular torus of periods $`d,4iT`$ by $`z\sim-z+2iT`$. Each upper edge map is $`z\mapsto-z+k d+2iT`$ across that edge, and the lower edge maps agree modulo the periods. The local map extends across a vertex of angle $`v\pi`$ over a target corner of angle $`\pi`$ with local degree $`v`$. Away from the four corners it is a covering. Its degree is $`2\pi/d`$ by flat areas. The equator has a single preimage circle covering it with that degree, and the two upper corners are the only possible branch values in the northern half. Both real structures above descend to reflection across the equator since $`\pi/d`$ is integral. This gives a dense family described by integer edge lengths and four possible branch values. The covering degree can grow with the denominators. [Eskin and Okounkov on pillowcase covers](https://arxiv.org/abs/math/0505545)

The unrestricted genus-two $`2\pi`$ bound and the unrestricted all-genus 6.15 bound remain open. The all-genus numerical lower bound on this branch is [6.096298010216328189](issue163_distance_balls.md).
