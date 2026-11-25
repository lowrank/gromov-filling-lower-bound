# Reaching 6.15 by cutting off handles

Let $M$ be a compact connected orientable Riemannian surface with one boundary component. Its ambient distance on that boundary is the intrinsic distance of a circle of length $2\pi$. The result below applies in arbitrarily high genus under a condition on interior curves. It uses the sharp disk and genus-one filling theorem of Bangert, Croke, Ivanov and Katz. [Genus-one theorem](https://arxiv.org/abs/math/0405583)

## A bound in terms of length and depth

Cut $M$ along a disjoint collection of smooth simple closed interior curves. One may also discard components away from the external boundary. Let $P$ be the retained connected surface, with the original boundary and new seam circles $C_i$. Assume that capping all its seams gives a surface of genus at most one. Write

```math
 L_i=\mathrm{length}(C_i),\quad
 d_i=d_M(C_i,\partial M),\quad
 H_i=\left(\frac\pi2-d_i\right)_+,\quad
 B_i=\frac{L_i^2}{2\pi}\sin\!\left(\min\left\{\frac\pi2,\frac{2\pi H_i}{L_i}\right\}\right).
```

Distances here are measured before cutting. Count both copies of a nonseparating cut if both are retained. Then

```math
 \boxed{\mathrm{Area}(M)\ \ge\ 2\pi+\mathrm{Area}(M\setminus P)-\sum_i B_i.}
```

The discarded area means $\mathrm{Area}(M)-\mathrm{Area}(P)$, so merely cutting a curve discards zero area.

**Consequences.** Suppose $g-1$ disjoint nonseparating curves of lengths $\ell_j$ leave a connected genus-one surface after cutting and capping.

- At any depth the area is at least $2\pi-\sum_j\ell_j^2/\pi$. This reaches $6.15$ when $\sum_j\ell_j^2\le\pi(2\pi-6.15)=0.4184139826\ldots$. For genus two the exact single-cut threshold is $\sqrt{\pi(2\pi-6.15)}=0.6468492734\ldots$.
- If $\sum_j\ell_j\le2$ and every curve lies at distance at least $1.54$ from the boundary, then $\mathrm{Area}(M)\ge6.16$. Indeed $B_i\le L_i H_i$ and $2\pi-4(\pi/2-1.54)=6.16$.
- If each curve lies at depth at least $\pi/2$, the area is at least $2\pi$ for arbitrary cut lengths. More generally, the sharp bound follows as soon as the discarded area covers the sum of the cap costs.

## Proof

For one seam of length $L$, put $r=L/(2\pi)$. A round hemisphere of radius $r$ has that seam as its equator. Between two points on the equator their distance in the hemisphere equals the shorter equatorial arc. Consequently each excursion through a whole cap can be replaced in $M$ by an arc of no greater length.

For $`0\le H\lt L/4`$, keep only the zone from the equator to meridional distance $H$. In coordinates with $0\le t\le H$ the metric is $`dt^2+r^2\cos^2(t/r)\,d\theta^2`$. Its area is $2\pi r^2\sin(H/r)$. Close its inner circle by a disk of arbitrarily small area. For example, use a meridional interval of length $\varepsilon$ with a bounded warping radius decreasing from the inner circle radius to zero and equal to distance from the tip near the tip. This costs $O(L\varepsilon)$. For $H=0$ attach the small disk directly. For $H\ge L/4$ take the whole hemisphere.

Consider a path between external boundary points. If it avoids every small closing disk, each excursion through a spherical zone or a whole hemisphere costs at least the shorter seam arc. It gives a path in the original surface of no greater length. If it visits closing disks, consider its first and last such visits. Before the first it travels from the external boundary to the corresponding seam and crosses that seam's zone. The first part costs at least $d_i$, since any earlier spherical excursion can be replaced in $M$. The crossing costs at least $H_i$ by the $dt^2$ term in the metric. Thus this initial part costs at least $d_i+H_i\ge\pi/2$. The terminal part similarly costs at least $\pi/2$, including when both visits are at the same disk. A path of length at least $\pi$ cannot shorten an intrinsic boundary arc. The shorter boundary arc itself is always available. It suffices to test transverse piecewise smooth paths by length approximation.

The glued metrics are continuous across the seams in arclength and inward-normal coordinates. They can be smoothed from above with arbitrarily small area increase, leaving a neighborhood of the external boundary fixed. To see this, approximate the tensor uniformly by a smooth tensor in the compact union of seam collars. Add a smooth majorant of the uniform error times an auxiliary positive metric there, using a cutoff equal to one on the smoothing support. Positivity, domination and convergence of the area follow from uniform approximation on a compact set. The boundary metric and the distance condition survive. Applying the sharp theorem to the smoothed genus-zero or genus-one filling and sending the smoothing and closing costs to zero proves the inequality.

## An intrinsic test for cut placement

The depth estimate uses the uniform upper bound $\pi$ for every external boundary distance. Finer data give a smaller cap when a shallow seam is localized. Choose a proposed collar height $h_i\ge0$ for each seam. Heights at least $L_i/4$ give whole hemispheres with cost $L_i^2/(2\pi)$. For seams with shorter collars set $a_i(s)=d_M(\gamma(s),C_i)$. It suffices to have

```math
 a_i(s)+h_i+h_j+a_j(t)\ \ge\ d_{S^1}(s,t)
```

for every pair of short collars $i,j$ and every $s,t$ on the external boundary. The first and last visits in the proof give exactly this inequality. The cost of a short collar is then $L_i^2\sin(2\pi h_i/L_i)/(2\pi)$.

One may also use $h_i=\mathrm{diam}_M(C_i)/2$ for an individual seam when this is less than $L_i/4$. Any excursion from that seam through its closing disk and back then costs at least its original ambient diameter. Replace it by an original path of no greater length between its endpoints. Such a seam needs no pairwise external test. These replacements compare lengths in the original surface, which may include the discarded region.

For an unrestricted $6.15$ theorem along this route the missing estimate is the existence of a genus-reducing choice with $\sum_i B_i-\mathrm{Area}(M\setminus P)\le 2\pi-6.15$ in every putative smaller filling. The argument gives the bound whenever the displayed condition holds.

## Independent caps on the two sides of a shortest nonseparating loop

Suppose $`C`$ is a smooth simple interior loop of length $`L`$ realizing the shortest length of a closed curve with nonzero mod-two homology in $`M`$. Cut along it, keep the connected cut surface $`P`$, and denote the two seam copies by $`C_+`$ and $`C_-`$. The boundary distances stay protected when each seam is capped independently according to the test below.

First $`C`$ is an isometric metric circle in $`M`$. A path shorter than its shorter arc would split $`C`$ into two loops both shorter than $`L`$, at least one homologous to a nonzero class. Second, $`d_P(C_+,C_-)\ge L/2`$. A path between the two copies, closed in $`M`$ by a shorter seam arc, has odd intersection with $`C`$ and length at most the path length plus $`L/2`$. One sees the odd intersection by moving the closing arc slightly to one side. Paths with other seam contacts are approximated in the interior of $`P`$. These two metric properties suffice for the following argument.

For each copy $`i`$ and arclength parameters $`s,t`$ on it put

~~~math
 D_i(s,t)=\max_{a\in\partial M}
 [\pi-d_P(a,C_i(s))-d_P(\bar a,C_i(t))]_+ ,
~~~

where $`\bar a`$ is antipodal to $`a`$ on the external boundary. Always $`D_i(s,t)\le d_C(s,t)`$. A cap whose seam distances are at least $`D_i(s,t)`$ for every $`s,t`$ suffices, provided its rim has its old arclength. For a path visiting just this cap, between the first and last visit replace any intervening excursions through $`P`$ by seam arcs. The isometry of $`C`$ ensures this costs no more. The cap test now protects every external antipodal pair. Any shorter external route would extend along the boundary to a shorter antipodal route.

For a path visiting both caps let $`i,j`$ denote the first and last copies, possibly equal. Its intermediate portion contains a crossing in $`P`$ between the two copies of length at least $`L/2`$. In the original surface the nearest points on $`C`$ to the two external endpoints, reached from their respective copies in $`P`$, can be joined by a seam arc of length at most $`L/2`$. The initial and terminal distances to the copies plus $`L/2`$ thus already dominate the external boundary distance. There is no joint cap constraint in this case.

### A spherical lune with two prescribed arms

Choose a reflection $`R`$ of a seam fixing points $`p,q`$ at distance $`L/2`$. The two arcs between them are the arms. Put $`u(s)=d_C(p,s)`$, $`r_0=L/(2\pi)`$. A lune of angle $`\gamma`$ in the round sphere of radius $`r_0`$ has these arms as its bounding meridians and area $`2r_0^2\gamma`$. Distances along an arm are $`|u-v|`$. For opposite arms its intrinsic seam distance $`d_\gamma`$ satisfies

~~~math
 \sin^2\!\bigl(d_\gamma/(2r_0)\bigr)
 =\sin^2\!\bigl((u-v)/(2r_0)\bigr)
   +\sin(u/r_0)\sin(v/r_0)\sin^2(\gamma/2).
~~~

This is the spherical cosine law on the convex lune. At angle $`\pi`$ it gives precisely the original seam-circle distance. For each seam let $`q_i`$ be the supremum over opposite-arm nonpole pairs of

~~~math
 \frac{
 [\sin^2(D_i(s,t)/(2r_0))-\sin^2((u(s)-u(t))/(2r_0))]_+
 }{\sin(u(s)/r_0)\sin(u(t)/r_0)} .
~~~

Then $`0\le q_i\le1`$. At the poles the arm-distance test holds automatically. The least area in this lune family protecting all external routes, in the limiting sense at zero angle, is $`4r_0^2\arcsin\sqrt{q_i}`$. In particular, if every reflected pair satisfies $`d_P(a,C_i(s))+d_P(\bar a,C_i(Rs))\ge\pi`$ for every anchor, one may cap this copy at arbitrarily small area. For points on opposite arms, traveling on the second arm from $`Rs`$ to $`t`$ gives $`D_i(s,t)\le |u(s)-u(t)|`$ in this case.

There is also a bound depending just on the worst reflected-pair deficit $`\Delta_i=\max_s D_i(s,Rs)`$. Insert a flat product cylinder of height $`b`$ before the thin lune. Projection of the lune to the meridian coordinate $`u`$ is 1-Lipschitz. Every route entering the lune and returning to the outer rim has length at least $`\sqrt{(u(s)-u(t))^2+4b^2}`$ by the triangle inequality for the absolute horizontal and vertical displacements. A route entirely in the cylinder costs at least $`d_C(s,t)`$. On the other hand $`D_i(s,t)\le\min(L/2,|u(s)-u(t)|+\Delta_i)`$, by traveling from $`Rs`$ to $`t`$ on their shared arm in the opposite-arm case. Maximizing $`\min(L/2,x+\Delta_i)^2-x^2`$ for $`0\le x\le L/2`$ gives $`L\Delta_i-\Delta_i^2`$. Thus a second available cost per copy is

~~~math
 Lb=\tfrac L2\sqrt{L\Delta_i-\Delta_i^2}.
~~~

The lune and cylinder have the exact prescribed rim lengths. Along smooth gluing arcs use smoothing from above as in the first proof. At either lune vertex the total angle after gluing is $`\pi+\gamma\le2\pi`$. Locally each sector admits radial coordinates based at the vertex with metric $`d\rho^2+G^2d\theta^2`$, with $`G/\rho\to1`$ uniformly on each side (use boundary straightening on the smooth side). Rescale the angular sectors proportionally to fill a $`2\pi`$ disk. A fixed multiple of the Euclidean metric dominates the sector metrics in these coordinates. Replace the tensor by this upper metric near the origin and interpolate in a shrinking annulus, then smooth the remaining arcs from above. The added area tends to zero and the original external boundary is untouched.

For example, in genus two a cut with $`L=2`$ and both $`\Delta_i\le1/500`$ gives $`A\ge2\pi-2\sqrt{0.003996}\gt6.15675`$. More generally each operation removes one handle and has the stated cost for that step's cut metric. A bound at $`6.15`$ for all genera would follow from a sequence down to genus one costing in total at most $`2\pi-6.15`$. The existence of such cuts in every putative smaller filling is open.
