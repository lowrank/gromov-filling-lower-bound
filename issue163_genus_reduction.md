# Reaching 6.15 by cutting off handles

Let $M$ be a compact connected orientable Riemannian surface with one boundary component. Its ambient distance on that boundary is the intrinsic distance of a circle of length $2\pi$. The result below applies in arbitrarily high genus under a condition on interior curves. It uses the sharp disk and genus-one filling theorem of Bangert, Croke, Ivanov and Katz. [Genus-one theorem](https://arxiv.org/abs/math/0405583)

## A bound in terms of length and depth

Cut $M$ along a disjoint collection of smooth simple closed interior curves. One may also discard components away from the external boundary. Let $P$ be the retained connected surface, with the original boundary and new seam circles $C_i$. Assume that capping all its seams gives a surface of genus at most one. Write

$$
 L_i=\operatorname{length}(C_i),\quad
 d_i=d_M(C_i,\partial M),\quad
 H_i=\left(\frac\pi2-d_i\right)_+,\quad
 B_i=\frac{L_i^2}{2\pi}\sin\!\left(\min\left\{\frac\pi2,\frac{2\pi H_i}{L_i}\right\}\right).
$$

Distances here are measured before cutting. Count both copies of a nonseparating cut if both are retained. Then

$$
 \boxed{\operatorname{Area}(M)\ \ge\ 2\pi+\operatorname{Area}(M\setminus P)-\sum_i B_i.}
$$

The discarded area means $\operatorname{Area}(M)-\operatorname{Area}(P)$, so merely cutting a curve discards zero area.

**Consequences.** Suppose $g-1$ disjoint nonseparating curves of lengths $\ell_j$ leave a connected genus-one surface after cutting and capping.

- At any depth the area is at least $2\pi-\sum_j\ell_j^2/\pi$. This reaches $6.15$ when $\sum_j\ell_j^2\le\pi(2\pi-6.15)=0.4184139826\ldots$. For genus two the exact single-cut threshold is $\sqrt{\pi(2\pi-6.15)}=0.6468492734\ldots$.
- If $\sum_j\ell_j\le2$ and every curve lies at distance at least $1.54$ from the boundary, then $\operatorname{Area}(M)\ge6.16$. Indeed $B_i\le L_i H_i$ and $2\pi-4(\pi/2-1.54)=6.16$.
- If each curve lies at depth at least $\pi/2$, the area is at least $2\pi$ for arbitrary cut lengths. More generally, the sharp bound follows as soon as the discarded area covers the sum of the cap costs.

## Proof

For one seam of length $L$, put $r=L/(2\pi)$. A round hemisphere of radius $r$ has that seam as its equator. Between two points on the equator their distance in the hemisphere equals the shorter equatorial arc. Consequently each excursion through a whole cap can be replaced in $M$ by an arc of no greater length.

For $0\le H<L/4$, keep only the zone from the equator to meridional distance $H$. In coordinates with $0\le t\le H$ the metric is $dt^2+r^2\cos^2(t/r)\,d\theta^2$. Its area is $2\pi r^2\sin(H/r)$. Close its inner circle by a disk of arbitrarily small area. For example, use a meridional interval of length $\varepsilon$ with a bounded warping radius decreasing from the inner circle radius to zero and equal to distance from the tip near the tip. This costs $O(L\varepsilon)$. For $H=0$ attach the small disk directly. For $H\ge L/4$ take the whole hemisphere.

Consider a path between external boundary points. If it avoids every small closing disk, each excursion through a spherical zone or a whole hemisphere costs at least the shorter seam arc. It gives a path in the original surface of no greater length. If it visits closing disks, consider its first and last such visits. Before the first it travels from the external boundary to the corresponding seam and crosses that seam's zone. The first part costs at least $d_i$, since any earlier spherical excursion can be replaced in $M$. The crossing costs at least $H_i$ by the $dt^2$ term in the metric. Thus this initial part costs at least $d_i+H_i\ge\pi/2$. The terminal part similarly costs at least $\pi/2$, including when both visits are at the same disk. A path of length at least $\pi$ cannot shorten an intrinsic boundary arc. The shorter boundary arc itself is always available. It suffices to test transverse piecewise smooth paths by length approximation.

The glued metrics are continuous across the seams in arclength and inward-normal coordinates. They can be smoothed from above with arbitrarily small area increase, leaving a neighborhood of the external boundary fixed. To see this, approximate the tensor uniformly by a smooth tensor in the compact union of seam collars. Add a smooth majorant of the uniform error times an auxiliary positive metric there, using a cutoff equal to one on the smoothing support. Positivity, domination and convergence of the area follow from uniform approximation on a compact set. The boundary metric and the distance condition survive. Applying the sharp theorem to the smoothed genus-zero or genus-one filling and sending the smoothing and closing costs to zero proves the inequality.

## An intrinsic test for cut placement

The depth estimate uses the uniform upper bound $\pi$ for every external boundary distance. Finer data give a smaller cap when a shallow seam is localized. Choose a proposed collar height $h_i\ge0$ for each seam. Heights at least $L_i/4$ give whole hemispheres with cost $L_i^2/(2\pi)$. For seams with shorter collars set $a_i(s)=d_M(\gamma(s),C_i)$. It suffices to have

$$
 a_i(s)+h_i+h_j+a_j(t)\ \ge\ d_{S^1}(s,t)
$$

for every pair of short collars $i,j$ and every $s,t$ on the external boundary. The first and last visits in the proof give exactly this inequality. The cost of a short collar is then $L_i^2\sin(2\pi h_i/L_i)/(2\pi)$.

One may also use $h_i=\operatorname{diam}_M(C_i)/2$ for an individual seam when this is less than $L_i/4$. Any excursion from that seam through its closing disk and back then costs at least its original ambient diameter. Replace it by an original path of no greater length between its endpoints. Such a seam needs no pairwise external test. These replacements compare lengths in the original surface, which may include the discarded region.

For an unrestricted $6.15$ theorem along this route the missing estimate is the existence of a genus-reducing choice with $\sum_i B_i-\operatorname{Area}(M\setminus P)\le 2\pi-6.15$ in every putative smaller filling. The argument gives the bound whenever the displayed condition holds.
