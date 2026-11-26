# How much genus the published gradient array requires

The **minimum genus is exactly 98** for realizing the published 112-vector neighboring near-maximizer and its strict scalar profile at a differentiability point of an actual circle filling. Even allowing an error of $`1/400`$ in every vector still requires genus at least six. This obstruction uses the actual shortest paths to the boundary anchors. The neighboring array gives raw density above $`0.99970`$ in the old chamber. The earlier construction realizing arbitrary directions on a small patch allowed the addition of handles. [Archived array](issue163_planar_witness.json) · [Earlier local construction](issue163_gradient_constraints.md#local-realization-at-arbitrarily-small-added-area) · [Exact order and matrix checks](issue163_geodesic_fan_check.py)

## A bound on the cyclic order at an interior point

Let $`a_1,\dots,a_n`$ occur in positive cyclic order on the boundary of a genus-$`g`$ orientable filling. At an interior point $`p`$ suppose all $`d(a_i,\cdot)`$ are differentiable. Write $`v_i=-\nabla d(a_i,p)`$ for the unit initial direction of a minimizing path from $`p`$ to $`a_i`$. First assume these directions are distinct. Let $`\beta`$ be the successor permutation of the labels on the boundary, $`\sigma`$ their counterclockwise successor in the oriented tangent plane, and $`b`$ the number of cycles of $`\sigma\beta^{-1}`$, including fixed points. Then

~~~math
               \frac{n-b}{2}\ \le\ g .
~~~

In particular, at most $`4g`$ labels have different successors in the two orders. This extends the disk's cyclic-order constraint to positive genus. [Ivanov on cyclic order of distance differentials in a disk](https://arxiv.org/abs/0910.2257)

**Proof.** At differentiability, every minimizing path to a given anchor starts in its indicated direction, by first variation on a short interior segment. If paths to two distinct-direction anchors met again, their initial segments to the meeting point would have the same length. Swapping initial segments would give a minimizing path to the first anchor with the second initial direction. Thus these paths are disjoint away from $`p`$, even if a terminal segment follows the boundary. The finitely many spokes can be moved slightly into the interior away from their endpoints in disjoint neighborhoods, keeping the initial order.

Cap the external boundary by a disk and continue the spokes radially to its center. The resulting embedded graph has two vertices and $`n`$ edges. The cyclic order at the new vertex is reversed by the oriented gluing. Following the boundary of a regular neighborhood gives one boundary component per cycle of $`\sigma\beta^{-1}`$. The neighborhood has Euler characteristic $`2-n`$, so has genus $`(n-b)/2`$. Its genus cannot exceed that of the closed ambient surface. Each nontrivial cycle of length $`k`$ moves $`k\le2(k-1)`$ labels, and the sum of $`k-1`$ is $`n-b`$. This proves the successor bound.

For repeated directions one may break ties within each group. Distinct groups still have disjoint traces outside their initial point by the same substitution argument. Truncate inside a small normal disk at $`p`$. In a disjoint neighborhood of each group's remaining paths take an embedded tree joining the entry point to the specified endpoints on the boundary, moving its other points into the interior. A thickening of this tree permits parallel disjoint spokes to all its endpoints. Ordering the tied directions as these spokes leave the entry point gives the same bound. In particular the sum of chord lengths $`\sum_i|v_{\beta(i)}-v_i|`$ is at most $`2\pi+8g`$. The tangent-circle order has polygonal length at most $`2\pi`$, and each of at most $`4g`$ changed edges can add at most two. For almost every $`p`$, differentiability holds for almost every boundary parameter by Fubini. Taking subdivisions of that full-measure set shows that the boundary-parameter field of initial directions has a bounded-variation representative with this same bound.

## A converse with the genus prescribed

Fix finitely many distinct boundary labels and distinct unit directions $`v_i`$. Define $`h=(n-b)/2`$ by their actual oriented orders. Prescribe numbers $`u_i`$ satisfying $`|u_i-u_j|\lt d_{S^1}(a_i,a_j)`$ for all distinct labels. For every $`g\ge h`$ there is a smooth, isometric circle filling of **exactly genus $`g`$** with a common interior differentiability point where the initial directions are $`v_i`$ and the distances are a common constant minus $`u_i`$. For antipodally paired labels with $`u_{i+n/2}=-u_i`$, the half-distance differences are exactly $`u_i`$. The same data can be approached throughout a patch of positive area at common differentiability points.

Take a flat central disk of radius one and a flat product annulus of small height $`\delta`$ with outer boundary the desired circle. Attach narrow Euclidean rectangles between disjoint arcs of the central rim at directions $`v_i`$ and arcs of the inner annular rim at the label longitudes $`a_i`$. Use equal arclength at each attachment, width at most $`\delta`$, and rectangle lengths $`L_i=C-u_i`$ with $`C`$ large enough that $`2\min L_i\gt\pi`$ and $`3\min L_i\gt2+\max L_i`$. The untwisted oriented attachments prescribe the two cyclic orders. Capping the external boundary temporarily would yield a regular neighborhood of the two-vertex graph, so the intermediate surface has genus $`h`$. Cap its *other* boundary circles with round hemispheres. If $`g\gt h`$, use an isometric circle filling of genus $`g-h`$ for one of those caps. One can construct this extra cap with a product collar longer than a quarter of its boundary circumference and any orientable interior of the required genus. Every cap excursion can be replaced by a shorter or equal rim arc. Thus distances between points of the intermediate surface are preserved.

In the intermediate surface a partial visit to a rectangle from one mouth back to that mouth can be projected to the attaching interval at no extra length. Between external boundary points a path staying in the annulus after these replacements dominates its angular displacement. Using two full rectangle crossings already costs more than $`\pi`$. Hence the external boundary is isometric. A path from the central patch to $`a_i`$ has an odd number of full crossings and using three is too expensive. With one crossing through rectangle $`j`$ its length from a point $`y`$ in the central disk is at least

~~~math
          |y-v_j|+L_j+d_{S^1}(a_j,a_i)-2\delta .
~~~

Here $`v_j`$ is also the midpoint of its mouth on the unit rim. At the center the direct route through $`i`$ costs exactly $`1+L_i+\delta`$, and the strict label inequalities give a positive margin against every $`j\ne i`$ for small enough $`\delta`$. A route using $`i`$ costs at least one before reaching the mouth, at least $`L_i`$ for the full crossing and at least $`\delta`$ in the annulus. Equality forces the last segment to move radially at the longitude of $`a_i`$. The full crossing must be straight at the same lateral coordinate, so the disk segment must point to the midpoint $`v_i`$. Replacing cap excursions or partial strip visits does not change the initial segment inside the central disk. Every minimizer therefore has the stated initial direction.

To smooth while preserving those lengths, use signed normal distance $`t`$ and mouth arclength $`s`$ near each seam midpoint. At the central disk mouth the metric is $`dt^2+k(t)^2ds^2`$, with $`k=1+t`$ inside the disk and $`k=1`$ in the strip. Replace $`k`$ by a smooth upper bound agreeing with it off a short interval. This leaves the radial direct path at $`s=0`$ unchanged in length. The strip and product-annulus coordinates are already flat across their midpoint. The rest of each direct path and the external boundary collar can be left untouched. At the finitely many corners the metric is bounded above in smooth charts obtained by rescaling a finite cone angle. Away from the direct paths use smooth upper metrics there and along the remaining seams, gluing majorants by a partition of unity. Domination and the preserved direct paths give the same exact lengths and initial directions at the center in the smooth surface. A distance function with a unique minimizing initial direction is differentiable at an interior point, by first variation in a convex normal ball. Compactness of minimizing paths gives convergence of their initial directions as the starting points approach the center. This also proves the positive-area approximation assertion. The construction controls local distance data and genus and can have large total area.

## The genus test for half differences

Use indices $`0,\ldots,223`$ in boundary order, with antipodal labels 112 apart. Set $`z_j=(v_j-v_{j+112})/2`$, the gradient of the antipodal half-distance difference. Since both directions are unit vectors,

~~~math
              \langle v_j,z_j\rangle=|z_j|^2 .
~~~

Let $`w_j`$ be the rational published array extended antipodally. All its lengths exceed $`0.99999995`$. If $`z_j=w_j`$, then the direction $`v_j`$ makes an angle at most $`\arccos(0.99999995)`$ with $`w_j`$. For a tolerance $`\epsilon`$, use the fact that $`z_j`$ is the mean of the two unit vectors $`v_j,-v_{j+112}`$. If $`|z_j-w_j|\le\epsilon`$, projecting this average onto $`w_j/|w_j|`$ gives

~~~math
       \left\langle v_j,\frac{w_j}{|w_j|}\right\rangle
                     \ge 2(|w_j|-\epsilon)-1 .
~~~

The following two subsets have angular gaps greater than twice the respective possible angular error. All indicated orders therefore persist for the actual shortest paths. The replay certifies the separations by squared dot products of integers and counts the cycles in both choices of frame orientation.

| Labels tested, together with their antipodes | Error in each $`z_j`$ | Genus of the graph neighborhood in the two frame orientations |
|---|---:|---:|
| All half-circle labels except $`53,57,63,66,72`$ | $`0`$ | $`98,\ 100`$ |
| $`0,11,15,33,36,79,84,97,105,111`$ | $`1/400`$ | $`6,\ 6`$ |

The conclusion is pointwise and survives a common rotation of the vectors and cyclic shifts of the grid labels. In particular, on genus two at least one label must differ from the witness by more than $`1/400`$ at every common differentiability point, regardless of the area and scalar profile.

To attain the lower genus 98, write a half-circle entry as $`w_j=(x,y)/D`$ with $`S=x^2+y^2`$ and $`q=\sqrt{(D^2-S)/S}`$. Choose the two actual unit directions

~~~math
       v_j=\frac{(x-qy,y+qx)}{D},\qquad
       v_{j+112}=\frac{(-x-qy,-y+qx)}{D}.
~~~

Their half difference is $`w_j`$. For this choice the 224 directions are distinct and the oriented order gives genus 98. The replay rounds $`q`$ down to a multiple of $`2^{-48}`$ by integer square root, verifies angular gaps wide enough to retain the exact order, and counts the boundary cycles. The construction above with the strict neighboring profile consequently realizes the entire test on a smooth genus-98 filling.

## What survives after ordering the directions

As a small test, put the neighboring vectors into positive cyclic order. Starting from their half-angle slopes $`y/(1+x)`$, pool adjacent blocks whenever their means decrease, then make ties strictly increasing by a rational perturbation. The inverse half-angle formula $`t\mapsto(1-t^2,2t)/(1+t^2)`$ supplies exact unit directions. On the same strict neighboring scalar profile this gives the following normalized densities. Here $`W`$ is the signed single-anchor field including its anchor correction, and $`Q`$ is the constant quarter-turn form.

| Test | $`W`$ | $`Q`$ |
|---|---:|---:|
| Published array, before imposing the order | $`0.999230\ldots`$ | $`0.604389\ldots`$ |
| Ordered neighboring array | $`0.992460\ldots`$ | $`0.627215\ldots`$ |
| Ordered unit directions in the central profile | $`0.99992\ldots`$ | $`1`$ |

Both ordered arrays have graph genus zero with the raw directions extended antipodally. Both scalar profiles are strictly distance-Lipschitz on the finite label set and lie inside their chambers. In spacing units the first has values $`55-j+(2j-55)/2000`$, and the second has values $`1/100`$ up to $`j=56`$ and $`-1/100`$ thereafter on the half circle. The converse realizes both tests on actual fillings of genus two, even on disks. The chamber coefficients persist under small profile perturbations.

For any real combination $`\lambda W+tQ`$ required to have comass at most one pointwise on every genus-two filling, its certified boundary action is **less than 6.12048**. To see this, write the two exact boundary actions as $`b\pi^2,\pi^2/2`$. The two-row linear system $`u_1W_1+u_2W_2=b,\ u_1Q_1+u_2Q_2=1/2`$ has positive solutions. Multiplying the test inequalities by these weights gives the upper bound $`\pi^2(u_1+u_2)`$. The replay uses exact rational directions, the archived integer chamber coefficients, and rational bounds for $`\pi`$. Thus excluding the published witness is a genuine genus-two restriction, while actual shortest paths still rule out reaching 6.15 with this particular pointwise comparison. [Boundary actions and original two-field tests](issue163_fiber_transfer.md#can-adding-this-flux-to-the-finite-calibration-reach-615)
