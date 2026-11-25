# Which gradient configurations can a filling realize?

Let $M$ be a compact connected orientable Riemannian surface with one isometrically embedded boundary circle of length $2\pi$. For a boundary point $a$, let $b$ be its antipode and write

```math
 r_a(x)=d_M(a,x),\qquad F_a=(r_b-r_a)/2,\qquad H_a=(r_a+r_b-\pi)/2 .
```

Two different tests apply to the optimization. A mixture supported entirely on unit gradients for even **one fixed anchor** cannot be the global occupation of a filling of area below $2\pi$. On the other hand, at a single point any finite collection of planar gradient values and admissible profile values can be approximated on true fillings, with arbitrarily small additional area if genus is unrestricted. The first test concerns the proportion of area occupied by the optimizer. The second determines which pointwise tests a comass comparison must retain. [A rank violation in the current optimizer and the improved bound](issue163_planar_comass.md)

## A forced loss of unit gradient in positive genus

For every filling of positive genus, for **each** boundary point $a$ and every $`\eta\gt 0`$,

```math
 \mathrm{Area}\{x: |\nabla F_a(x)|^2<1/2+\eta\}>0.
```

In particular, unit vectors throughout a proposed global occupation fail this test. A filling with area below $2\pi$ has positive genus by the disk filling theorem. The estimate gives a threshold for the gradient loss. A uniform lower bound on the measure of the exceptional set for a putative filling below $6.15$ remains open. [Disk theorem and genus-one extension, Bangert–Croke–Ivanov–Katz](https://arxiv.org/abs/math/0405583)

**Proof.** Interior distance gradients have norm one almost everywhere, and therefore $`|\nabla F_a|^2+|\nabla H_a|^2=1`$. If the displayed set had zero area for some $`0\lt \eta\lt 1/2`$, then $`H_a`$ would be $c$-Lipschitz for $`c=\sqrt{1/2-\eta}\lt 1/\sqrt2`$. Here an almost-everywhere gradient bound for a Lipschitz function gives the same intrinsic Lipschitz constant, by local smoothing in charts, integration along interior paths, and passage to the boundary by continuity.

For an interior $x$, let $v,w$ be the terminal unit velocities of any shortest paths from $a,b$ to $x$. Each is a supergradient of its distance function. For example, take a point $y$ shortly before $x$ on the first path, in a convex normal ball about $x$. The smooth function $`r_a(y)+d_M(y,\cdot)`$ touches $`r_a`$ from above at $x$ and has gradient $v$. Thus $`H_a`$ has an upper support with gradient $(v+w)/2$. A $c$-Lipschitz function gives every such gradient norm at most $c$, by taking a displacement opposite to the support gradient. We obtain, for every pairing of terminal velocities,

```math
 v\cdot(-w)\ge 1-2c^2>0 .
```

Consequently $`r_a`$ has a local direction of strict increase at every interior point. Fix one $w$ and extend $-w$ locally to a smooth vector field. Terminal velocities from $a$ vary upper semicontinuously in the interior. Indeed a sequence of minimizing paths has a uniformly convergent subsequence, and their final short geodesic segments converge with their velocities in a normal ball. After shrinking the neighborhood, the field has positive pairing with every terminal velocity. Along its flow $`r_a`$ strictly increases. To see the derivative lower bound along an integral curve, use the smooth upper support at the current point and a negative time increment, at times when the Lipschitz composition is differentiable.

The field can also be taken tangent to the boundary away from $a,b$. Here are the boundary details. Use normal collar coordinates $(s,v)$, with $v$ the depth and $s$ arclength increasing from $a$ toward $b$ on the relevant boundary semicircle. The trace of $`r_a`$ equals $s$ up to translation. Join $(s,v)$ to $(s\pm\sqrt v,0)$ by straight coordinate segments. Each has length at most $\sqrt v+O(v^{3/2})$ because the tangential metric coefficient differs from one by $O(v)$ along the segment. The Lipschitz inequality in both directions gives

```math
 r_a(s,v)=r_a(s,0)+O(v^{3/2}) .
```

Take the last $v/2$ of a minimizing path ending at $(s,v)$. It is an interior geodesic and $`r_a`$ increases by $v/2$ on it. The estimate at its endpoints shows that $s$ increases by $v/2+O(v^{3/2})$. Coordinate acceleration is bounded on the collar, so the terminal unit velocity has $s$-component $1+O(\sqrt v)$. All such velocities approach the increasing boundary tangent uniformly on compact arcs away from the two anchors. The vector field $`\partial_s`$ therefore has the required pairing on a collar, and increases the boundary trace as well.

The maximum of $`r_a`$ cannot occur in the interior. On the boundary it equals $\pi$ only at $b$, so $b$ is the unique maximum and $a$ the unique minimum. On every compact band $`d\le r_a\le\pi-d`$, a partition of unity patches the local fields to a smooth field tangent to the boundary and increasing $`r_a`$ at a uniformly positive rate. Any loop in the interior lies in such a band for small $d$. Flow each of its points until it reaches the level $\pi-d$. The hitting time depends continuously on the initial point by strict increase and continuity of the flow. For sufficiently small $d$ this level is contained in a contractible boundary chart at the unique maximum. The loop contracts in $M$. Thus $M$ is simply connected and is a disk by the classification of compact surfaces with boundary. This proves the claim by contraposition.

## How much of this loss would move the bound?

The threshold gives $`\mathrm{Lip}(H_a)\ge1/\sqrt2`$ in positive genus. Its effect on the area can be quantified. Use the original normalized bisected-gap diagonals $`D_j(x)`$ on any rotated grid. Write $`T=\int_M\sum_jD_j\,dA`$ and let $p$ be the fraction of this weight on pairs $(x,j)$ with $`|\nabla F_j(x)|^2\le0.51`$. Every positive-genus filling has $`p\gt 0`$ because each $`D_j\ge1/(16n)`$. The earlier excess inequality and $`|\nabla H_j|^2\ge0.49`$ on these pairs give

```math
 B+0.49pT\le T\le\mathrm{Area}(M),\qquad
 \mathrm{Area}(M)\ge\frac{B}{1-0.49p}.
```

Here $B$ is the exact bisected-gap bound. Any filling of area below $6.15$ therefore requires $`p\lt 0.017957`$ for **every** rotation of the grid. Showing that just $1.8$ percent of the old diagonal weight must occur in this set in a smaller filling would give an area above $6.15013$. [Weighted excess and the diagonal floor](issue163_angular_energy.md#a-geometric-test-for-any-candidate-below-615)

The measure can approach zero in positive genus when the area approaches $2\pi$. For example remove two small interior disks from the hemisphere and join their rims by a thin product cylinder of length $10\pi$, using the smooth rim construction below. On the retained hemisphere the boundary distance functions converge uniformly to their round values. Short paths through a partial cylinder project to its rim, and a round minimizing arc can detour around the two small caps at cost $O(s)$ for hole radius $s$. Away from the holes the gradients of each fixed distance converge weakly in $L^2$, by uniform convergence. Their norms equal one almost everywhere before and after the limit, giving strong $L^2$ convergence on compact subdomains. The leftover regions have vanishing area on exhaustion. The antipodal excess gradients hence tend to zero in $L^2$ for every fixed anchor, as they vanish on the hemisphere. For each fixed finite grid this gives $p\to0$, since the diagonals are bounded and $T\ge B$. A quantitative improvement must account for the area deficit from $2\pi$ as well as topology.

## Local realization at arbitrarily small added area

Fix finitely many distinct boundary labels and their antipodes. Prescribe profile values $`u_a`$ with $`u_b=-u_a`$ and $`|u_a-u_d|\le d_{S^1}(a,d)`$ for every pair of labels. Prescribe planar covectors $`z_a`$ of norm at most one with $`z_b=-z_a`$. Given **any** admissible filling $`M_0`$ and $`\varepsilon\gt 0`$, there is a smooth orientable isometric filling $M'$ with

```math
 \mathrm{Area}(M')<\mathrm{Area}(M_0)+\varepsilon
```

and an open Euclidean patch on which $`|F_a-u_a|\lt \varepsilon`$ and $`|\nabla F_a-z_a|\lt \varepsilon`$ for every sampled $a$ at almost every point. The added genus can depend on the number of labels. The original filling need only satisfy the stated metric hypotheses.

**Construction.** First shrink all $`u_a`$ toward zero by a common factor arbitrarily close to one. This makes every pair inequality for distinct labels strict. Write $\delta$ for the smallest resulting pair margin $`d_{S^1}(a,d)-|u_a-u_d|\gt 0`$. For each antipodal pair choose unit directions $`v_a,v_b`$ with $`(v_a-v_b)/2=z_a`$. For example use $`v_a=k+z_a`$, $`v_b=k-z_a`$, where $`k\perp z_a`$ has length $`\sqrt{1-|z_a|^2}`$. Perturb the directions arbitrarily slightly to make them all distinct.

Take a flat square torus of side $10r$ with center $o$ in a Euclidean chart and mark the points $`p_a=o+r v_a`$. Choose $r$ so that the whole torus has area less than $\varepsilon/2$. Inside $`M_0`$ choose points $`b_a`$ within distance $\xi$ of the corresponding boundary labels on short normal segments. Remove a small open disk of radius $s$ about each $`p_a`$ and $`b_a`$. Connect each pair of holes by a circular product cylinder of length $`L_a=10\pi-u_a`$. Holes are disjoint and all original boundary points are retained.

One can perform this surgery with smooth metrics that dominate the old metrics on the retained pieces. In geodesic polar coordinates around each hole the local metric is $d\rho^2+G(\rho,\theta)^2d\theta^2$ with $G\le 2\rho$ for small $\rho$. On $s\le\rho\le2s$ interpolate by a smooth cutoff to $d\rho^2+(4s)^2d\theta^2$ near the inner edge. Both metrics dominate the old tensor where they are mixed. Glue cylinders of radius $4s$ along these product ends with compatible orientation. The area cost of the changes to the annuli is $O(s^2)$ per hole and each cylinder costs $`8\pi s L_a`$. With $r$ fixed we can make the added area less than $\varepsilon$.

The external circle remains isometric. Any path crossing a full cylinder already has length greater than $\pi$. For a shorter boundary path, each visit to a partial cylinder can be projected back to its entrance rim without increasing length. The remaining path projects to $`M_0`$ with its original metric, which supplies the required lower bound on length.

For points $y$ near $o$, every shortest path to the boundary label $a$ crosses exactly the cylinder indexed by $a$. To check this, let $|y-o|\le\rho$. A direct path through the intended cylinder costs at most $`r+\rho+L_a+O(\xi+s)`$ with a constant depending on the finite set of holes. Small detours and travel along a rim cost $O(s)$ per hole. Three full crossings exceed this cost when $r,\rho,\xi,s$ are small. One crossing through the wrong cylinder $d$ costs at least

```math
 r-\rho-s+L_d+d_{S^1}(d,a)-\xi-s .
```

The initial estimate follows by projection to the flat torus, and the final estimate follows by projection to $`M_0`$ and the boundary triangle inequality. Partial cylinder visits also project to their rims in these comparisons. The wrong crossing costs at least $\delta$ more in the limit. Take $\rho,\xi,s$ sufficiently small, keeping $s$ small enough for the chosen hole centers. The distances to the labels then approach $`r+10\pi-u_a`$ as $y\to o$ and the mouth sizes and offsets tend to zero. Their half-differences approach the prescribed values.

The same comparison controls the gradients. The first part of a shortest path to $a$, projected to the flat torus, ends within $s$ of $`p_a`$ and has length $r+o(1)$. Its first fixed segment of length $r/3$ lies in the untouched Euclidean chart. As $y\to o$ every limit of these paths is the unique straight segment from $o$ to $`p_a`$, by compactness of arclength parametrizations and the injectivity radius of the torus. Their initial directions therefore converge to $`v_a`$. At differentiability points this gives $`\nabla r_a\to-v_a`$ and $`\nabla F_a\to(v_a-v_b)/2`$. The convergence is uniform over choices of minimizing paths in sufficiently small patches by the same subsequence argument. This proves the assertion.

For a form with coefficients constant in an open profile chamber, any chosen planar test in that chamber can consequently be approached on a positive-area patch of a genuine filling. Taking $`M_0`$ close to the filling infimum gives the same pointwise obstruction there. The patch can have arbitrarily small area. The global gradient loss above and the signed projected area in the comass proof constrain how an entire filling can distribute such configurations.
