# How much can finite antipodal distance tests miss?

Let $A$ be the infimum of the areas of compact connected orientable fillings of the intrinsic circle of length $2\pi$ with arbitrary genus. Let $A_n$ be the analogous infimum when only the $n$ antipodal distances at angles $j\pi/n$, $`0\le j\lt n`$, are required to equal $\pi$. The whole boundary must still be a single circle of length $2\pi$. For $n\ge2$,

```math
 \boxed{(1-1/n)A\le A_n\le A,\qquad 0\le A-A_n\le 2\pi/n.}
```

The additive estimates are $0.056099869$ for $n=112$ and $0.028049935$ for $n=224$, rounded upwards. They compare the **actual infima of areas**. The value $6.095889052386098292$ obtained by calibration is a lower bound for $A_{112}$. A lower bound cannot be substituted for an actual filling's area in the construction below. [All-genus calibration and local extension criterion](issue163_midpoint.md)

## Repairing all shortcuts by changing one semicircle

Write $h=\pi/n$ and let $M$ pass the finite tests. Every sampled anchor has the correct distance to *every* old boundary point. Indeed the two distances from that point to a tested antipodal pair are bounded above by the two circle distances, which sum to $\pi$, and bounded below in sum by the tested distance $\pi$. It follows in particular that the entire semicircle $[\pi,2\pi]$ is isometrically embedded. The distance coordinate from angle zero has unit slope there.

Choose any genuine all-genus filling $K$. Scale $n$ copies of its metric in length by $1/n$ so that each boundary has length $2h$. Glue one half of such a boundary to each of the $n$ old gaps covering $[0,\pi]$, preserving arclength and choosing the compatible orientation. The opposite half replaces that old gap in the external boundary. The other semicircle of $M$ is kept. The area of the resulting surface is

```math
 \mathrm{Area}(M)+\frac1n\mathrm{Area}(K).
```

The new boundary has exactly its circle metric. To see this, any excursion through an attached filling between its boundary points can be replaced by an equatorial arc of no greater length, since its boundary is isometric. Thus distances between external boundary points can be computed in the old $M$ with one extra interval of length $h$ joining the endpoints of each replaced gap. Entire added intervals traversed in the middle of a path can be replaced by the old intervals of the same length. A path starting in the interior of an added interval either stays there or passes through an old anchor. Between such an anchor and any old boundary endpoint, and between any two anchors, the correct circle distance is available as a lower bound. If both endpoints belong to the retained old semicircle, that whole semicircle already has the correct distances. Concatenating the comparison arcs shows that every path costs at least the desired circle distance. For two endpoints on the same added edge the direct segment has the same property. The external boundary supplies equality. Equivalently, the gluing length metric is computed by taking infima over finite chains of paths in the pieces, to which these replacements apply.

Taking $K$ to be the unit hemisphere gives the additive cost $2\pi/n$. Taking the areas of $M$ and $K$ down to their respective infima gives $A\le A_n+A/n$. Every full filling also passes the finite tests, proving the other inequality. The ability to increase genus when attaching $K$ is why the infimum here ranges over all orientable fillings.

## Passing to smooth metrics

The construction initially has seam edges and finitely many boundary corners. Here is a justification that taking smooth infima gives the same estimates. In coordinates normal to the interior of each seam edge the glued tensor is continuous, since the two arclength metrics agree. A boundary vertex consists of finitely many smooth sectors and has a coordinate half-disk in which the piecewise metric and a smooth positive background metric are bounded by constant multiples of one another. One obtains such coordinates by rescaling the angular variable in each sector and using common arclength along the seam rays.

In shrinking vertex neighborhoods dominate the piecewise metric by a fixed large multiple of the background metric, interpolating with a cutoff. On the complement uniformly smooth the continuous metric from above, using an arbitrarily small multiple of the background metric to absorb the approximation error. A partition of unity preserves domination. This gives smooth metrics with area at most the glued area plus $o(1)$ and perimeter $L=2\pi+o(1)$. They dominate all old path lengths. The length increase on each boundary arc is at most the increase of the whole perimeter. Thus their boundary distances are at least the new shorter arclength distance minus $\delta$, where $\delta=L-2\pi\to0$.

Attach a product cylinder of circumference $L$ and height $H=\tfrac12\sqrt{L\delta+\delta^2}$. Its new outer circle has exactly its intrinsic distance. A prospective shortcut of length less than $L/2$ which meets the inner rim first at $u$ and last at $v$ has horizontal angular distances $a,b$ on its initial and terminal cylinder pieces, with $`a+b\lt L/2`$. The middle piece has length at least the old surface distance $d_M(u,v)$, by projecting any remaining cylinder visits to the inner rim. The two cylinder pieces together cost at least

```math
 \sqrt{H^2+a^2}+\sqrt{H^2+b^2}
 \ge\sqrt{4H^2+(a+b)^2}\ge a+b+\delta .
```

The last inequality uses $a+b\le L/2$ and the definition of $H$. This pays the entire possible boundary-distance error. Paths confined to the cylinder project to the outer circle. The cylinder costs $LH=o(1)$ area. Smooth its interior seam from above with arbitrarily small additional area while fixing the external circle, and rescale lengths by $2\pi/L$. This gives smooth, exactly isometric fillings of the required circumference and establishes the infimum statement.
