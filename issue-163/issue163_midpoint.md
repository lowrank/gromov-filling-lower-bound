# An all-genus improvement from the gaps between boundary anchors

For every compact connected orientable Riemannian surface whose single boundary is an isometrically embedded intrinsic circle of length $2\pi$,

```math
 \mathrm{Area}(M)\ge
 \frac{737877064811692678202731938521}{1194666547200000000000000000000}\pi^2
 >6.095889052386098292.
```

The gain over the previous certificate is $`(2016404894069/22399997760000000)\pi^2\gt 0.000888442884240785`$. The correction on an unsplit gap gives $6.095818942814274622$. Bisecting each gap once gives the displayed result with three matrices of order 112. Both use the old global comass budget $U=999999900000/10^{12}$. [Previous finite proof](issue163_free_field.md) · [Exact replay](issue163_midpoint.cjs) · [Integer witness](issue163_midpoint_witness.json)

## What distance information is available?

Let $\gamma$ be the boundary arclength parametrization. For a boundary pair $s,t$, put $\theta=d_{S^1}(s,t)$. The triangle inequality gives

```math
 \pi-d_M(\gamma(s),\gamma(s+\pi))
 \ \ge\ \theta-d_M(\gamma(s),\gamma(t)).
```

Thus the largest boundary shortcut is detected by an antipodal pair. Finitely many antipodal tests can miss one. For example, add an edge of length $\pi-h$ joining antipodal midpoints of gaps in the metric circle with anchor spacing $h$. Any anchor-to-anchor path using this edge costs at least $h/2+(\pi-h)+h/2=\pi$. This metric graph illustrates the loss from sampling. The earlier calculation supplies a lower-bound calibration. It gives no candidate surface in which to measure such a shortcut.

Write $n=112$, $h=\pi/n$, $R=h/2$, and

```math
 F_i(x)=\tfrac12\big(d_M(x,\gamma(ih+\pi))-d_M(x,\gamma(ih))\big),\qquad F_{i+n}=-F_i.
```

Each $F_i$ is 1-Lipschitz in $x$, and the functions are 1-Lipschitz in their angular label in the uniform norm. The isometric boundary fixes $F_i(\gamma(s))=\pi/2-d_{S^1}(s,ih)$.

## Two tents on one gap

Take the gap from $-h$ to $0$ with midpoint $p=\gamma(-h/2)$. Set $c_i=F_i(p)=(55.5-i)h$ and $e_i=F_i-c_i$ for $`0\le i\lt n`$. Since $F_i-F_{i+1}\le h$, these offsets satisfy $e_0\le\cdots\le e_{n-1}$. Along the gap, at signed arclength $t$ from $p$, every $e_i=t$ and $-R\le t\le R$. Define

```math
 L=\big(\min\{R+e_0,\ R-e_{n-1}\}\big)_+,\qquad
 P=(R-d_M(x,p))_+ .
```

The two functions are 1-Lipschitz, and $0\le P\le L$ because $|e_i|\le d_M(x,p)$. On the boundary both tents equal $R-|t|$ on this gap and vanish elsewhere. Indeed $`L\gt 0`$ means that the adjacent anchors at $-h,0$ both have $`F\gt \pi/2-h`$. On the boundary this is exactly the open gap.

On all of $`\{L\gt 0\}`$ the inequalities $`-R\lt e_0\le e_i\le e_{n-1}\lt R`$ put coordinate $F_i$ in the single open bin numbered $111-i$, with bin zero beginning at $-56h$. The full old 2-form there has a constant real skew coefficient matrix $W$, including its scalar multipliers. All $224$ rotations of the gap give the same matrix in the signed frame $F_j,\ldots,F_{j+111}$. The old coefficient rule is invariant under this change of frame. When one index wraps around, exchanging the two indices and changing the sign of one coordinate cancel in the wedge product. The pair class changes from $(k,a,b)$ to $(n-k,b,111-a)$, in the same coefficient orbit. The even scalar weights are invariant as well.

The positive sets of the rotated $L$ are pairwise disjoint. For any two angular labels, antipodality and angular Lipschitz continuity give $F_s+F_t\le\pi-d_{S^1}(s,t)$. Thus two labels with $`F\gt \pi/2-h`$ are at distance strictly below $2h$. At most two grid labels meet this condition and, if two do, they specify a unique gap. The intrinsic balls $`\{P\gt 0\}`$ are contained in these positive sets.

## The closed correction and its norm

Let $g,v\in\mathbb R^n$ each be invariant under reversing the indices. For each rotated gap use its own signed frame $F$. The following weak exterior derivative corrects the old form.

```math
 d\big(L\, g\!\cdot\!dF+P\,v\!\cdot\!dF\big)
 =dL\wedge(g\!\cdot\!dF)+dP\wedge(v\!\cdot\!dF).
```

The primitive has boundary integral $R^2\sum_i(g_i+v_i)$ per gap since $dF_i=dt$ and the tent has integral $R^2$. Stokes for this Lipschitz expression follows termwise from $`\int_M df\wedge dk=\int_{\partial M} f\,dk`$ for Lipschitz functions on a smooth oriented surface. One proof in charts extends the functions across the boundary and smooths with uniformly bounded Lipschitz constants. The functions converge uniformly and their interior derivatives converge in $L^2$. On the boundary the uniform convergence and a uniform bound on total variation give convergence of $`\int f\,dk`$ by integration by parts.

On $`\{L\gt 0\}`$, $dL=dF_0$ or $dL=-dF_{111}$ almost everywhere. Where the arguments of the minimum agree, their derivatives agree almost everywhere on that equality set. A Lipschitz function also has zero differential almost everywhere on each of its level sets. Thus boundaries of the supports contribute no extra comass. The old facet bounds apply wherever all tents vanish.

Append $P$ as coordinate $112$. For column vectors write $a\wedge b=ab^T-ba^T$, extend $g,v$ by a final zero and $W$ by a zero row and column, and denote the standard vectors by $b_i$. The two possible augmented matrices are

```math
 Y_+=W+b_0\wedge g+b_{112}\wedge v,\qquad
 Y_-=W-b_{111}\wedge g+b_{112}\wedge v.
```

Let $S$ reverse the first 112 entries and negate the last one. The verifier checks entrywise that reversal carries the old $W$ to $-W$. Hence $Y_-=-S^TY_+S$. Complex conjugation and the same signed permutation carry a diagonal certificate for the first chamber to one for the second.

The integer witness supplies a diagonal $D$ such that

```math
 D+\tfrac{i}{2}Y_+\succ0,\qquad
 \mathrm{tr}(D)=\frac{99999989798801}{10^{14}}<U.
```

Indeed, for an oriented orthonormal tangent pair $(X,Y)$ let $`z_j=dF_j(X)+i\,dF_j(Y)`$, using $dP$ for the last entry. Then $|z_j|\le1$. Positivity of $D\pm iY_+/2$ gives $`|\sum_{j\lt k}(Y_+)_{jk}(dF_j\wedge dF_k)(X,Y)|\le\sum_j D_{jj}|z_j|^2\le U`$. The same holds in the other chamber, and the original comass bound holds off the supports.

The sums of the integer numerators of $g$ and $v$, in units of $10^{-14}$, are $1403380708346$ and $453903902074$. Since $224R^2=\pi^2/224$, the gain in normalized action is $\pi^2\sum_i(g_i+v_i)/(224U)$. Adding this to the old exact action gives the first bound $6.095818942814274622$.

The proof also works with $P=L$. Substitution restricts the augmented form to $dP=dF_0$ or $dP=-dF_{111}$ in the respective chambers and leaves the boundary action the same. Thus this particular gain already follows from the joint ordering and boundary traces of the sampled coordinates. The proof does not establish a shortcut in a surface or require strict separation of the two tents.

## Bisecting the same boundary gap

The stronger constant needs only three corner matrices of order 112. Keep $L$ and set

```math
 L_\ell=\big(\min\{R+e_0,-e_{111}\}\big)_+,\qquad
 L_r=\big(\min\{e_0,R-e_{111}\}\big)_+.
```

On the boundary these are the tents on the left and right halves of the gap. Their positive sets are disjoint subsets of $`\{L\gt 0\}`$. Throughout the first one $`e_i\lt 0`$ for every $i$, so $dL=dF_0$ there. Throughout the second all $`e_i\gt 0`$, so $dL=-dF_{111}$. Let $J$ reverse the 112 indices. Use the primitive

```math
 L\,s\!\cdot\!dF+L_\ell\,u\!\cdot\!dF+L_r\,(Ju)\!\cdot\!dF,
 \qquad Js=s.
```

The vector $u$ may be asymmetric. Reflection of the coordinate frame $F\mapsto-JF$ interchanges the two half-gaps and negates the full form, including the old $W$. This is a coefficient identity valid on every filling.

Write $B=W+b_0\wedge s$. On the part of the first parent chamber outside both child supports use $B$. On $`\{L_\ell\gt 0\}`$ the differential of the child tent is either $dF_0$ or $-dF_{111}$. Hence the three required matrices are

```math
 B,\qquad B+b_0\wedge u,\qquad B-b_{111}\wedge u .
```

Their reflected matrices cover the other parent chamber. The same level-set argument as above covers ties and zero sets. All three integer diagonals have trace strictly below $U$. Their traces in units of $10^{-14}$ are $99999989872318$, $99999989753112$ and $99999989755295$, respectively.

The boundary integral on one gap is $R^2(\sum_i s_i+\tfrac12\sum_i u_i)$, since each half-tent has integral $R^2/4$. The two sums in units of $10^{-14}$ are $1840460913618$ and $351887960902$. This gives the exact improvement over the old calibration

```math
 \frac{\pi^2}{224U}\left(\sum_i s_i+\tfrac12\sum_i u_i\right)
 =\frac{2016404894069}{22399997760000000}\pi^2
 >0.000888442884240785.
```

Adding the old action proves the bound at the top of this note. Both constructions use the same original grid.

## Exact local replay

From the <code>issue-163</code> directory with Node.js, run

~~~sh
node issue163_midpoint.cjs issue163_inputs
~~~

The checker reconstructs the constant corner field from the pinned archives and the previous master corrections. It clears the denominators and performs fraction-free elimination over the Gaussian integers. At each step both divisions must be exact and the next leading principal minor must be real and strictly positive. The checker tests 113 leading minors for the first construction and 112 for each of the three matrices in the bisected construction. It also checks the trace bounds, reflection identity, boundary actions and rounded-down areas. The earlier all-genus certificate is used as a lemma. Its independent full replay is documented in the [previous note](issue163_free_field.md). The repository's [Lean statements](../docs/current-manuscript.md) concern the earlier Fourier bound.

## Which supports leave room for 6.15?

Test any normalized calibration on the unit hemisphere. Write $A_0$ for the old boundary action and $\omega_0$ for the old form divided by $U$. If the new form has comass at most one and agrees with $\omega_0$ outside a region $E$ on this hemisphere, its boundary action is at most

```math
 A_0+\mathrm{Area}(E)-\int_E\omega_0 .
```

We can bound this quantity for arbitrary changes on either family of supports using only the old corner matrix.

| Union of 224 regions on the hemisphere | Certified interval for the displayed ceiling |
|---|---:|
| Intrinsic balls $`P\gt 0`$ centered at gap midpoints | $[6.138850561,\ 6.139705261]$ |
| Larger regions $`L\gt 0`$ determined by adjacent anchors | $[6.150978383,\ 6.152493731]$ |

Thus changes confined to the actual midpoint balls cannot reach $6.15$ with this exterior form fixed. For the adjacent-anchor regions, the hemisphere test alone allows only a narrow margin above $6.15$. Its upper endpoint also rules out $2\pi$ for all corrections with this support. These are ceilings on calibration actions. [One-dimensional interval replay](issue163_midpoint_budget.cjs) A subsequent flat profile comparison sharpens the ceiling on the aligned adjacent-anchor supports to $6.107523028$. [Flat collar proof](issue163_flat_collar.md)

On the hemisphere $F_i(x)=\pi/2-d(x,\gamma(ih))$. Each larger region is the upper half of the lens common to two spherical caps of radius $h$ whose centers are at distance $h$. Set $\beta=\arccos(\cos h/(1+\cos h))$, the angle of the equilateral spherical triangle of side $h$. The area of one half-lens is $\pi-(1+2\cos h)\beta$, obtained by subtracting the excess $3\beta-\pi$ of one triangle from two sectors of total area $2\beta(1-\cos h)$. The area of a single midpoint half-ball is $\pi(1-\cos R)$.

In either region the primitive of the old form is $`\tfrac12(F-c)^T W\,dF`$ before division by $U$. It vanishes on the bottom edge since $F-c=t\mathbf1$ there. By reflection it suffices to integrate the arc from the left boundary endpoint to the highest point. Write $r=h$ and $a=\beta$ for the lens, or $r=R$ and $a=\pi/2$ for the ball. The arc has length $\ell=a\sin r$. With $\delta_i$ the positive angular difference from its cap center to anchor $i$, its distances satisfy

```math
 \cos d_i(t)=\cos r\cos\delta_i-\sin r\sin\delta_i\cos t,\qquad 0\le t\le a .
```

Stokes gives minus the sum of the chord terms $(F_k-c)^TW(F_{k+1}-c)$ for the two oriented arcs together, up to the polygonal error. On reflection the offsets transform by negative coordinate reversal and $W$ changes sign, which gives the factor of two.

For arbitrary real vectors $u,v$ with sup norm at most one we have $|u^TWv|\le2U$ because the planar vectors $(u_i,v_i)/\sqrt2$ are allowed by the old diagonal certificate. In arclength $F$ is 1-Lipschitz in the sup norm. On a segment of length $b$, replacing the primitive integral by its chord value therefore costs at most $Ub^2/2$. With $K=256$ equal segments per half-arc the normalized total error per region is at most $\ell^2/K$. Rounding every offset at a vertex to sup error $\varepsilon$ adds at most $2K\varepsilon(2R+\varepsilon)$, because the true offsets have sup norm at most $R$. The verifier encloses every vertex by directed cosine comparisons, uses $\varepsilon=6\pi/(224\cdot10^8)$, and includes both errors. From the <code>issue-163</code> directory, run

~~~sh
node issue163_midpoint_budget.cjs issue163_inputs
~~~

## Why a missing antipodal distance needs a global test

There is a precise limitation on adding more distance coordinates separately inside boundary gaps. Suppose just the finitely sampled antipodal distances are correct. At each sampled pair $a,a+\pi$, the two arc distances to any boundary point $s$ sum to $\pi$. The corresponding surface distances are bounded above by those two numbers and also sum to at least $\pi$. This gives the correct trace of every sampled $F_a$ on the whole boundary. Every original gap is isometrically embedded, since one of these traces varies at unit slope throughout the gap.

More generally, for a set of boundary parameters $E$, the following are equivalent.

1. Every pair in $E$ has its correct circle distance in $M$.
2. The sampled profiles can be extended to *all* angular labels by functions $G_t(x)$ which are separately 1-Lipschitz in $x,t$, satisfy $G_{t+\pi}=-G_t$, agree with every old $F_a$ on $M$, and have trace $\pi/2-d_{S^1}(s,t)$ at every $s\in E$.

For necessity use the label $t=s$ to test the distance from $s$ to another point of $E$. For sufficiency use the sum metric $d_M+d_{S^1}$ on $M\times S^1$. Prescribe the old values on $M$ times the anchor set (including antipodes) and the required boundary values on $\gamma(E)\times S^1$. Two prescribed values of the second type satisfy the Lipschitz inequality by the isometry on $E$. For a mixed pair, pass through the old anchor value at the boundary point, using its exact trace. Two old values satisfy the inequality by their spatial and angular Lipschitz properties. The real McShane extension $H(z)=\inf_y(H_0(y)+d(z,y))$ extends these jointly 1-Lipschitz data. Taking $G_t=(H(x,t)-H(x,t+\pi))/2$ preserves the prescribed values and gives antipodality.

In particular, separate extensions on each gap are possible even when a shortcut joins two opposite gap midpoints. An argument using only those Lipschitz properties and the traces on a single gap cannot distinguish the shortcut. A joint extension prescribing the traces on both endpoints would detect it immediately. This gives a specific reason to couple separated boundary arcs in a further calibration. At the level of actual metric fillings, one can also repair every missed shortcut at area cost at most $2\pi/n$ by replacing one semicircle. [Finite-test repair theorem](issue163_sampling.md)
