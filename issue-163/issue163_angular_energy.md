# A strict all-genus gain from unsampled antipodal distances

Let $A$ be the infimum of areas of compact connected orientable Riemannian surfaces of arbitrary genus with one isometrically embedded boundary circle of length $2\pi$. Let $B$ denote the exact bound from the bisected gaps. Then

```math
 B=\frac{737877064811692678202731938521}{1194666547200000000000000000000}\pi^2,
 \qquad A\ge B+2^{-1372}.
```

The gain has no effect on the first 18 decimal places of $B$. Its source is the Dirichlet energy required to extend the traces of two shifted families of true distance functions. There is also a quantitative limit. Even with the best possible *uniform* allocation of the diagonal budget to this energy, the gain at every shift is less than $2\times10^{-25}$. In a separate smooth disk construction all 112 sampled antipodal distances are correct and an unsampled pair has a shortcut. [Bisected-gap proof](issue163_midpoint.md) · [Smooth disk example](issue163_sampled_disk.md)

## Keeping the energy of the angular difference

Parameterize the boundary by arclength $\gamma(t)$. For $`0\lt \varepsilon\le\pi/2`$ define

```math
 F_t(x)=\tfrac12\big(d_M(x,\gamma(t+\pi))-d_M(x,\gamma(t))\big),\qquad
 P_t=\tfrac12(F_{t+\varepsilon}+F_{t-\varepsilon}),\qquad
 Q_t=\tfrac12(F_{t+\varepsilon}-F_{t-\varepsilon}).
```

The spatial gradients satisfy $`|\nabla P_t|^2+|\nabla Q_t|^2\le1`$ by the parallelogram identity. The angular profile $`t\mapsto P_t(x)`$ is still antiperiodic and 1-Lipschitz. Apply the old calibration to the $n=112$ samples of $P$ on a grid of offset $v$. Its normalized diagonal certificate has, at every reached cell, weights satisfying

```math
 \sum_j D_j\le1,\qquad D_j\ge\frac{1}{16n}.
```

The original weighted diagonal and trace witnesses give this additional lower bound by direct integer comparison on 214,058 terminal cells. Inheritance halves each parent diagonal when the number of samples doubles, preserving the displayed floor. The three replacement diagonals at the bisected corner pass the same comparison. On scalar facets choose an incident cell from the finite coverage. Each coordinate pinned to a facet has zero spatial differential almost everywhere there, so its bin choice leaves the evaluated form unchanged. The bounds on the diagonal still apply to every index. Ties in the minima defining the tents are handled by equality of the differentials on the tie set. [Finite hierarchy](issue163_free_field.md) · [Corner witnesses](issue163_midpoint.md)

If $`\omega_v(P)`$ denotes the normalized form at this offset, the Hermitian certificate bounds its evaluation on a positively oriented orthonormal frame by $`\sum_j D_j|\nabla P_{v+j\pi/n}|^2`$. It follows pointwise almost everywhere that

```math
 \omega_v(P)\le
 \left(1-\frac{1}{16n}\sum_{j=0}^{n-1}|\nabla Q_{v+j\pi/n}|^2\right)dA .
```

Write $J(\varepsilon)$ for its boundary action. It is independent of $v$ by rotating the boundary parameter. On the boundary $`F_t(\gamma(\theta))=b(\theta-t)`$, where $`b(s)=\pi/2-d_{S^1}(s,0)`$. The trace of $`P_t`$ is this triangle wave clipped to the interval $[-\pi/2+\varepsilon,\pi/2-\varepsilon]$. Integrating the last inequality in space and averaging the offsets gives

```math
 \mathrm{Area}(M)\ge J(\varepsilon)+
 \frac1{16}\int_M\frac{1}{2\pi}\int_0^{2\pi}|\nabla Q_t|^2\,dt\,dA .
```

## What the full boundary forces

Take the real angular Fourier coefficients $`a_k(x),b_k(x)`$ of $`Q_t(x)`$ with normalization $1/\pi$. They are Lipschitz in space and weak differentiation commutes with the angular integral. Bessel's inequality bounds the averaged energy below by the sum of $`\tfrac12\int_M(|\nabla a_k|^2+|\nabla b_k|^2)`$. On the boundary the triangle wave has cosine coefficient $4/(\pi k^2)$ at each odd positive $k$, as follows by integrating its two linear pieces. Hence

```math
 (a_k,b_k)(\gamma(\theta))=
 \frac{4\sin(k\varepsilon)}{\pi k^2}(\sin k\theta,-\cos k\theta)
 \qquad(k\text{ odd}).
```

This circle has signed area $\pi k$ times its squared radius. Stokes gives that area as $`\int_M da_k\wedge db_k`$, which is at most the $k$-th Dirichlet energy above. Summing finite sets of odd modes and taking the limit proves, in every genus,

```math
 A\ge J(\varepsilon)+\tfrac1{16}E(\varepsilon),\qquad
 E(\varepsilon)=\frac{16}{\pi}\sum_{k\ge1,\ k\text{ odd}}
       \frac{\sin^2(k\varepsilon)}{k^3}.
```

The full isometric boundary supplies the winding of every coefficient map. The calculation uses arbitrarily many angular labels and requires only a one-variable integral to evaluate the series.

## Exact loss at a clipped vertex

Write $h=\pi/n$, $R=h/2$ and $U=999999900000/10^{12}$. For $`0\lt \varepsilon\lt h/8`$, interpolate linearly from the original boundary trace to the clipped one. In the $\varepsilon$-neighborhood of a vertex just one coordinate moves. In the signed frame of the preceding gap, at distance $r$ before its right endpoint, all offsets from the gap center previously equaled $R-r$. The peak coordinate decreases by at most $\varepsilon-r$. The two extreme offsets stay positive with sum greater than $R$. Thus this entire half of the ribbon uses the last child matrix, except on the edge of zero two-dimensional measure. In the previous note's notation its matrix is $`Y=W-e_{n-1}\wedge(s+Ju)`$, where $J$ in this expression reverses the indices and $Js=s$.

Use $`Z=(Y\mathbf 1)_0=(W\mathbf 1)_0+s_0+u_{n-1}`$. Evaluating the form on the interpolation direction and boundary tangent gives $-Z(\varepsilon-r)/U$. The next half-ribbon has the same loss by reflection. There are $2n$ vertices, so the boundary action is exactly

```math
 J(\varepsilon)=B-C\varepsilon^2,\qquad
 C=\frac{2nZ}{U}
 =\frac{378039744062792675747566367741}{4999999500000000000000000000}
 =75.60795637335\ldots .
```

The signed energy wins at sufficiently small shifts because it contains a logarithm. Indeed twice differentiating the series for $\pi E/16$ on $`0\lt t\lt \pi/2`$ gives $`2\sum_{k\ \mathrm{odd}}\cos(2kt)/k=\log\cot t`$. This follows by taking real parts of the power series for $\log((1+z)/(1-z))$ and taking radial limits. The derivative series after one differentiation converges uniformly. The cosine series after two differentiations converges uniformly on compact intervals in the open range by Dirichlet's test. The value and first derivative at zero vanish, and the logarithm is integrable there. Consequently

```math
 E(\varepsilon)=\frac{16}{\pi}\int_0^{\varepsilon}(\varepsilon-t)\log\cot t\,dt .
```

For $`0\lt t\le1/4`$, one has $`\cos t\ge31/32\gt e^{-1/16}`$ and $\sin t\le t$. Integration yields

```math
 \tfrac1{16}E(\varepsilon)\ge
 \frac{\varepsilon^2}{2\pi}\left(\log(1/\varepsilon)+\frac{23}{16}\right)
 \qquad(0<\varepsilon\le1/4).
```

Choose $\varepsilon=2^{-684}$. The first four terms of $`2\sum_{j\ge0}3^{-(2j+1)}/(2j+1)`$ give $`\log 2\gt 6931/10000`$. With $`\pi\lt 355/113`$, the coefficient on the right exceeds $C+1/16$. This proves the stated gain $2^{-1372}$.

## A ceiling over all shifts

Consider the expression $J(\varepsilon)+aE(\varepsilon)$ for a uniform coefficient $0\le a\le1$. Trace at most one forces this upper limit on the fraction of diagonal allocated uniformly. For $`0\lt \varepsilon\lt h/8`$, the inequality $\cot t\le1/t$ gives

```math
 J(\varepsilon)+aE(\varepsilon)-B
 \le\varepsilon^2\left[\frac8\pi
 \left(\log(1/\varepsilon)+\tfrac32\right)-C\right]
 \le\frac4\pi\exp(2-\pi C/4).
```

The final number is about $1.53\times10^{-25}$. The last inequality maximizes the preceding elementary expression in $\varepsilon$. For an exact upper bound, $`\pi C/4-2\gt 57+1/4`$ and $`e^{57+1/4}\gt (1957/720)^{57}(5/4)\gt (2/3)10^{25}`$. Together with $`\pi\gt 3`$ this gives $2\times10^{-25}$.

For the intermediate shifts $h/8\le\varepsilon\le h$, a ribbon in each gap changes at most the first and last coordinates. Write $e=n-1$ and use $`b_i`$ for the $i$-th coordinate vector. At signed arclength $t\in[-R,R]$ from the gap center set

```math
 p=(t-R+\varepsilon)_+,\quad q=(-R+\varepsilon-t)_+,\quad
 v=-p b_0+q b_e,\quad H(t,\lambda)=c+t\mathbf 1+\lambda v,\quad 0\le\lambda\le1 .
```

The interior of this ribbon stays in the old pair cell. Indeed its offsets are between $-R$ and $R$ and are ordered. Only this gap's tents can be positive there. For each of its three unreflected matrices $Y$, exact row comparisons give

```math
 (Y\mathbf 1)_0-\max(0,Y_{0e})>U/8,\qquad
 -(Y\mathbf 1)_e-\max(0,Y_{0e})>U/8 .
```

Reflection $Y\mapsto-JYJ$ interchanges the comparisons. The unnormalized form on $`(\partial_\lambda H,\partial_t H)`$ equals $`-p(Y\mathbf 1)_0+q(Y\mathbf 1)_e+\lambda(-pq'+qp')Y_{0e}`$. The coefficient of $`Y_{0e}`$ lies between zero and $p+q$. Thus the normalized evaluation is at most $-(p+q)/8$. On each gap $`\int(p+q)\,dt=\varepsilon^2`$, proving $J(\varepsilon)\le B-28\varepsilon^2$. Meanwhile $`\log(1/\varepsilon)\le\log(896/\pi)\lt 6`$ gives $`E(\varepsilon)\lt 20\varepsilon^2`$. The bound on this entire interval is strictly below $B$.

For $h\le\varepsilon\le\pi/2$ all tents vanish. In a pair projection, clipping both coordinates restricts the original boundary polygon to the square of half-width $\pi/2-\varepsilon$ for the action integral. Indeed coordinatewise clipping has Jacobian one inside that square and zero outside. At clipping depth $mh$, exactly the original positive-area cells with $\min(i,j,111-i,111-j)\ge m$ survive, with $i,j$ the two scalar bin indices. Between successive integer depths, keep the positive contributions at the shallower depth and the negative contributions at the deeper one. Orbit symmetry preserves the ring index and the coefficient sign.

For an interval ending at $t=j\pi/n$, bound $E$ by the minimum of the following three rationally enclosable quantities,

```math
 44\pi j^2/n^2,\qquad 8j/n+4\pi j^2/n^2,\qquad (16/\pi)(115/108).
```

For the first two, the integral majorant $(8/\pi)t^2(3/2-\log t)$ is increasing up to $\pi/2$. At these endpoints $`\log(1/t)\lt 4`$ and $\log(1/t)\le1/t-1$. For the third, bound the odd reciprocal-cube sum by $`1+1/27+\int_1^\infty(2x+1)^{-3}dx=115/108`$. Each of the 55 resulting interval bounds is below $6.086$. Combining the three shift ranges proves the stated ceiling on uniform splitting. An estimate assigning more energy to particular profiles or angles would require a separate argument.

## A geometric test for any candidate below 6.15

There is another way to use shortest paths that incurs zero clipping cost. On the original grid write $`r_t=d_M(\cdot,\gamma(t))`$ and $`H_t=(r_t+r_{t+\pi}-\pi)/2`$. The function $H_t$ is half the excess length of a shortest route from one anchor to its antipode constrained to pass through the given point. It vanishes on the boundary. At almost every interior point both distance gradients have norm one. Consequently

```math
 |\nabla F_t|^2+|\nabla H_t|^2=1,\qquad
 |\nabla H_t|^2=\tfrac12\big(1+\langle\nabla r_t,\nabla r_{t+\pi}\rangle\big).
```

Use the normalized diagonal for the original bisected field at each point. For any fixed rotation of the grid set $`T=\int_M\sum_jD_j\,dA`$. The original comass proof then gives

```math
 B+\int_M\sum_jD_j|\nabla H_{t_j}|^2\,dA\le T\le\mathrm{Area}(M).
```

Normalize the measure $`D_j\,dA`$ on point-index pairs by $T$. Every filling of area below $6.15$ must satisfy

```math
 \mathbb E\langle\nabla r_{t_j},\nabla r_{t_j+\pi}\rangle
 \le-1+2\frac{\mathrm{Area}(M)-B}{B}<-0.98224.
```

In particular the angle between the two minimizing directions can be $120$ degrees or less on at most $3.551$ percent of this weighted measure. There the squared excess gradient is at least $1/4$. This gives an explicit test for a prospective geometric realization of a near extremizer. The angle bound gives a geometric constraint in every genus.

A second constraint follows from geodesic flow. Let $`G=\{t:H_t\equiv0\}`$ and use arclength for its measure. For every such filling,

```math
 |G|\le\mathrm{Area}(M),\qquad
 |\{t:H_t\not\equiv0\}|\ge2\pi-\mathrm{Area}(M).
```

To prove this, let $a=\gamma(t)$ for $t\in G$ and start a strictly inward unit geodesic at $a$. Its sufficiently short initial segment to $x$ minimizes. A shortest continuation from $x$ to the antipode has length $\pi-d_M(a,x)$, by the definition of $G$. The concatenation minimizes and is the original geodesic as long as it stays in the interior. If it first hits the boundary before time $\pi$, the hit must be tangential. Indeed the segment to that point followed by the shorter boundary arc to the antipode also minimizes. A transverse corner with this arc can be shortened inside a smooth boundary chart.

Incoming directions whose orbits encounter a tangency have zero boundary flux measure. In a smooth extension the flowout of the boundary-tangent unit vectors has dimension at most two inside the three-dimensional unit tangent bundle. Local transverse flow coordinates then give the asserted null set of incoming directions. Hence for almost every incoming direction based over $G$ the orbit spends time $\pi$ inside the surface. Before the first exit, incoming phase point and elapsed time parametrize the reached unit vectors injectively. Liouville volume in these coordinates is $`\cos\alpha\,dt\,d\alpha\,d\ell`$, where $\alpha$ is the entry angle from the inward normal and $\ell$ is elapsed time. Integrating over $G$ and $`-\pi/2\lt\alpha\lt\pi/2`$ gives $2\pi|G|$. The whole unit tangent bundle has volume $`2\pi\,\mathrm{Area}(M)`$. This one-sided use of the geodesic-flow integral also allows trapped directions. [Santaló formula and boundary flux, Guillarmou–Mazzucchelli–Tzou, Lemma 3.3](https://www.imo.universite-paris-saclay.fr/~colin.guillarmou/papernonconvex.pdf)

More quantitatively, let $\tau$ be first boundary return time and normalize incoming flux to probability by dividing by $4\pi$. Integrating the same flow coordinates up to $\min(\pi,\tau)$ gives

```math
 \mathbb E_{\mathrm{flux}}(\pi-\tau)_+
 \ge \pi-\tfrac12\mathrm{Area}(M).
```

Thus area below $6.15$ forces a mean early-return shortfall above $0.06659$ and positive excess for a set of angular labels of length greater than $0.13318$, while the squared excess gradients have the small weighted integral above. The round hemisphere has zero excess for every label. A quantitative lower bound on the energy cost of these early returns could connect the two estimates. The present argument controls their mean shortfall.

## Replay

From the repository's <code>issue-163</code> directory, run

~~~sh
node issue163_angular_energy.cjs issue163_inputs
node issue163_free_field.cjs issue163_inputs
node issue163_midpoint.cjs issue163_inputs
~~~

The first command checks the rational corner cost, the positive logarithmic gain the two-coordinate ribbon inequalities and the 55 interval ceilings. The other two replay the finite certificates with the extra diagonal floor. The spatial energy and Stokes arguments above are analytic proofs. The repository's [Lean theorem](../docs/current-manuscript.md) concerns the earlier Fourier result.
