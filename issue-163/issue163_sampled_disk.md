# A smooth disk in which the sampled distances miss a shortcut

For $n=112$ equally spaced tested antipodal pairs there are smooth Riemannian disks of boundary length $2\pi$ with all 112 tested distances exactly $\pi$, area below $6.26430$, and two unsampled antipodal boundary points at distance less than $\pi-0.0116$. For $n=15$ the same construction even gives area below $6.15$. These examples realize the sampling defect in genuine surfaces. The status of the optimizing profiles in the 112-point lower-bound certificate remains open. [Finite-test repair estimate](issue163_sampling.md) · [Unconditional lower bound using the full boundary](issue163_angular_energy.md)

## A metric preserving finite distance witnesses

On the unit hemisphere use longitude $\theta$ and height $z$. Put $h=\pi/n$ with $n\ge3$. For an equatorial anchor $a$, set $`f_a=\pi/2-d_{\rm round}(\cdot,a)`$. Preserving $`|df_a|\le1`$ and the round boundary arclength suffices to preserve the tested distance to its antipode, because the two boundary values differ by $\pi$. The covectors for antipodal anchors have opposite sign.

At an interior point the $`df_a`$ have round norm one. In a round orthonormal frame a representative at angular displacement $\delta=a-\theta$ is proportional to $(\sin\delta,-z\cos\delta)$. For $`z\gt 0`$ this linear transformation of the angular directions preserves projective cyclic order up to the choice of frame. Suppose the two successive anchors straddling the longitude are at displacements $-s,h-s$, where $`0\lt s\lt h`$. Their angular gap in the circle of unoriented covector lines exceeds $\pi/2$ precisely when

```math
 0<z<z_c(s),\qquad z_c(s)=\sqrt{\tan s\tan(h-s)} .
```

Indeed the dot product has the sign of $z^2\cos s\cos(h-s)-\sin s\sin(h-s)$. All other consecutive gaps are acute. Their displacements can be chosen in $[0,\pi]$, so their sine product is nonnegative. If their cosine product is negative, its coefficient $z^2\le1$ bounds the dot product below by $`\cos h\gt 0`$. The order of the lines identifies which projective gap the dot product tests.

In this open region let $v,w$ be the two extremal unit covectors with signs chosen so that the complementary cone between them is acute. All the sampled lines have representatives in this cone. Replace the round metric $g$ there by

```math
 g'=v\otimes v+w\otimes w .
```

For any sampled covector in the cone write it as $a v+b w$ with $a,b\ge0$. Its squared round norm is $1=a^2+b^2+2ab\langle v,w\rangle$, so its squared dual norm for $g'$ is $a^2+b^2\le1$. The area density of $g'$ relative to $g$ is $`|v\wedge w|\lt 1`$. At height $`z_c(s)`$ the two covectors are perpendicular and $g'=g$.

This tensor minimizes area pointwise among metrics preserving the same finite covectors. In the acute cone, $v,w$ must each have dual norm at most one, which gives the lower area density $|v\wedge w|$. Outside those regions all projective gaps are at most $\pi/2$. Doubling the line angles puts their directions around a full circle with no gap exceeding $\pi$, so their convex hull contains the origin. Weights $`\lambda_i\ge0`$ with $`\sum_i\lambda_i=1`$ then give $`\sum_i\lambda_i v_i v_i^T=I/2`$ in round coordinates. For any other inverse metric $Q$ satisfying $`v_i^TQv_i\le1`$, averaging gives $\mathrm{tr}(Q)\le2$ and hence $\det Q\le1$. The round area is optimal there.

Use $g$ outside the indicated regions. To obtain smooth metrics all the way to the equator choose smooth cutoffs $0\le\chi\le1$ supported compactly inside their union, tending to one on compact subsets, and use $(1-\chi)g+\chi g'$. Both tensors dominate $`df_i\otimes df_i`$ for each tested anchor, and this inequality is convex. Thus every $`f_i`$ remains 1-Lipschitz. Each smooth metric agrees with the round metric near the boundary. Since $g'\le2g$, dominated convergence gives the limiting area and the limiting length of the meridian used below. Strict inequalities for the limits hold on all sufficiently close smooth disks.

## The missing antipodal distance

Choose the opposite midpoints of two unsampled gaps. The round meridian joining them through the pole has length $\pi$. Put $R=h/2$ and measure latitude $\alpha$ from the equator along this meridian. The modified region ends at $`\alpha_*=\arcsin(\tan R)`$. On it the round distances to the two neighboring anchors both equal $d(\alpha)=\arccos(\cos R\cos\alpha)$. The new length element is $`\sqrt2\,d'(\alpha)\,d\alpha`$. Its coefficient is strictly below one for $`0\lt \alpha\lt \alpha_*`$ because $`\cos^2R\sin^2\alpha\lt \sin^2 R`$. The limiting meridian therefore saves the positive length

```math
 2\left[\arcsin(\tan R)
  -\sqrt2\left(\arccos\sqrt{\cos h}-R\right)\right].
```

Here $d(0)=R$ and $`\cos d(\alpha_*)=\sqrt{\cos h}`$. The factor two accounts for the two ends of the meridian. At $n=112$ the saving is about $0.01161958292$. This one path suffices to witness a shorter intrinsic distance.

## The area of the disks

The round area removed per gap is $`\int_0^h z_c(s)\,ds`$, since round area in longitude and height is $`d\theta\,dz`$. In the new metric use the two distances $u,v$ to the neighboring anchors as coordinates. The upper hemisphere maps injectively in the open region since the two cosines determine its equatorial projection. The spherical triangle inequalities describe the image there by

```math
 0<u<h,\qquad h-u<v<\arccos(\cos h/\cos u).
```

Indeed the lower edge lies on the equator, and the obtuse-angle condition is $`\cos u\cos v\gt \cos h`$. Conversely these inequalities give a nondegenerate spherical triangle of sides $u,v,h$ with obtuse angle opposite $h$, realized on the upper side of the equator. The other two triangle angles are acute by the spherical cosine rule since $`\cos v\gt \cos h\cos u`$ and $`\cos u\gt \cos h\cos v`$. Thus the longitude lies between the two anchors. The area element is $`du\,dv`$. With $2n$ gaps the limiting area is

```math
 S_n=2\pi-2n\int_0^h\left[
 \sqrt{\tan s\tan(h-s)}
 -\arccos(\cos h/\cos s)+h-s\right]ds .
```

An elementary enclosure suffices for the strict upper bounds. Since $\tan s\ge s$, the removed round area is at least $\pi h^2/8$. The region before subtracting the triangle $`u+v\lt h`$ lies in a quarter disk of squared radius $-2\log\cos h$, since $-2\log\cos t\ge t^2$. Also $\tan v/v$ increases, so for $0\le t\le h$,

```math
 \tan t=t+\int_0^t\tan^2 v\,dv
 \le t+\frac{t^3}{3}\left(\frac{\tan h}{h}\right)^2,
 \qquad -2\log\cos h\le h^2(1+\tan^2 h/6).
```

Subtracting the triangle of area $h^2/2$ bounds the area put back in. It follows that

```math
 S_n\le2\pi-\frac{2\pi^2}{n}
 \left(\frac12-\frac{\pi}{8}-\frac{\pi}{24}\tan^2(\pi/n)\right).
```

In particular the loss has leading term $\pi^2(1-\pi/4)/n$ as $n$ grows. This also follows directly in the integral by rescaling $s/h$ and using $\tan s=s(1+O(h^2))$ and $\arccos(\cos h/\cos s)=\sqrt{h^2-s^2}(1+O(h^2))$ uniformly.

| Tested antipodal pairs | Limiting disk area, numerical | Certified upper bound on limiting area | Certified meridian saving, rounded down |
|---:|---:|---:|---:|
| 14 | 6.13131279 | 6.141511807 | 0.093423371 |
| 15 | 6.14150827 | 6.149765585 | 0.087137766 |
| 56 | 6.24535417 | 6.245508768 | 0.023244676 |
| 112 | 6.26427314 | 6.264292440 | 0.011619577 |

The last two columns use directed integer bounds on trigonometric functions. The middle numerical estimate uses a 256-panel one-dimensional Simpson integral after the change of variables $s=(h/2)(1-\cos t)$. Run the checker from the repository's <code>issue-163</code> directory.

~~~sh
node issue163_sampled_disk.cjs
~~~
