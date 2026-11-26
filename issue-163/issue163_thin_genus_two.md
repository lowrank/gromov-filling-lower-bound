# Where a genus-two counterexample could occur

Let $`N`$ be the nonorientable surface of genus five obtained by identifying antipodal boundary points of a genus-two isometric filling of the circle of length $`2\pi`$. Write $`A`$ for its area. Every orientation-reversing loop has length at least $`\pi`$. Let $`J`$ be its conformal structure and use the curvature $`-1`$ metric in $`J`$ to measure hyperbolic lengths. The following restrictions hold for **every** genus-two filling.

| If $`A\le6.15`$, every simple closed hyperbolic geodesic of this type | Has length greater than |
|---|---:|
| One-sided | $`0.987`$ |
| Two-sided, nonseparating | $`1.462`$ |
| Two-sided, separating | $`2.147`$ |

More generally, along **every** sequence leaving compact sets in genus-two quotient moduli,

~~~math
                  \liminf_{j\to\infty} A_j\ge 2\pi .
~~~

In particular, for each $`a\lt2\pi`$ it suffices to study a compact part of moduli to exclude $`A\le a`$. The compact part depends on $`a`$. A second estimate below gives the full hemisphere bound on neighborhoods obtained by adding a thin handle to *any fixed* quotient whose orientation double has genus two. It also gives explicit examples with only simple branch values. [Ordinary three-sheeted example](issue163_ordinary_cover.md) · [Distance constraint on the quotient](issue163_cyclic_companions.md) · [Rational checks](issue163_collar_surgery_check.py)

## Cutting a two-sided conformal cylinder

Write a conformal cylinder as $`[-M/2,M/2]\times(\mathbb R/\mathbb Z)`$. Its modulus is $`M`$. In these coordinates a filling metric has length element $`\rho(t,x)\sqrt{dt^2+dx^2}`$. Put

~~~math
    E(t)=\int_0^1\rho(t,x)^2\,dx,\qquad
    L(t)=\int_0^1\rho(t,x)\,dx,\qquad L(t)^2\le E(t).
~~~

Cut across two levels on opposite sides of the middle, discard the strip between them, and cap each exposed circle with a round hemisphere of circumference $`L(t)`$. Its area is $`L(t)^2/(2\pi)`$. Any path between equatorial points in the hemisphere costs at least the shorter equatorial arc. Replacing each cap excursion by such an arc therefore takes an orientation-reversing loop on the capped surface to one on the original surface at no extra length. The orientation local system on the retained part is the restriction of both orientation local systems and is trivial on each cap. Continuous seam metrics can be smoothed from above with arbitrarily small area change. [Details of the metric gluing](issue163_genus_reduction.md)

For a nonseparating two-sided core the capped surface has Euler characteristic $`-1`$, hence is nonorientable of genus three. Its orientation double has genus two and is hyperelliptic, so its area is at least $`2\pi`$ by the relative Pu theorem. For an essential separating core, retain an odd nonorientable component after capping. Its nonorientable genus is at most three because the other side does not cap to a sphere. Pu's theorem or the same hyperelliptic result applies. In this case one cut suffices and all the way to the far end of the collar can be discarded. [Bangert, Croke, Ivanov and Katz, Theorem 1.7](https://arxiv.org/pdf/math/0405583)

Here is the choice of cut that makes the error exponential. Suppose one has a strip parametrized from its discarded end by $`s\in[0,m]`$ and that a cut at $`s`$ costs at most $`E(s)/b`$. Discard the portion $`[0,s]`$. Choose the cut with probability density

~~~math
          p(s)=\frac{b e^{-bs}}{1-e^{-bm}} .
~~~

For each $`u\in[0,m]`$ the coefficient of $`E(u)`$ in expected cap cost minus discarded area is exactly

~~~math
           \frac{p(u)}b-\int_u^m p(s)\,ds=\frac1{e^{bm}-1}.
~~~

For the ordinary hemispheres use $`b=2\pi`$. In the nonseparating case apply the formula independently to the two halves with $`m=M/2`$. The sum of their actual areas is at most $`A`$. In the separating case use $`m=M`$ on the single strip, allowing the whole opposite component to be discarded. If $`P`$ denotes the lower bound on the capped area, the comparison gives $`P\le A+A/(e^{bm}-1)`$. Consequently

~~~math
 \begin{aligned}
 A&\ge 2\pi(1-e^{-\pi M})                 &&\text{for a nonseparating cylinder},\\[2pt]
 A&\ge 2\pi(1-e^{-2\pi M})                &&\text{for an essential separating cylinder}.
 \end{aligned}
~~~

For example, a nonseparating cylinder of modulus $`1.227`$ already gives $`A\gt6.15`$. The discarded strip pays most of the cap cost. Using only the shortest circumference selected by an area average would give an error of order $`1/M`$.

## From cylinders to compactness

A two-sided simple closed hyperbolic geodesic of length $`\ell`$ has a standard collar of half-width $`w`$ with $`\sinh w=1/\sinh(\ell/2)`$. The metric is $`du^2+\ell^2\cosh^2(u)\,dx^2`$ for $`x\in\mathbb R/\mathbb Z`$. Integration gives its modulus

~~~math
     M(\ell)=\frac2\ell\int_0^w\frac{du}{\cosh u}
            =\frac4\ell\arctan(e^{-\ell/2}).
~~~

One can apply the collar theorem on the orientation double, where disjoint lifts have disjoint standard collars. For a one-sided geodesic of length $`\ell`$ the lift has length $`2\ell`$. Its quotient collar is a conformal Möbius band. In longitude of period $`2\pi`$ on the orientation double its half-width is

~~~math
     H(\ell)=\frac{2\pi}{\ell}\arctan(e^{-\ell}).
~~~

The band alone contributes at least $`2\pi\tanh H(\ell)`$ by averaging round great semicircles contained in it. All three estimates decrease with $`\ell`$, and all tend to $`2\pi`$ as $`\ell`$ tends to zero. Substitution gives the table. The nonorientable Mumford compactness criterion then gives the claimed lower limit. [Buser, *Geometry and Spectra of Compact Riemann Surfaces*, Chapter 4](https://link.springer.com/book/10.1007/978-0-8176-4992-0) · [Proof of the Möbius band estimate](issue163_conformal_program.md#a-curve-family-test-in-every-genus) · [Matthiesen and Siffert, section 2 on nonorientable compactness](https://ems.press/content/serial-article-files/33827)

For precision, define $`P(J)`$ as the infimum of area among metrics in $`J`$ for which every orientation-reversing loop costs at least $`\pi`$. It is continuous in moduli. A marking of conformal distortion $`K`$ transports a metric by taking the larger length singular value as the conformal density. This dominates all lengths and increases area by at most a factor $`K`$. Applying the same argument to the inverse gives continuity. Thus if the infimum of $`P(J)`$ over genus-five nonorientable conformal structures is below $`2\pi`$, some interior conformal structure attains that infimum as a value of $`P`$. Existence of a smooth minimizing density in that class is a separate question.

## Keeping the conformal structure of the capped surface

The round cap above uses arclength to identify its boundary. To retain the *prescribed* conformal structure of a reference surface $`Y`$, consider a round coordinate disk on $`Y`$. Its boundary has angular length density $`f(\theta)`$ in the given metric. Put $`c=(2\pi)^{-1}\int f`$ and $`G(\theta)=c^{-1}\int_0^\theta f(v)\,dv`$. Map the unit disk to the round hemisphere of radius $`c`$ in stereographic coordinates by $`(r,\theta)\mapsto(r,G(\theta))`$. Its pullback is dominated by the conformal length element

~~~math
             \frac{2\max(c,f(\theta))}{1+r^2}\,|dz|.
~~~

The boundary trace in the target has the desired arclength parametrization. Thus the cap preserves the excursion comparison. Its area is $`\int_0^{2\pi}\max(c,f)^2d\theta`$. For $`v=f/c`$ the pointwise inequality

~~~math
      \max(1,v)^2\le\tfrac43(v^2-v+1),\qquad v\ge0
~~~

follows by completing a square separately on each side of one. Since $`v`$ has mean one, the new cap costs at most $`(4/3)\int f^2d\theta`$. In the cylinder coordinates this is $`E(s)/b`$ with $`b=3\pi/2`$. At the boundary the cap density can exceed the old density and at its center it can depend on angle. For smooth input the densities are bounded near those sets at each fixed cut. Dominate both one-sided values across a shrinking seam collar and use a constant upper bound on a shrinking central disk, then smooth the density from above with area error tending to zero. The target comparison holds for capped excursions even when their endpoints touch the original seam.

**Conformal embedding estimate.** Choose any finite set of disjoint coordinate disks of radius one on a closed nonorientable reference surface $`Y`$. Suppose a surface $`N`$ with the orientation-reversing length bound contains a conformal copy of $`Y`$ with the inner open disks of radius $`r`$ deleted, $`0\lt r\lt1`$. Its complement in $`N`$ can have any topology. Then

~~~math
       \mathrm{Area}(N)\ \ge\ (1-r^{3/4})\,P(Y).
~~~

Indeed, each retained annulus has modulus $`m=(2\pi)^{-1}\log(1/r)`$. Measure the cut distance from its inner end and cap on the original coordinate disk, using the density just constructed. All capped surfaces have the conformal structure of $`Y`$. Sum the random-cut comparison over the disjoint annuli. Their total area is at most $`A`$, independently of how many holes were made, giving $`P(Y)\le A/(1-e^{-bm})`$. This proves the estimate.

In particular every fixed conformal $`Y`$ of nonorientable genus three has $`P(Y)\gt2\pi`$ by the strict hyperelliptic comparison. For all sufficiently small $`r`$, inserting an arbitrary handle or other surface inside the deleted disks therefore preserves the full $`2\pi`$ bound. If the embedding has conformal distortion $`K`$, the same proof uses the larger length singular value on the embedded part and gives $`A\ge(1-r^{3/4})P(Y)/K`$. This also covers marked deformations of the retained component. [Strict estimate for each genus-two orientation double](issue163_cyclic_companions.md#strictness-for-the-transferred-genus-two-double)

## Which degenerations can approach equality?

Suppose only a two-sided simple hyperbolic geodesic pinches and the remaining components converge smoothly on compact subsets after punctures are filled in conformally. The limit has a component obtained from a fixed $`Y`$ of nonorientable genus three by deleting one or two points. For a nonseparating curve this follows by Euler characteristic. For a separating curve the odd component could only have genus one or three. A genus-one nonorientable component with a single end would be a Möbius band, whose boundary cannot be an embedded hyperbolic geodesic because it represents the square of its one-sided core. For each fixed $`r`$ the punctured-disk comparison now applies with distortion tending to one. Sending $`r`$ to zero proves $`\liminf A_j\ge P(Y)\gt2\pi`$.

If a single one-sided curve pinches and its remaining fixed limit is nonorientable, a compact region of that component contains another Möbius band of positive conformal width. One can use a narrower part of the pinching collar still of width tending to infinity and disjoint from this compact band. The two disjoint band estimates then have sum strictly above $`2\pi`$ in the limit. These statements give extra exclusions within the thin part when the remaining components stay fixed.

The unrestricted lower limit $`2\pi`$ along degeneration is sharp. Remove a round disk of small spherical radius $`\varepsilon`$ from the projective plane. Replace it by a copy of a fixed orientable genus-two surface $`S`$ with one isometrically embedded boundary circle of length $`2\pi`$, scaling its lengths by $`\sin\varepsilon`$. Such an $`S`$ can be made with a flat product collar longer than $`\pi/2`$ attached to any genus-two interior. Every excursion through the replacement can be sent to the old seam without increasing length, and its orientability preserves the orientation character. The round one-sided equator still has length $`\pi`$. Cutting along it gives an actual genus-two filling: a shortcut on the doubled boundary would extend along that boundary to an antipodal shortcut and hence to an orientation-reversing loop shorter than $`\pi`$. Its area before arbitrarily small seam smoothing is

~~~math
                  2\pi\cos\varepsilon+\sin^2\varepsilon\,\mathrm{Area}(S)
                  \ \longrightarrow\ 2\pi .
~~~

The round Möbius belt outside the removed disk has conformal width tending to infinity. Its double is an annulus of unbounded modulus. Applying horizontal-circle Cauchy–Schwarz to the uniformizing hyperbolic metric, whose total area is fixed, gives a representative of the squared core of length tending to zero. The characteristic one-sided hyperbolic geodesic therefore pinches. Smoothing can be confined to the seam while retaining a slightly narrower round belt of diverging width.
