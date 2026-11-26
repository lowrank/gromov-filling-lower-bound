# What the rest of a filling must pay outside a spherical belt

Suppose the antipodal quotient of a circle filling contains an embedded **characteristic** conformal Möbius band. This means that removing the open band leaves an orientable surface $`Y`$ with one boundary component. Its genus is arbitrary. Identify the band with the unit spherical belt $`|z|\le H`$ modulo antipodes, where $`0\lt H\lt1`$, and put $`s=\sqrt{1-H^2}`$. Write $`r`$ for the physical length factor on the belt relative to round lengths.

If the belt is isometrically round, the whole filling satisfies

~~~math
                  A\ \ge\ 2\pi-\pi(1-H)^2 .
~~~

In particular $`H=0.8`$ gives $`A\gt6.1575`$, although the belt alone has area $`1.6\pi`$. For $`H`$ sufficiently close to one, the whole area is at least $`2\pi`$. There is also an explicit estimate under a one-sided metric error. For $`H=0.9`$ and $`r\le1.02`$ it gives $`A\gt6.1579`$. These estimates require geometric information about the physical belt. [Rational checks](issue163_sewn_cylinder_check.py) · [Conformal band estimates](issue163_conformal_program.md#a-curve-family-test-in-every-genus)

## Transferring a distance inequality to the complement

Represent each boundary point by its upper spherical lift $`p`$ at height $`H`$. Write $`d(p,q)`$ for its spherical distance from another such lift. The short spherical arc lies in the northern cap. The arc continuing from $`p`$ away from the cap to $`-q`$ has length $`\pi-d(p,q)`$ and lies in the band. Let $`L(p,-q)`$ be the infimum of physical lengths of paths in the double of the band between those points. Concatenating such a path with any return path in $`Y`$ gives an orientation-reversing loop. Indeed the orientation double has two copies of the orientable complement, attached at opposite ends of the band cylinder. Therefore

~~~math
                  d_Y(p,q)\ \ge\ \pi-L(p,-q).
~~~

For a round belt this gives $`d_Y(p,q)\ge d(p,q)`$. The spherical cap is geodesically convex and its boundary distances are exactly $`d`$. Projection of its boundary to the horizontal plane gives a Euclidean circle of radius $`s`$ with chords of length at most $`d`$. Each of the two Cartesian coordinates on this circle extends to a real 1-Lipschitz function on $`Y`$ by the infimum extension formula. The resulting map to the plane has absolute Jacobian at most one. Its boundary winds once around the disk of radius $`s`$, so its area counted with multiplicity is at least $`\pi s^2`$ by degree and the area formula. Adding the belt area $`2\pi H`$ proves the first estimate.

For small caps the Burago–Ivanov minimal-filling theorem gives the whole spherical cap area $`2\pi(1-H)`$ on $`Y`$. In geodesic normal coordinates on the unit disk, a cap of angular radius $`\alpha=\arccos H`$, rescaled by $`1/\alpha`$ in lengths, has metric $`dt^2+(\sin(\alpha t)/\alpha)^2d\theta^2`$. It tends to the Euclidean metric in $`C^2`$ in Cartesian coordinates as $`\alpha\to0`$. The theorem allows orientable competitors of any topology and only requires domination of boundary distances. This gives the stated $`2\pi`$ conclusion for a sufficiently wide isometrically round belt, with a nonexplicit threshold. [Burago and Ivanov, Theorem 1](https://annals.math.princeton.edu/2010/171-2/p10) · [Cossarini’s spherical cap observation, Chapter 3](https://w3.impa.br/~mbel/tese/MarcosCossarini-Tese-2018.pdf)

## Measuring the extra length that can hide a shortcut

More generally, suppose $`d_Y(p,q)\ge t\,|p-q|-\delta`$ for all upper boundary points, with $`|\cdot|`$ the Euclidean chord, $`t\ge0`$ and $`\delta\ge0`$. For each Cartesian coordinate $`f`$ of the planar circle of radius $`ts`$, the function

~~~math
              F(x)=\inf_{q\in\partial Y}\bigl(f(q)+d_Y(x,q)\bigr)+\delta/2
~~~

is 1-Lipschitz and differs from $`f`$ on the boundary by at most $`\delta/2`$. The two extensions together move each boundary point by at most $`\delta/\sqrt2`$. Straight-line homotopy preserves boundary winding around the open disk of radius $`(ts-\delta/\sqrt2)_+`$. The same Jacobian and degree argument gives its Euclidean area as a lower bound on $`Y`$.

For arbitrary physical density $`r`$, define

~~~math
  \delta=\sup_{p\ne q}\bigl[L(p,-q)-(\pi-d(p,q))\bigr]_+ .
~~~

The distance inequality above applies with $`t=1`$. The band path average also gives the squared deviation of $`r`$ from one. Together these imply

~~~math
  A\ \ge\ 2\pi H+\int_B(r-1)^2\,dA_{\rm rd}
                       +\pi\bigl(s-\delta/\sqrt2\bigr)_+^2 .
~~~

Consequently, at $`H=0.9`$, any filling of area at most 6.15 must have $`\delta\gt0.055`$. Some pair forces even the **shortest** permitted path in the band to be more than 0.055 longer than its round counterpart. This conclusion uses no pointwise closeness assumption.

If $`r\le1+\varepsilon`$, the comparison great-circle arc gives $`L(p,-q)\le(1+\varepsilon)(\pi-d(p,q))`$. Use $`t=1+\varepsilon`$ and $`\delta=\pi\varepsilon`$ in the extension argument. Thus

~~~math
 A\ \ge\ 2\pi H+\int_B(r-1)^2\,dA_{\rm rd}
        +\pi\left((1+\varepsilon)\sqrt{1-H^2}
                          -\frac{\pi\varepsilon}{\sqrt2}\right)_+^2 .
~~~

This proves the two-percent example. Passing from the available area control on $`r-1`$ to an upper bound on the shortest-path surplus for arbitrary fillings remains open.
