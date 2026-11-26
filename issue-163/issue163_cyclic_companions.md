# The hemisphere bound for cyclic trigonal doubles in genus two

**Theorem.** Let $`M`$ be a genus-two orientable Riemannian filling of the intrinsic circle of length $`2\pi`$. Identify antipodal boundary points, write $`N`$ for the quotient, and let $`(X,\tau)`$ be its orientation double with its induced conformal structure. If $`X`$ has a holomorphic cyclic map of degree three to the sphere, then

~~~math
                 \mathrm{Area}(M)\ge 2\pi .
~~~

The metric can vary arbitrarily in the conformal class. The map itself can be exchanged with a different trigonal map by $`\tau`$. In fact every fixed class in the theorem has a positive area margin above $`2\pi`$, so the hemisphere bound persists on an open neighborhood in real conformal moduli. In one such neighborhood we prove **area above 7.42** for an explicit double with trivial holomorphic automorphism group and no equivariant cubic. [Quantitative comparison and asymmetric example](issue163_asymmetric_genus_two.md)

The new case with a cyclic quotient over the real projective plane includes the clustered family whose previous bound was $`6.23428`$. There is even a curve on which the earlier unweighted projective-line estimate gives precisely $`2\pi/3`$ for **both** projections. The short curves used here can exchange arcs at intersections. [Earlier projective-line estimates](issue163_projective_lines.md) · [The two-projection example and the remaining genus-two problem](issue163_genus_two_pencils.md)

## Distances and sheet displacements

Write $`A=\mathrm{Area}(N)=\mathrm{Area}(M)`$. The quotient $`N`$ has nonorientable genus five, $`X`$ has genus four, and every orientation-reversing loop in $`N`$ has length at least $`\pi`$. Indeed, cut a transverse loop at seam crossings and replace each piece by a shortest boundary arc in $`M`$. Boundary isometry bounds the replacement length, and cutting along the seam trivializes the orientation character. The resulting loop on the seam of length $`\pi`$ has odd winding. Approximation extends this to rectifiable loops. The proof below applies to any metric with this orientation-reversing length bound.

First suppose $`\tau`$ preserves the cyclic trigonal map up to a change of target coordinates. Its induced antiholomorphic involution on the sphere is conjugate to the antipodal map. Otherwise it fixes a circle, and a regular real fiber of odd cardinality would contain a fixed point of $`\tau`$. All ramification indices are three, so Riemann–Hurwitz gives six branch values forming three antipodal pairs. Write $`Q=\mathbb{RP}^2`$ and $`p_1,p_2,p_3`$ for the three images.

If $`\tau`$ commutes with a deck generator, the map $`N\to Q`$ is cyclic. Its unbranched part over $`Q^\circ=Q\setminus\{p_1,p_2,p_3\}`$ has a sheet displacement

~~~math
            \chi:\pi_1(Q^\circ)\longrightarrow\mathbb Z/3 .
~~~

Following a path around a branch value changes the sheet by a generator. Based loop displacements are independent of changes of basepoint by conjugation. Over a regular point let $`\rho_1,\rho_2,\rho_3`$ be the three length densities relative to the round metric of $`Q`$. Define $`\lambda=(\rho_1+\rho_2+\rho_3)/3`$. Then

~~~math
 3\int_Q\lambda^2\,dA_{\rm rd}\le A,\qquad
 \int_\gamma\lambda\,ds_{\rm rd}\ge\pi
 \quad\text{if }\gamma\text{ reverses orientation and }\chi(\gamma)=0.
~~~

Indeed, each of the three lifts of such a loop closes and reverses orientation. The integral is the mean of their lengths. All metric averaging in the cyclic argument occurs in this step.

## Three auxiliary projective planes

For each $`p_i`$ take a round projective plane $`Q_i`$ and the map $`R_i:Q_i\to Q`$ induced on the sphere by $`z\mapsto z^3`$ followed by a round rotation taking the poles to the pair over $`p_i`$. This map commutes with antipodes in the chosen coordinates. It has degree three in absolute value and its only projective branch value is $`p_i`$. Let $`\eta_i\,ds_{\rm rd}=R_i^*(\lambda\,ds_{\rm rd})`$. For a uniformly chosen round projective line $`L\subset Q_i`$,

~~~math
 \int_{Q_i}\eta_i^2\,dA_{\rm rd}=3\int_Q\lambda^2\,dA_{\rm rd}\le A,
 \qquad
 \mathbb E_L\,\ell_\lambda(R_i L)
 =\tfrac12\int_{Q_i}\eta_i\,dA_{\rm rd}
 \le\sqrt{\pi A/2}.
~~~

The factor $`1/2`$ is the ratio of line length to projective area. Area and line integrals count multiplicities. All selected curves can avoid the finitely many branch values.

For a generic $`L`$, the curve $`R_i L`$ splits at one double point into a simple one-sided loop $`o_i`$ and the boundary $`e_i`$ of an embedded disk $`D_i`$ containing $`p_i`$. To see this, rotate $`L`$ about the auxiliary pole by $`120`$ and $`240`$ degrees. The three lines have three distinct intersection points permuted cyclically. On the sphere take their unit normals with positive axial components. Their three positive half-spaces cut out a triangle containing the north pole. Their sum points north, so the triangle lies in the northern hemisphere. The quotient by the rotation identifies its three edges in cyclic order and maps it to a disk with one simple boundary loop. Its projection to $`Q`$ is embedded, since the antipodal triangle is disjoint. The rest of $`L`$ gives the second simple loop. The entire image has odd orientation character by antipodal equivariance, so this second loop is one-sided. Nongeneric lines through the pole, the equatorial line, and lines hitting a preimage of a mark may all be discarded.

Suppose each of the three auxiliary planes has a generic line whose image has $`\lambda`$-length strictly less than $`\pi`$. Choose one per plane. Strictness allows small perturbations making disk boundaries transverse to each other and avoiding each other's vertices. These take place in the regular part, preserve disk contents and loop classes, and can preserve all three strict inequalities. Write $`m=\chi(o_i)`$ and $`n=\chi(e_i)`$ for a chosen image. If $`m=0`$, its one-sided loop is already too short. If $`n\ne0`$, one of $`m,m+n,m-n`$ is zero. Omitting the disk loop or traversing it in the appropriate direction again contradicts the distance constraint.

It follows that each failure has $`n=0`$ and $`m\ne0`$. Its disk contains **exactly two** of the three marked points. It contains $`p_i`$, a single meridian has nonzero displacement, and if it contained all three then the complementary Möbius band would be unbranched. Its boundary represents twice its one-sided core up to sign. The loop $`o_i`$ is such a core after a small separation at the vertex, so $`n=\pm2m`$ in that case.

## Exchanging arcs between two disk boundaries

The three failed disks cannot contain the same pair, since each contains its own $`p_i`$. Choose two whose marked pairs differ and call their common marked point $`p`$. In the orientation sphere of $`Q`$, choose the lift of each disk containing the same lift $`p^+`$ of $`p`$. Both omit $`p^-`$ and can be viewed as planar disks. Their intersection contains just one marked lift, $`p^+`$. Each disk has another mark outside the other disk, so the boundaries $`b,c`$ intersect.

Both boundaries have zero displacement. Take closed lifts of $`b,c`$ to the cyclic cover $`X`$ of the marked sphere, with the branch values removed. At each crossing record the element of $`\mathbb Z/3`$ carrying the first sheet to the second. These elements cannot all agree. Indeed, after one deck rotation the two lifted curves would then agree at all crossings, yielding a section over the connected graph $`b\cup c`$. The face of the planar graph containing $`p^+`$ lies inside both disks. Its boundary walk has nonzero displacement because it encloses just one branch value. A section over that walk is impossible. This uses the lifted-intersection argument for short based loops in the hyperelliptic proof, here with three sheets. [Bangert, Croke, Ivanov and Katz, Lemma 7.2](https://arxiv.org/pdf/math/0405583)

Choose crossings $`s,t`$ with different sheet differences. On each of $`b,c`$ select the arc between $`s,t`$ that avoids its original figure-eight vertex. Exchange these two arcs, reversing their parametrizations when necessary to match endpoints. Each new loop still goes through its own vertex. Both now have **nonzero** displacement. In fact, orient the selected arcs from $`s`$ to $`t`$. The difference of their sheet transports equals, up to sign, the change in sheet difference from $`s`$ to $`t`$. Replacing either arc changes its original zero displacement by this nonzero element or its negative. These new loops lie on the orientation sphere, so their projections are two-sided in the sense of orientation character.

The sum of the two lengths is preserved by the exchange. Add back the two original one-sided loops. At least one of the resulting pairs costs less than $`\pi`$. Its nonzero disk-loop displacement allows the choice $`m,m+n,m-n`$ as before, producing a closed orientation-reversing lift shorter than $`\pi`$. This contradiction proves that **some auxiliary plane has every generic line of length at least $`\pi`$**. The preceding average gives $`A\ge2\pi`$.

## A positive margin in each fixed commuting class

Let $`\psi_i\,ds_{\rm rd}`$ be the base metric whose pullback by $`R_i`$ is the unit round metric of $`Q_i`$. It exists because the rotations defining the cyclic quotient are isometries. For the index whose lines all cost at least $`\pi`$, the mean length bound gives $`\int_{Q_i}\eta_i\ge2\pi`$. Expanding a square yields

~~~math
       3\int_Q(\lambda-\psi_i)^2\,dA_{\rm rd}
       =\int_{Q_i}(\eta_i-1)^2\,dA_{\rm rd}\le A-2\pi .
~~~

For each $`i`$ choose another mark $`p_j`$. Lift it to a point $`u`$ on the auxiliary sphere and let $`S`$ be the $`120`$-degree deck rotation. Since $`u`$ is off the axis, $`d_{\rm rd}(u,-Su)\lt\pi`$. The image of this arc is an orientation-reversing loop based at $`p_j`$ with $`\psi_i`$-length less than $`\pi`$. One can perturb the arc off the remaining marks and its own endpoint value in its interior, preserving strictness. In a small punctured disk about $`p_j`$, join its two truncated ends and insert, if needed, a meridian with either orientation. This costs arbitrarily little since $`\psi_i`$ is regular there. Its displacement can thus be made zero.

Take a small open neighborhood of the identity in the rotation group of $`Q`$. Every rotation in it keeps this last loop in the same free homotopy class in $`Q^\circ`$ and keeps its $`\psi_i`$-length at most $`\pi-\varepsilon_i`$ for some $`\varepsilon_i\gt0`$. The resulting mean round arclength has a bounded density $`k_i`$ relative to round area. Indeed the average over all rotations has constant density and conditioning on a positive-measure neighborhood increases its upper bound by at most the reciprocal of that measure. The distance constraint implies $`\int_Q(\lambda-\psi_i)k_i\ge\varepsilon_i`$. Consequently every admissible filling in this fixed class satisfies

~~~math
           A\ge2\pi+3\min_{1\le i\le3}
                     \frac{\varepsilon_i^2}{\|k_i\|_2^2}\gt2\pi .
~~~

The margin depends on the branch configuration. For a smooth marking of a nearby conformal class of distortion $`K`$, use the larger length singular value of the pulled-back metric as its conformal density on the reference surface. It dominates lengths and its area is at most $`K A`$. Thus a reference margin $`\delta\gt0`$ proves $`A\ge2\pi`$ whenever $`K\le1+\delta/(2\pi)`$.

## The other actions on a cyclic pencil

If $`\tau`$ preserves the map and inverts the deck generator, every orientation-reversing base loop acts on its three sheets by $`j\mapsto c-j`$ and fixes one. The projective-line argument applies. It also gives a strict fixed-class margin for any three distinct projective branch values. For almost every regular basepoint the lines toward those three values divide its direction circle into three nonempty intervals. Crossing just one marked direction composes the sheet permutation with a conjugate of a local three-cycle. Adjacent transpositions therefore have different fixed sheets, including across the last endpoint of the direction circle. The three conditional sheet probabilities $`w_j`$ are all positive. The length average gives $`A\ge 2\pi/(\mathbb E\sum_jw_j^2)\gt2\pi`$. [Derivation of the sheet-weighted estimate](issue163_projective_lines.md)

Finally suppose $`\tau`$ exchanges the given pencil with a different one. Write $`f_1,f_2`$ for the pair. The joint map embeds $`X`$ as a smooth curve of bidegree $`(3,3)`$ on a quadric. Indeed its generic degree divides three, and degree three would identify the pencils. The image has arithmetic genus four, the genus of its normalization, hence is smooth. By adjunction this is its canonical embedding via $`\mathcal O(1,1)`$. Any second independent quadric would restrict to a divisor of type $`(2,2)`$ containing this curve. The two rulings give all degree-three pencils. A general fiber of any such pencil spans a line by Riemann–Roch (a degree-three divisor on this nonhyperelliptic genus-four curve has at most two sections by Clifford's theorem). A line meeting the unique quadric in three distinct points lies on the quadric and belongs to a ruling. These facts about trigonal curves also appear in the real-curve classification. [Gross and Harris, section 8](https://www.numdam.org/item/10.24033/asens.1401/)

Choose an order-three deck generator $`\sigma_1`$ and set $`\sigma_2=\tau\sigma_1\tau^{-1}`$. Each preserves both rulings, since an order-three permutation cannot exchange two pencils. In the product of projective lines the two generators act on separate factors. They generate $`(\mathbb Z/3)^2`$. They cannot have a common fixed point on $`X`$, since a finite stabilizer of a point of a Riemann surface is cyclic (its derivative action is faithful). The automorphism $`s=\sigma_1\sigma_2^{-1}`$ is therefore free, since a fixed point in the product would be fixed on both factors separately. Moreover $`\tau s\tau^{-1}=s^{-1}`$.

The unbranched quotient $`Z=X/\langle s\rangle`$ has genus two. Its descended involution $`\tau'`$ is free since any invariant fiber of odd size would contain a $`\tau`$-fixed point. Put $`N'=Z/\tau'`$. Every orientation-reversing loop on $`N'`$ has a closed orientation-reversing lift to $`N`$, by the same $`j\mapsto c-j`$ formula. Relative to any smooth conformal metric on $`N'`$, use the maximum of the three length densities over each point. Its area is at most $`A`$, and every orientation-reversing loop now costs at least $`\pi`$. A genus-two Riemann surface is hyperelliptic, so the relative Pu theorem gives $`A\ge2\pi`$. Continuous metrics can be approximated from above in this conformal class. [Bangert, Croke, Ivanov and Katz, Theorem 1.7](https://arxiv.org/pdf/math/0405583)

## Strictness for the transferred genus-two double

For completeness, the hyperelliptic comparison used in the last step has a positive margin in each *fixed* genus-two conformal class with free real involution. Let $`A'`$ be the area on $`N'`$. The hyperelliptic map on $`Z`$ has six branch values. The real involution on its sphere is reflection across the equator, with three branch values in the open northern hemisphere $`H`$. Average the two length densities there to get $`\lambda`$, now with $`2\int_H\lambda^2\le A'`$. Any loop in the closed hemisphere based on the equator with odd total winding modulo two about the three marks has $`\lambda`$-length at least $`\pi`$. Each of its two lifts connects $`z`$ to $`\tau'z`$ over its equatorial basepoint. [Hyperelliptic quotient and loops in a hemisphere, sections 6–7](https://arxiv.org/pdf/math/0405583)

For a mark $`w_i\in H`$ choose the degree-two sphere map branched at $`w_i`$ and its reflected point. Use round coordinates on its source so the map is $`z\mapsto z^2`$ followed by a conformal automorphism of the target preserving the equator and its hemispheres. Its deck rotation is a round half-turn. The northern half of a generic great circle projects to a loop based on the equator enclosing $`w_i`$. Reflection gives its other half the same length. If each mark had such a loop shorter than $`\pi`$, the odd-set loop lemma in the hemisphere would produce an equator-based loop shorter than $`\pi`$ with odd total winding. Use the largest of the three strict lengths as the common cutoff. Thus for some $`i`$ every generic northern half costs at least $`\pi`$. [Bangert, Croke, Ivanov and Katz, Lemmas 5.1 and 7.3](https://arxiv.org/pdf/math/0405583)

Let $`\psi_i`$ be the density on $`H`$ pulling back to the round northern hemisphere under this double map. A uniform great circle spends half its length there with mean arclength density $`1/2`$. The same square expansion gives $`2\int_H(\lambda-\psi_i)^2\le A'-2\pi`$, using any fixed round area reference on the target for the densities.

For this football metric, every other mark $`w_j`$ has distance strictly less than $`\pi/2`$ to the equator. Only the cone point attains $`\pi/2`$, as one sees on the round northern double. Travel from the equator toward $`w_j`$, circle $`w_j`$ in a small regular disk, then retrace the incoming arc. Such loops enclose precisely $`w_j`$ modulo two and can have lengths uniformly below $`\pi`$. To obtain bounded mean arclength density, use a small annulus about $`w_j`$, choose a radius uniformly in a compact positive interval, and choose a meridian from the equator uniformly in a short interval of longitudes about the one through $`w_j`$. Stop at its first intersection with the chosen circle, traverse the circle and return. Take the intervals small enough that all intersections are transverse. The meridian portions stay away from the cone point and have bounded occupation by polar coordinates. The circle portions have bounded occupation by integration in radius. The incoming arc can meet other marks only on a null set of longitudes. These area comparisons hold for smooth reference area as the paths stay in a compact region away from the cone point. Cauchy–Schwarz now gives a positive margin for each of the three candidate densities, exactly as in the commuting case. The minimum is positive. This proves strictness on $`N'`$ and hence on $`N`$.

The same fixed-class margin argument applies in every filling genus $`g\ge1`$ when the orientation double is hyperelliptic. Its genus is $`2g`$, so the comparison disk has $`2g+1`$ marked points. This number is odd, as required by the based-loop lemma, and each mark has a different regular mark at which to construct the short comparison loop. Taking a minimum over the finitely many footballs still gives a positive margin. The size of the resulting conformal neighborhood can depend on all the marks.

For an example in the component with exchanged rulings, use the smooth compact curve

~~~math
              1+\tfrac12(u^3+v^3)+u^3v^3=0,\qquad
              \tau(u,v)=(\bar v,\bar u).
~~~

It is a cyclic cubic in each coordinate. The equation $`v^3=-(u^3+2)/(2u^3+1)`$ has three simple zeros and three simple poles, with the local equations smooth there and at infinity. On the real locus $`v=\bar u`$ its left side is $`|u^3+1/2|^2+3/4`$, and the point at infinity on this real sphere also misses the curve. On this example the transferred comparison gives **area above 7.5050**, so the hemisphere bound holds up to conformal distortion **1.1944**. Within this neighborhood both complex projections can have twelve simple branch values while the real structure exchanges them. [Explicit deformation and quantitative estimate](issue163_asymmetric_genus_two.md) · [Degree-five comparison](issue163_genus_two_pencils.md)
