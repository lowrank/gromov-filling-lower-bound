# Ordinary three-sheeted covers with area above 6.65

The genus-four doubles in this family admit an equivariant three-sheeted map with full $`S_3`$ monodromy and six simple projective branch values. **Every genus-two filling in these conformal classes has area above 6.65**, while the direct projective-line estimate for this map is **below 4.8**. All the simple branch points can move inside the indicated disks. The bound uses the region that survives when the sheet connections inside the disks change. [Conformal embedding estimate](issue163_thin_genus_two.md#keeping-the-conformal-structure-of-the-capped-surface)

## A genus-one reference filling class

Let $`a=1/8`$ and take the compact smooth model of

~~~math
 x^3=\frac{z^2-a^2}{1-a^2z^2},\qquad
 \tau(z,x)=(-1/\bar z,1/\bar x).
~~~

Substitution verifies the involution and the $`z`$ coordinate makes it free. Projection to $`z`$ is cyclic cubic with full ramification at the two zeros and their antipodal poles, giving genus two by Riemann–Hurwitz. Let $`Y`$ be the nonorientable quotient, of genus three. Projection to $`x`$ is hyperelliptic, with branch values at $`x^3=-a^2,-1/a^2`$. In the unit disk the three marks have radius $`a^{2/3}=1/4`$ and angular spacing $`120`$ degrees.

For this geometry the hyperelliptic comparison gives $`P(Y)\gt2\pi\cdot2400/2231`$. Here $`P(Y)`$ is the least conformal area as an infimum with orientation-reversing lengths at least $`\pi`$. To verify the constant, let $`\psi_j`$ be the density whose northern hemisphere double branches at mark $`j`$. The threefold symmetry permutes the marks, so their averaged comparison gives $`P(Y)\ge 2\pi/D`$ with $`D=1-\|\psi_1-\psi_2\|_2^2/(3\pi)`$. In the unit disk coordinate taking a mark to zero its density is $`1/(\sqrt{|z|}(1+|z|))`$. [Derivation of the three-density formula](issue163_asymmetric_genus_two.md#a-quantitative-reference-class)

Take the pseudohyperbolic disk of radius $`s=1/8`$ about each mark. Their center separation is $`d=4/\sqrt{91}\gt5/12`$. The disks are disjoint since $`d\gt2s/(1+s^2)`$. On the disk belonging to $`i`$ the normalized squared mass of $`\psi_i`$ is $`2s/(1+s)=2/9\gt(47/100)^2`$. For a different mark, the disk in centered coordinates has Euclidean radius $`R=s(1-d^2)/(1-d^2s^2)`$ and closest modulus $`h=(d-s)/(1-ds)`$. The normalized mass there is at most $`R^2/[h(1+h)^2]`$, decreasing in $`d`$ and equal to $`208/10201\lt(29/200)^2`$ at $`d=5/12`$. Applying the reverse triangle inequality on both disks gives

~~~math
            D\lt1-\tfrac23(47/100-29/200)^2=2231/2400 .
~~~

For comparison, the line test for the cubic uses only the monodromy of one projective line at a time. A random great circle separates the two zeros with probability $`4\arctan(a)/\pi`$, the angle between them divided by $`\pi`$. The complementary hemisphere contains the antipodes of its omitted zeros. The signed zero count therefore vanishes when the zeros are separated and is $`\pm2`$ otherwise. This determines the full-circle permutation by the argument principle. The real involution commutes with the cubic generator, so the projective permutation lies in the cyclic group of order three and is determined by its square. Thus it is the identity precisely in the separated case. The direct certificate is

~~~math
       2\pi\left(\tfrac13+\tfrac83\,\frac{4\arctan(1/8)}{\pi}\right)
       =4.74730\ldots .
~~~

## Changing the gluing inside four coordinate disks

On the target projective plane take three disjoint round coordinate disks, two centered at the projective branch values of the reference cubic and one at the class of $`z=i`$. In centered spherical stereographic coordinates choose outer radii $`R_0=1/16`$. The first two centers have spherical projective distance $`4\arctan(1/8)\gt4\arctan(1/16)`$, and the third lies at projective distance $`\pi/2`$ from both. Write $`r=1/256`$.

* Over the third disk there are three regular sheets. Choose two. In the inner target disk of stereographic radius $`R_0r`$, glue these sheets together by the double cover branched at two distinct interior values. The third sheet is retained. The two transpositions agree, so the boundary monodromy is the identity and the old sheets match on the surrounding annulus. The connected double cover of the inner disk is an annulus by Euler characteristic. It replaces two disks by a handle and lowers the surface Euler characteristic by two.
* Each of the two old fully ramified disks has a source coordinate $`w`$ with target coordinate $`R_0 w^3`$. Within target radius $`R_0r^3`$, replace the old three-cycle by two distinct transpositions with the same ordered product. They act transitively and the new disk cover has Euler characteristic $`3-2=1`$ with one boundary component. It is again a disk. Each replacement splits one full branch value into two simple ones.

These modifications are conformal off the chosen slits by construction. More explicitly, take the topological unbranched cover with the prescribed permutations on the punctured inner disk, pull back the target conformal structure, and complete the ramification points with power-map coordinates. Unbranched covers on the overlap are identified over the base by matching their identical boundary permutations. This identification is conformal. The result is a connected cubic cover of the projective plane. Its six meridians are transpositions, and the old three-cycle remains as the product around either split pair. Its monodromy group is $`S_3`$, also on the orientation sphere since these local meridians are orientation-preserving. The quotient has Euler characteristic $`3-6=-3`$ and its orientation double has genus four.

In the source, the four replacements leave a conformal copy of $`Y`$ minus four coordinate disks of relative radius $`r`$. These consist of the two regular sheets used for the handle and the two old ramification disks. Applying the conformal embedding estimate gives

~~~math
             A\ \ge\ (1-r^{3/4})P(Y)
             \ \gt\ \frac{63}{64}\,\frac{2400}{2231}\,2\pi
             \ \gt\ 6.65 .
~~~

For any round projective line missing the modified target disks the original sheet permutation persists. The probability of hitting one disk of spherical radius $`\varepsilon`$ is $`\sin\varepsilon`$, by the uniform distribution of a great-circle normal. Each modified disk has stereographic radius at most $`1/4096`$ and hence hit probability less than $`1/2048`$. The change in the direct estimate is at most $`2\pi(3-1/3)(3/2048)`$. Even the upper estimate obtained by assigning every affected line three fixed sheets is below $`4.8`$. These inequalities hold uniformly in the positions of the new simple branch values inside their disks. The conformal quotient classes can be cut to give actual fillings by choosing a characteristic one-sided core, as in the earlier construction. [Line formula and realization by fillings](issue163_projective_lines.md) · [Arithmetic replay](issue163_collar_surgery_check.py)
