# How much of the continuum comass excess can the triangular profiles carry?

Let $`D=6.15`$. In every compact connected orientable isometric filling of the circle of length $`2\pi`$ with area $`A\le D`$, a positive amount of Züst's excess density must occur a **uniform positive distance** from the eroded, folded and clipped boundary triangles and the round-hemisphere profiles. If $`w`$ is the signed density of the normalized form and $`S`$ is their union, there exists $`\eta\gt 0`$, the same in every genus, for which

~~~math
 \int_{\{d_\infty(F,S)\gt \eta\}} (w-1)_+\,dA \gt  0.01349 .
~~~

If the folded triangles are omitted from $`S`$, the lower bound is **0.03846**. The first estimate requires more than **0.0236** surface area outside the stated neighborhood where $`w\gt 1`$. The radius in the excess estimates is obtained by compactness. The area estimate for a tube of any specified small radius, derived below, is explicit. The current unconditional area certificate gives **6.096292737690900167**. [Area certificate](issue163_anchor_occupation.md) · [Züst's form](https://arxiv.org/pdf/2104.04498) · [Scalar arithmetic replay](issue163_profile_occupation.py)

There is also a single inequality valid at every area. Write $`R_\eta`$ for the exterior integral above and $`c_0=1/\pi+\pi/4`$. For a sufficiently small fixed $`\eta\gt 0`$,

~~~math
 A+R_\eta/c_0\ \gt\ 6.16222 .
~~~

With the folded family omitted the right side is **6.18485**. The exterior integral is the term that must be controlled to turn this comparison into an area bound. For example, on a filling with $`A\le 6.15`$ the normalized finite calibration of action $`B\gt 6.096286`$ has density $`w_B\le1`$ and satisfies $`\int(1-w_B)\,dA\lt 0.053714`$. Hence a set of positive area outside the four families' tube must satisfy $`w-1\gt (1-w_B)/4`$. Otherwise its total positive excess would be less than 0.013429. This gives a joint test on the two comass comparisons.

A modified pair form has exact boundary action **6.1543800083824…** and satisfies the unit net density test on all four families through their full width ranges. It uses the height determined by each pair of scalar distance coordinates. [Construction and finite-width estimate](#a-modified-form-with-boundary-action-above-615)

Write $`h=\pi/2`$ and $`b_s(a)=h-d_{S^1}(s,a)`$. A profile $`P`$ is antiperiodic and 1-Lipschitz in $`a`$. Their space $`X`$ is compact in the uniform metric. On a filling use $`F_a(x)=(d(x,a+\pi)-d(x,a))/2`$. With orientation chosen so the boundary action is positive, let

~~~math
 w=\frac1\pi\int_{0\lt a\lt b\lt \pi}p_{ab}(F)\,
       \det(\nabla F_a,\nabla F_b)\,da\,db .
~~~

Here $`p_{ab}`$ is Züst's nonnegative coefficient. It is continuous in the two scalar values for distinct, nonantipodal labels at interior profiles. At profile depth $`h-\max_a P_a\ge r\gt 0`$ it is uniformly bounded, including as the labels approach each other. For example completing a square gives $`p_{ab}\le(1-\sin^2 P_a)^{-1}`$. The pair-weight inequality gives $`|w|\le\pi/2`$. The signed integral on the full filling is $`2\pi`$, so $`A\le D`$ requires at least $`2\pi-D\gt 0.133185`$ total positive excess. [Coefficient, pair-weight proof and regularization](issue163_zust_mass.md)

At depth parameter $`e`$, apply the odd functions below to $`y=b_s(a)`$ and allow every rotation $`s`$ to obtain the eroded, folded and clipped triangles.

~~~math
 E_e(y)=\mathrm{sgn}(y)(|y|-e)_+,\qquad
 K_e(y)=\mathrm{sgn}(y)\max\{|y|-e,-|y|\},\qquad
 C_e(y)=\mathrm{sgn}(y)\min\{|y|,h-e\}.
~~~

Take $`0\le e\le h`$ for erosion and clipping, and $`0\le e\le\pi/3`$ for folding, through its threefold endpoint. The round family is $`P_a=\arcsin(R\cos(a-s))`$, $`0\le R\le1`$. The previously computed eroded test tends to raw density $`1/\pi+\pi/4=1.103708\ldots`$. [Two-direction test](issue163_zust_angles.md) · [Folded and clipped tests](issue163_continuum_tests.md)

There is already a shortest-path obstruction at a single point. An interior point of a smooth filling cannot have $`F_s-F_{s+t}=|t|`$ on both sides of $`t=0`$ for all small $`t`$. Each of the two distance increments contributing to this difference is at most $`|t|`$. Equality forces $`d(x,s+t)=d(x,s)+|t|`$. Choose a minimizing path from $`x`$ to $`s`$ and flow it by a smooth vector field which fixes a neighborhood of $`x`$ and translates the boundary by arclength. The path length is a differentiable upper support for $`d(x,s+t)`$, with equality at zero. Such a support cannot touch an upward corner. This excludes the exact eroded peak at every positive amplitude, including the boundary triangle at an interior point. Arbitrarily close approximations on small patches of true fillings are possible. The estimates below control concentration across a sequence of entire fillings. [Local realization with short routes](issue163_short_routes.md)

## An explicit upper bound on the area of a profile tube

Use the existing closed calibration of comass one and boundary action $`B\gt 6.096286`$. It accepts any family of coordinates with the triangular boundary trace, angular Lipschitz constant one and spatial Lipschitz constant one. For this proof one can use the rational lower estimate $`B_0=6.096286`$ for its action. [Signed anchor calibration](issue163_anchor.md)

Suppose $`Y\subset X`$ contains the boundary triangles and has an arclength map $`s:Y\to S^1`$ with $`s(b_u)=u`$ and Lipschitz constant $`L`$ for intrinsic circle distance. The map $`P\mapsto b_{s(P)}`$ extends to an $`L`$-Lipschitz map $`Q:X\to X`$. Indeed take the infimum over $`T\in Y`$ of $`b_{s(T)}(a)+L\|P-T\|_\infty`$ for each label $`a`$, then take half the difference of the values at $`a`$ and $`a+\pi`$. The infimum preserves angular Lipschitz continuity. For $`d(P,Y)\lt \delta`$, the image $`Q(P)`$ is within $`L\delta`$ of a boundary triangle.

There is a circle-valued phase map on the $`r`$-tube around the boundary triangles. For $`r\le1/10`$ put

~~~math
 d_r=\frac{\pi}{2}\big(1-\sqrt{1-4r/\pi}\big),\qquad
 \kappa(r)=1-4(r+d_r)/\pi .
~~~

Take the zero $`v`$ of $`J_v(P)=\pi^{-1}\int_v^{v+\pi}P_a\,da`$ with $`P_v\gt 0`$. If $`\|P-b_u\|_\infty\le r`$, then $`|v-u|_{S^1}\le d_r`$. In fact $`J_{u+d}(b_u)=-d(1-d/\pi)`$ for $`0\le d\le\pi`$, with the reflected formula on the other side. Its only possible zero neighborhoods after perturbation are within $`d_r`$ of $`u`$ and its antipode. On the first interval $`P_v\ge h-r-d_r\gt 0`$ and $`J'_v=-2P_v/\pi`$. The intermediate value theorem gives exactly one such zero. Thus $`\|P-b_v\|_\infty\le r+d_r`$. For two phases separated by $`d\le\pi/2`$, the two descending half-circles overlap on an interval of length $`\pi-d`$. On the overlap their boundary triangles differ by $`d`$. Each error $`P-b_v`$ has mean zero on its own descending half and absolute value at most $`r+d_r`$. Its integral on the overlap is at most $`(r+d_r)d`$ in magnitude. For $`d\ge\pi/2`$ use $`\|b_v-b_{v'}\|_\infty=d`$. Both comparisons give $`\|P-P'\|_\infty\ge\kappa(r)d`$.

Compose this phase with $`Q`$. On $`d(P,Y)\lt \delta`$ the composite has Lipschitz constant $`L/\kappa(L\delta)`$. Extend its triangular coordinates to all profiles by the same infimum and antiperiodic symmetrization. On the tube they factor through a circle, so their spatial differentials have rank at most one almost everywhere there. Pull back the calibration on the filling. It has zero density in the tube and density at most $`[L/\kappa(L\delta)]^2`$ outside. Its boundary action gives

~~~math
 \mathrm{Area}\{d(F,Y)\lt \delta\}
 \le A-B_0 L^{-2}\kappa(L\delta)^2 .
~~~

For $`Y`$ consisting of all eroded profiles through width $`t\lt h`$, one may use $`L=1/\sigma(t)`$, where $`\sigma(t)=(\pi-2t)/(\pi+2t)`$. For the union of eroded and folded profiles through $`t\lt \pi/3`$, use $`\sigma(t)=(\pi-3t)/(\pi+t)`$. To check this, evaluate a pair of profiles at their two center labels, separated by $`d\in[0,\pi]`$. The maximum of the two signed differences is at least the mean of $`h-e-\phi_e(h-d)`$ for the two shapes and widths. For erosion this expression is successively $`d,h-e,d-2e`$, with switches at $`h-e,h+e`$. Its ratio to $`d`$ is at least $`(h-e)/(h+e)`$. For folding the three expressions are $`d,2h-e-d,d-2e`$, with switches at $`h-e/2,h+e/2`$. The ratio is at least $`(h-3e/2)/(h+e/2)`$. The centers are unique in these width ranges. For example, in area at most 6.15 the 0.001-tube around all eroded profiles through width 0.05 has area less than 0.812.

## Which Jacobians can survive concentration?

Consider any sequence of the fillings with $`A\le D`$. Push forward area by $`F`$ to measures $`\mu_j`$ on $`X`$ and pass to a weak limit $`\mu`$. On $`X\times(S^1)^2`$ also take a weak limit of the signed measures obtained by pushing forward $`\det(\nabla F_a,\nabla F_b)\,dA\,da\,db`$, keeping the two labels. The limit has density $`k(P,a,b)`$ with respect to $`\mu\,da\,db`$, with $`|k|\le1`$. It is antisymmetric and antiperiodic in each label. The explicit tube inequality and weak convergence on open neighborhoods give $`\mu(Y_t)\le D-B_0\sigma(t)^2`$ for each family through width $`t`$ above.

The following consequence of Stokes applies even if the gradients oscillate as the profiles converge. Suppose $`H=\sum_i c_i P_{a_i}-c(\mathbf a)`$ is an affine relation on scalar values, with fixed coefficients and continuous label term. On $`\{H=0\}`$ the corresponding combination of rows of $`k`$ vanishes almost everywhere for the joint area and label measures. Indeed choose smooth functions $`h_\epsilon`$ with $`\|h_\epsilon\|_\infty=O(\epsilon)`$ and uniformly bounded derivatives converging pointwise to the indicator of zero. For a Lipschitz test $`\chi`$ on profiles and labels and a label $`b`$, apply

~~~math
 \int_M \chi\,h'_\epsilon(H)\,dH\wedge dF_b
 =\int_{\partial M}\chi h_\epsilon(H)\,dF_b
    -\int_M h_\epsilon(H)\,d\chi\wedge dF_b .
~~~

The right side is $`O(\epsilon)`$ uniformly, since the boundary length is fixed, the areas are bounded and $`F:M\to X`$ is 1-Lipschitz. Integrate the labels. At fixed $`\epsilon`$ the left side passes to the weak limit, including any auxiliary independent labels by product with Lebesgue measure. Then use dominated convergence. The label $`b`$ can itself occur in $`H`$ since its wedge with itself is zero. Truncating continuous label charts or using the finitely many possible lifts handles constants written in unwrapped angles. In particular $`k=0`$ when $`P_a=0`$, when $`P_a=\pm P_b`$, and on each boundary facet of a pair polygon $`|P_a-P_b|\le d`$, $`|P_a+P_b|\le\pi-d`$, on the corresponding equality set.

At interior profiles integrate $`p_{ab}(P)k(P,a,b)/\pi`$ over $`0\lt a\lt b\lt \pi`$ to define a signed density $`w_*(P)`$ for $`\mu`$. It represents the weak limit of the signed action on compact subsets away from the boundary triangles. Remove a thin angular strip around coinciding or antipodal labels, use continuity there, and use the depth bound on the coefficient for the discarded strip. The density satisfies $`|w_*|\le\pi/2`$.

**The full action survives in the interior.** Set $`w_*=0`$ on the boundary triangles. Apply the same weak-limit computation to $`T_q(P_a)=\arcsin(q\sin P_a)`$ at fixed $`0\lt q\lt 1`$. Its coefficients, including the two scalar derivatives, are bounded and the absolute density is at most $`\pi/2`$. Its action is $`2\pi(1-\sqrt{1-q^2})`$ on every filling. At a boundary triangle every label pair is on a pair-polygon facet, so its limiting Jacobian vanishes. At interior profiles the regularized density tends to $`w_*`$ by dominated convergence in the labels. Dominated convergence in $`\mu`$ now gives $`\int_X w_*\,d\mu=2\pi`$. The same regularization on a single filling gives $`\int_M w\,dA=2\pi`$. [Pair-polygon degree](issue163_free_field.md) · [Regularized boundary action](issue163_zust_mass.md#consequence-for-actual-fillings)

## The densities on the four families

A round interior profile has pointwise comass at most one for arbitrary gradient directions. There $`p_{ab}=g_a g_b`$, with $`g_a\,da/\pi`$ a probability measure on the projective label circle. The absolute determinant of two independent planar unit directions has mean at most $`2/\pi`$ by the Fourier series of $`|\sin|`$. The kernel varies continuously in label $`L^1`$ when the profile varies uniformly near an interior round profile. Evaluating on the same gradients therefore changes the density by at most that $`L^1`$ error divided by $`\pi`$, which gives the same upper bound on the limiting signed density there. [Round comparison](issue163_zust_angles.md#a-change-using-both-angles)

For erosion choose $`s=0`$ by rotation. In the half-circle there are a left ramp, a zero interval and a right ramp. The pairs on each single ramp have $`p_{ab}=0`$. Pairs meeting the zero interval have limiting $`k=0`$ by Stokes. The surviving contribution is at most the integral of $`p_{ab}/\pi`$ over left-right pairs. Call it $`C_E(e)`$.

For folding the two outer ramps have the same formulas as in erosion, each extending to length $`h-e/2`$. On the middle interval the value is $`-b_s(a)`$. In local unwrapped angles, $`P_i+i`$ equals $`h+s-e`$ on the left and $`h+s+e`$ on the right, and $`P_j-j=-h-s`$ in the middle. The linear relations above identify all rows within each group, for almost every label. Twice any one middle row plus a left row and a right row sum to zero almost everywhere in the labels. This follows by using $`2(P_j-j)+(P_i+i)+(P_l+l)=0`$ and an auxiliary wedge label. Fubini and antisymmetry then give three pair densities $`k_{LR}=z`$, $`k_{LM}=k_{MR}=-z/2`$ on the respective ordered blocks, with $`|z|\le1`$. The identities apply on the full-measure set of label tuples for each such profile, including after choosing the half-circle beginning at its center. Intra-group determinants vanish. The absolute evaluation is at most the larger of the full left-right integral $`C_K(e)`$ and half the remaining cross-group integral. The latter is at most $`\pi/4`$ by the pair-weight theorem. Erosion has $`C_E(e)\le C_K(e)`$ wherever both families are defined, by inclusion of the two positive integration domains.

For clipping at $`m=h-e`$, both ramp labels give a pair on the original boundary polygon, with $`p_{ab}=0`$. Two plateau labels satisfy $`P_a=\pm P_b`$ and give zero limiting Jacobian. The remaining absolute sum equals the absolute density on the explicit cylinder $`(s,e)\mapsto C_e(b_s)`$ with metric $`ds^2+de^2`$. In a half-circle beginning at $`s`$ the two plateau gradients are $`(0,-1),(0,1)`$ and the intervening ramp gradient is $`(1,0)`$. All surviving ordered determinants equal one. This density is $`-J'(e)/(2\pi)`$, where $`J(e)`$ is the action inside the clipped loop.

To compute $`J(e)`$, componentwise clipping restricts each degree-one pair polygon to $`|P_a|,|P_b|\lt m`$. Equivalently integrate the original form on the hemisphere with this indicator on each pair. At hemisphere height $`z`$, set $`R=\sqrt{1-z^2}`$. For the round gradient direction $`\nu`$ measured from the meridian, $`|\tan P_a|=R|\cos\nu|/z`$. The round coefficient change of variables $`d\nu=g_a\,da`$ gives pair action proportional to $`\sin|\nu-\nu'|`$ on the projective circle. For $`u=\max(|\cos\nu|,|\cos\nu'|)`$ its cumulative distribution is $`(L-\sin L)/\pi`$, with $`L=2\arcsin u`$. Indeed both directions must be in a single interval of length $`L`$, and the ordered sine integral there is $`L-\sin L`$. The condition on height is $`z\ge u/\sqrt{\tan^2m+u^2}`$ and hemisphere area is $`ds\,dz`$. Integrating with the density $`4u^2/(\pi\sqrt{1-u^2})`$ gives

~~~math
 \begin{aligned}
 \frac{J(e)}{2\pi}
 &=1-\frac4\pi\int_0^1\frac{1-v^2}{\sqrt{\sec^2m-v^2}}\,dv
 =1-\frac2\pi\big[(2-\csc^2 e)e+\cot e\big],\\[2pt]
 -\frac{J'(e)}{2\pi}
 &=\frac4\pi\frac{\cos e\,(e-\sin e\cos e)}{\sin^3 e}
 \le \frac8{3\pi}\lt 0.848827 .
 \end{aligned}
~~~

The first substitution is $`v=\sqrt{1-u^2}`$. For the inequality the derivative of $`(2/3)\sin^3 e-\cos e(e-\sin e\cos e)`$ is $`\sin e(e-\sin e\cos e)\ge0`$. The endpoint at zero is obtained by a limit. Thus clipping contributes zero positive limiting excess at every width.

## Bounding the total excess by profile width

For cross-ramp labels $`a,\pi-v`$ put $`U=\tan a/(\tan e+\tan a)`$ and likewise $`V`$ for $`v`$. Put $`S'=UV/\cos^2e`$ and $`H=U+V-2UV`$. The pair weight in $`dU\,dV`$ is $`4S'(1-S')/H^2`$. Each variable has maximum $`\cos^2e`$ for erosion and $`\cos e`$ for folding. Scale each square to $`[0,1]^2`$, take the half in which the first variable is larger, and write the two coordinates there as $`u,uy`$. This gives

~~~math
 \begin{aligned}
 C_E(e)&=\frac{8t}{\pi}\int_0^1\int_0^1
    \frac{uy(1-tu^2 y)}{(1+y-2tuy)^2}\,du\,dy,\quad t=\cos^2e,\\[2pt]
 C_K(e)&=\frac8\pi\int_0^1\int_0^1
    \frac{uy(1-u^2 y)}{(1+y-2tuy)^2}\,du\,dy,\quad t=\cos e .
 \end{aligned}
~~~

Both have value $`c_0=1/\pi+\pi/4`$ at $`e=0`$ by the common limiting integral. Both decrease with width. For reproducible upper bounds, expand in powers of $`t`$ and substitute $`v=2y/(1+y)`$. In units of $`4/\pi`$ the two coefficient lists are

~~~math
 \begin{aligned}
 a_m &=\int_0^1\frac{v^m}{(2-v)^2}
     \left[\frac{m}{m+1}-\frac{m-1}{m+2}
           +\frac{m}{m+1}(1-v)\right]dv, &&m\ge1,\\[2pt]
 b_n &=\frac{n+1}{(n+2)(n+4)}
   \int_0^1\frac{v^{n+1}}{(2-v)^2}
      [2+(2n+6)(1-v)]\,dv, && n\ge0 .
 \end{aligned}
~~~

These follow from the geometric derivative series for the squared denominator and integration of the powers of $`u`$. All coefficients are nonnegative. In the folded formula monotone convergence at $`t=1`$ gives the same integral as the eroded limit; for erosion the positive coefficient sum also follows from its known boundary limit. Truncation at degree 256 uses the sum $`c_0`$ and replaces each remaining power by $`t^{257}`$. The scalar checker encloses every retained coefficient by the series for $`(2-v)^{-2}`$. [Cross-ramp change of variables and boundary limit](issue163_zust_angles.md#a-family-with-two-gradient-directions)

For each of the two comparisons put $`M(t)=D-B_0\sigma(t)^2`$ in the applicable width range. On eroded profiles use $`q(t)=(C_E(t)-1)_+`$, and on the eroded-folded union use $`q(t)=(C_K(t)-1)_+`$. Width here is the depth $`h-\max F`$ for these families. Round and clipped profiles have zero positive limiting excess. With $`t_j=j/200`$ a nonincreasing $`q`$ and the cumulative upper bounds $`\mu(Y_t)\le M(t)`$ give

~~~math
 \int_S(w_*-1)_+\,d\mu\ \le\ q(0)M(0)
   +\sum_{j=0}^{m-1}q(t_j)\big[M(t_{j+1})-M(t_j)\big].
~~~

Indeed a shell step-function majorant of $`q`$ can be written as a positive sum of nested indicators. The numerical upper bounds for $`q(t_j)`$ can be substituted on the right because its coefficients are nonnegative. For erosion $`q(0.10)=0`$ and the result is below **0.094717**. On the larger union $`q(0.12)=0`$ and the result is below **0.119694**.

Finally, if the claimed uniform neighborhood failed, take fillings with radii $`\eta_j\downarrow0`$ violating the proposed exterior estimate. Every continuous test $`0\le\chi\le1`$ compactly supported in $`X\setminus S`$ is eventually supported outside those tubes, away from the boundary triangles. The weak convergence of the action and area gives the same upper bound for $`\int\chi(w_*-1)\,d\mu`$. Taking the supremum gives that upper bound for the exterior positive part. But $`\int(w_*-1)\,d\mu\ge2\pi-D`$. Subtracting the two respective budgets requires exterior positive excess greater than 0.03846 or 0.01349. This contradiction proves the statement for whole fillings, allowing arbitrary near-profile gradients and unbounded genus.

For the inequality at every area, a sequence violating it has bounded areas, since $`R_\eta\ge0`$. Pass to a limit of those areas $`A_*=\mu(X)`$ and of the exterior integrals. Use $`A_*`$ in place of $`D`$ in $`M(t)`$. Only the first term in the shell bound changes, by exactly $`(c_0-1)(A_*-D)`$. If $`b`$ is the corresponding verified shell budget at $`D`$, the same weak-limit argument gives

~~~math
 A_*+\frac{\lim R_{\eta_j}}{c_0}
 \ \ge\ D+\frac{2\pi-D-b}{c_0}.
~~~

The right side exceeds 6.16222 on the full union and 6.18485 with folding omitted. This excludes a violating sequence with radii tending to zero.

## A modified form with boundary action above 6.15

For a pair of distinct, nonantipodal labels let $`v`$ be the unique vector in the closed Euclidean unit disk with $`v\cdot e_a=\sin P_a`$ and $`v\cdot e_b=\sin P_b`$, where $`e_a=(\cos a,\sin a)`$. The pair-polygon inequalities give $`|v|\le1`$. Its height $`z=\sqrt{1-|v|^2}`$ is determined by just the two scalar coordinates. Multiply $`p_{ab}`$ by a continuous function $`m(z)`$ equal to $`9/10`$ through $`z=1/5`$, rising linearly to one at $`21/100`$ and equal to one thereafter. Each term still has a primitive on its coordinate plane. On the round hemisphere all pairs at a point give its actual height. The modified form therefore has the exact boundary action

~~~math
 2\pi\int_0^1 m(z)\,dz=\frac{1959\pi}{1000}=6.1543800083824\ldots .
~~~

This form has **absolute limiting density at most one on all four families**. Round profiles pass by domination by the original coefficient, and clipping keeps the upper bound $`8/(3\pi)`$. For the other two families the eroded cross domain lies inside the folded left-right domain, and half the folded mixed-block integral is at most $`\pi/4`$. For widths at least 0.12 the unmodified cross integral already lies below one. The following uniform estimate at smaller widths is also a test against the earlier finite-width obstruction. [Earlier two-angle modification](issue163_zust_angles.md#a-change-using-both-angles)

Use the folded rescaling above, now writing the two square variables as $`u,v`$. Set $`c=\cos e`$, $`S'=uv`$ and $`T=\tfrac12\log(u/v)`$. The cross weight in $`du\,dv`$ and the corresponding height satisfy

~~~math
 g=\frac{4uv(1-uv)}{(u+v-2cuv)^2},\qquad z^2=\sin^2 e\,g .
~~~

For the height identity use $`z^2=p_{ab}\cos^2P_a\cos^2P_b`$ and the tangent substitutions in the cross-ramp computation. Equivalently, in the original $`U,V`$ variables one has $`z^2=4\tan^2 e\,S'(1-S')/[(1+\tan^2e)^2 H^2]`$. Put $`b=1/5`$. Since $`u+v\ge2\sqrt{uv}`$, for the unsuppressed part $`z\ge b`$ it is necessary that $`\sqrt{S'}\ge r_-(e)`$, where

~~~math
 r_-(e)=\frac{b^2\cos e-\sin^2 e\sqrt{1-b^2}}{b^2+(1-b^2)\sin^2e}.
~~~

This lower endpoint decreases throughout the range $`0\le e\le0.12`$. In the variables $`S',T`$ the weight is $`(1-S')/(\cosh T-c\sqrt{S'})^2`$, on $`|T|\le-\log\sqrt{S'}`$. At $`c=1`$ its $`T`$ integral is $`G(S')=2+2\sqrt{S'/(1-S')}\arccos\sqrt{S'}`$. At general $`c`$ the ratio of integrands is largest at the endpoints of the $`T`$ interval. Thus the height tail is bounded by

~~~math
 H_e=\frac1\pi\int_{r_-(e)^2}^1
 \left(4-\frac23(1-S')\right)
 \left(\frac{1-S'}{1-S'+2(1-\cos e)S'}\right)^2dS'.
~~~

Writing $`S'=\cos^2 t`$, the bound $`G(S')\le4-2(1-S')/3`$ follows from $`t\cos t\le\sin t-\sin^3t/3`$. The difference has derivative $`\sin t(t-\sin t\cos t)\ge0`$. The modified cross is at most $`[9C_K(e)+\min(C_K(e),H_e)]/10`$. On each width interval $`[j/1000,(j+1)/1000]`$, use the left width for $`C_K`$ and $`\cos e`$ and the right width for the lower integration endpoint. The checker bounds the integral by 64 equal subintervals, using the right endpoint for its increasing linear factor and the left for its decreasing ratio. The resulting uniform upper bound through width 0.12 is **0.998788**. This uses two one-dimensional enclosures and no optimization.

A small independent-gradient test illustrates the role of Stokes. On the eroded profile of width 0.1 assign $`(1,0)`$ and $`(0,1)`$ to the outer ramps and $`(1,1)/\sqrt2`$ to the central plateau. Tensor midpoint quadrature gives **1.00505** with 64 nodes per interval and **1.00479** with 128. These are numerical values without a quadrature error bound. The plateau terms giving this excess vanish in the limiting signed Jacobian on the eroded family. The checker reports the quadrature separately from its rational enclosures.

The action and the density conclusions use the same geometric restrictions as the original comparison. For a bounded-area sequence, regularization now gives action $`2\pi\int_{\sqrt{1-q^2}}^1 m(z)\,dz`$, tending to $`1959\pi/1000`$. The scalar-facet argument again retains the full action in the interior. If $`\widetilde R_\eta`$ denotes the measured positive excess of this modified form outside the four families' $`\eta`$-tube, the compactness proof gives, for some fixed $`\eta\gt 0`$ in all genera,

~~~math
 A+\widetilde R_\eta\gt 6.15438 .
~~~

In particular an area at most 6.15 requires **more than 0.00438 exterior positive excess for this specific form**. The net density estimate permits arbitrary oscillating gradients along a sequence of genuine fillings. A globally valid upper bound on the exterior excess is open.

~~~sh
python3 issue163_profile_occupation.py
~~~
