# How much can these coefficients improve the certificate?

With the 15 scalar multipliers from the three-coefficient checkpoint fixed, let the three raw endpoint coefficients in classes 1, 115 and 280 range independently over all real numbers. Keep every other raw coefficient fixed. For certificates that bound each terminal cell separately, the optimal area bound lies in the following intervals.

| Norm test | Achieved lower bound | Certified upper bound |
|---|---:|---:|
| Independent planar gradients | $6.090475197311347654$ | $6.090480263618$ |
| Diagonal Hermitian PSD witnesses | $6.090475197311347654$ | $6.090475261348$ |

The distance to the second upper endpoint is less than $6.404\cdot10^{-8}$. The signed changes in the later lower bound use additional endpoint classes. [Lower-bound proof](issue163_reweighted_field.md)

### All 330 nonnegative endpoint changes

Fix the multiplier vector and the three-coefficient calibration from the first table at commit <code>0a29d2a</code>. Starting from that field, allow independent **nonnegative increments of arbitrary size** in all 330 fresh endpoint classes at level 112. The action obtainable by independent planar tests is at most $6.090478414162$. For the diagonal PSD norm test the upper bound is $6.090475297341$.

The checker enumerates every endpoint orbit having a scalar label in the two outermost cells at either end. A mixture of three planar unit-vector tests bounds both the constant term in the action and its slope in each of the 330 directions. Four tests suffice for the PSD mixture. Every inequality is rational. Since the changes are nonnegative, summing these slope inequalities against the changes proves the bound simultaneously on the entire nonnegative orthant. Allowing a coefficient to decrease removes this implication.

### Required size of the coefficient decreases

Keep the same scalar multipliers and let all 330 endpoint coefficients change with either sign. Measure their physical changes $t_j$ relative to the three-coefficient checkpoint, before applying the scalar multipliers. Write $r_-=\sum_j\max(0,-t_j)$. These comparisons put no limit on positive changes.

| Norm test | Bound on $r_-$ | Upper bound on the attainable area certificate |
|---|---:|---:|
| Independent planar gradients | $1/160$ | $6.099901142931$ |
| Independent diagonal PSD witnesses | $1/80$ | $6.099787086674$ |

Thus reaching $6.1$ by this route requires $r_->1/160$ for planar tests and $r_->1/80$ for diagonal PSD witnesses. To see this, let $h_j\ge0$ be the excess of the monotone dual mixture's physical slope over the action slope for class $j$. Arbitrary signed changes reduce the mixture's domination margin by at most $r_-\max_j h_j$. An interior test with positive value $b_q$ has zero slope on every endpoint class. Adding weight $r_-\max_j h_j/b_q$ to that test restores domination. The replay rounds the extra weight upward and checks the cross-multiplied inequality.

### Varying the endpoint coefficients and all 15 multipliers together

Let $s_*$ be the multiplier vector in the lower-bound proof. Allow all three endpoint coefficients to vary freely as above and allow any positive rescaling of $s$ to lie in the indicated box. Rescaling leaves the normalized action invariant.

| Multiplier box | Upper bound using independent planar gradients |
|---|---:|
| $\|s-s_*\|_\infty\le 0.02$ | $6.093053684618$ |
| $\|s-s_*\|_\infty\le 0.05$ | $6.097833910032$ |

The upper bounds concern this family of certificates. The filling-area inequality and calibrations coupling gradients across different cells have a different scope.

### Four-profile proof for fixed multipliers

Write $u_1,u_2,u_3$ for the three changes in the physical coefficients of the reference field. With fixed multipliers the boundary action divided by $\pi^2$ is the affine function $a_0+\sum_j a_j u_j$. Every chosen profile and rational unit-ball vector gives a necessary inequality $b_p+\sum_j g_{pj}u_j\le U$ for a claimed norm budget $U$. For a diagonal PSD budget one can also sum several planar columns if at each anchor the sum of their squared absolute values is at most one.

Take the terminal profiles $(14,2846)$, $(112,0)$, $(112,12)$ and $(112,67)$, with zero-based row indices. The replay constructs two separate mixtures using rational data. In each it solves the four equations
$$
 \sum_p\lambda_p b_p=a_0,\qquad
 \sum_p\lambda_p g_{pj}=a_j\quad (j=1,2,3).
$$
Integer determinants give the weights. A subsequent multiplication checks all four identities and the nonnegativity of every weight. Consequently the action is bounded by $\pi^2 U\sum_p\lambda_p$ for every real choice of the three coefficients. Upward rounding of $\pi^2\sum_p\lambda_p$ gives the first table.

### Joint proof

Every edge in endpoint orbit $j$ has the same unordered pair $(a_j,b_j)$ of absolute scalar bins. Its boundary-action and profile-test slopes both acquire the factor $s_{a_j}s_{b_j}$. Thus matching the three unweighted slopes cancels **all dependence on the free endpoint coefficients for every multiplier vector**.

Use 17 rank-one planar tests. The checker rounds the proposed mixture weights to rationals and solves a three-by-three system for three of them. It checks all three cancellations exactly and verifies positivity. A further nonnegative weight on the coarse profile $(14,2846)$ preserves the cancellations because that profile contains no 112-point correction.

For the resulting mixture, write $H=\sum_p\lambda_p M_p-A$, where $s^TM_p s$ is the test value and $\pi^2s^TAs$ is the boundary action on the reference field. Both are quadratic in $s$. The three cancellations make the same difference matrix valid for every choice of endpoint coefficients. For each radius the checker verifies
$$
 s_*^T Hs_*-2r\sum_i |(Hs_*)_i|-r^2\sum_{i,j}|H_{ij}|>0
$$
in integer arithmetic. Expanding at $s_*$ proves $s^T Hs>0$ throughout the box, and the normalized boundary action is at most $\pi^2\sum_p\lambda_p$. In all of these tests the complex witness vectors, scalar values and weights have exact rational representations.

### Earlier fixed-field multiplier test

Fix the 112-point transported field and the three coefficient increments from commit <code>5426ac4</code>. In units of $1/(16\cdot10^{12})$ these are $(1,6714930082)$, $(115,49203043)$ and $(280,10427640066)$. Allow all 15 real interval multipliers to vary. A common rescaling cancels from the ratio of boundary action to norm. The bounds below apply if some positive rescaling of the multiplier vector $s$ satisfies $\|s-c\|_\infty\le r$. The reference vector $c$, recorded exactly in the witness file, is the one in that commit. Each bound covers the entire box.

| $r$ | Independent planar comass tests on the terminal cells | Independent diagonal PSD certificates on the terminal cells |
|---:|---:|---:|
| $0.02$ | $6.094181375728$ | $6.091303086224$ |
| $0.05$ | $6.098672199104$ | $6.095700444190$ |

The entries are upper bounds on the area lower bound this fixed-field certificate can yield. The planar column permits exact maximization over all planar gradient vectors at each single cell. The PSD column permits arbitrary feasible diagonal witnesses at each cell. Coupled tests across cells, other endpoint coefficients and other closed forms are open directions.

### Fixed-field proof

Write the normalized boundary action as $s^T A s$ in units of $\pi^2$. The endpoint orbit sums determine the symmetric rational matrix $A$. On a fixed terminal profile $p$, take rational complex vectors $z_i\in\mathbb C^k$ satisfying $\|z_i\|_2\le1$. Summing the $k$ quadratic-form evaluations gives another quadratic polynomial $s^TM_p s$. For $k=1$ it is a planar test. For any $k$, every PSD diagonal bound $U$ satisfies $s^T M_p s\le U$, since the contribution of its diagonal is at most $\sum_i d_i\|z_i\|_2^2\le\sum_i d_i$. Thus a vector of nonnegative rational weights $\lambda_p$ for which
$$
  s^T\left(\sum_p\lambda_p M_p-A\right)s>0
$$
throughout the box gives an upper bound $\pi^2\sum_p\lambda_p$ for the certificate value.

The two mixtures each use 15 profile tests. The planar mixture uses rank one throughout. The other mixture uses rank three on two endpoint profiles and rank one elsewhere. All complex components and weights are stored as integers with common denominators. For each stated radius the checker multiplies its mixture by a fixed rational factor and forms $H=\sum_p\lambda_p M_p-A$. Expanding around $c$ proves positivity throughout the box whenever
$$
  c^T Hc-2r\sum_i |(Hc)_i|-r^2\sum_{i,j}|H_{ij}|>0.
$$
All four strict comparisons pass in integer arithmetic. The reported upper endpoints use an upper rational enclosure of $\pi$ and upward rounding. The proof only uses the 18 distinct stored configurations; finding them again by numerical optimization is unnecessary.

## Replay

Keep the three JavaScript checkers and the three JSON witness files together and run

~~~sh
node issue163_reweight_ceiling.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The replay checks the signed rational tests against the supplied finite input, constructs each mixture, and prints all bounds with directed rounding. The public Lean repository verifies the earlier Fourier work. The upper bounds here have independent integer replays.
