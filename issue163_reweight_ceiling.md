# A local ceiling for the 15 scalar multipliers

Fix the 112-point transported field and the three coefficient increments from commit <code>5426ac4</code>. In units of $1/(16\cdot10^{12})$ these are $(1,6714930082)$, $(115,49203043)$ and $(280,10427640066)$. Allow all 15 real interval multipliers to vary. A common rescaling cancels from the ratio of boundary action to norm. The bounds below apply if some positive rescaling of the multiplier vector $s$ satisfies $\|s-c\|_\infty\le r$. The reference vector $c$, recorded exactly in the witness file, is the one in that commit. Each bound covers the entire box.

| $r$ | Independent planar comass tests on the terminal cells | Independent diagonal PSD certificates on the terminal cells |
|---:|---:|---:|
| $0.02$ | $6.094181375728$ | $6.091303086224$ |
| $0.05$ | $6.098672199104$ | $6.095700444190$ |

The entries are upper bounds on the area lower bound this fixed-field certificate can yield. The planar column permits exact maximization over all planar gradient vectors at each single cell. The PSD column permits arbitrary feasible diagonal witnesses at each cell. Coupled tests across cells, other endpoint coefficients and other closed forms are open directions.

## Proof

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

Place the two lower-bound checkers, the ceiling checker and its JSON witness in the same directory. Run

~~~sh
node issue163_reweight_ceiling.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~
