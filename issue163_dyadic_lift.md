# Lifting the signed field to 224 antipodal anchor pairs

For the same orientable circle fillings, the signed 112-point certificate gives
$$
 \operatorname{Area}(M)\ge \frac{617154280862042281}{10^{18}}\pi^2>6.091068606547150624 .
$$
The 224-point lift preserves this bound. Its two-profile dual limits every additional nonnegative endpoint repair for the stated inherited trace rule. The two calculations use the finite transported certificate in the supplied bundle. The 224-point replay first checks the full signed 112-point field and then checks 1,898,400 rooted child profiles. [Signed 112-point proof](issue163_reweighted_field.md)

### Inheritance

Write $Q=64\cdot10^{12}(10^8)^2$. Let $P_i/Q$ be the certified trace on 112-point endpoint profile $i$, and let $U/Q$ be the certified global budget. Use half of the 112-point form on the even 224-point anchors and half on the odd anchors. Their boundary actions agree by rotation, so the raw action is preserved. At a child with parent rows $i,j$, the inherited trace is $(P_i+P_j)/(2Q)$. Its even and odd blocks have separate diagonal witnesses. The existing zero-coordinate argument applies on scalar grid facets.

On the outermost two cells at either end of the 224-point scalar grid, the finite-source enumeration reduces every compatible profile to one of the following rooted label sequences. Indices are zero-based.

- In the first family, $b_j=j-\mathbf 1_{j\ge a}$ for $1\le a\le224$.
- In the second family, the offsets $b_j-j$ form consecutive blocks of $1,0,-1,-2$ of lengths $a,b,c,d$ summing to 224. Here $1\le a<224$. When $d>0$, at least one of $b,c$ must be positive.

The adjacent Lipschitz inequalities make the offsets nonincreasing. The inequalities against the rooted endpoint restrict them to these values and rule out the direct three-unit drop. The source endpoint enumeration proves coverage. The two lists contain $\binom{226}{3}=1{,}898{,}400$ rows.

### A formula for the parent rows

Define $B_k(u,v)=k+\mathbf 1_{k<u}-\mathbf 1_{k\ge v}$ for $0\le k<112$. For the first family the even and odd parent labels are $B(0,\lceil a/2\rceil)$ and $B(0,112)$. For the second family they are
$$
 B\!\left(0,\left\lceil\frac{a+b}{2}\right\rceil\right),\qquad
 B\!\left(\left\lfloor\frac a2\right\rfloor,
          \left\lfloor\frac{a+b+c}{2}\right\rfloor\right).
$$
These follow by taking $\lfloor b_{2k}/2\rfloor$ and $\lfloor b_{2k+1}/2\rfloor$. The checker canonicalizes the 6,439 distinct parent lookups against the hash-bound 112-point profile list.

### Spending the remaining trace

Use the three dihedral orbits with representatives $(1,0,0)$, $(1,0,1)$ and $(2,1,2)$. The coordinates of a representative are the anchor separation and the two scalar cell labels. Give these orbits physical coefficient increments $2L/(4Q),L/(4Q),2L/(4Q)$ respectively. An edge increment of size $x$ costs $x$ in diagonal trace. For multiplicities $c_0,c_1,c_2$ on a child, the exact feasibility check is
$$
  L(2c_0+c_1+2c_2) \le 2(2U-P_i-P_j).
$$
The checker starts at $L=U-P_0$ and takes the minimum of all positive-load ratios. If an earlier ratio has already decreased $L$, every earlier inequality continues to hold. Rows with zero load satisfy the inherited inequality. Every admissible occurrence of a pair of labels $x,y$ at separation $k$ is counted by testing the indices in $[x-1,x+2]\cap[y-k-1,y-k+2]\cap[0,223-k]$, using the four possible offsets.

In units of $1/(2\cdot224^2)$ the three raw boundary-action weights are $448,896,1792$. The normalized area gain is exactly $\pi^2(3/224)L/U$. The replay gives $U=639414960924605591061056558420$, $P_0=639414960924605591061056558420$ and $L=0$ in the common trace units.

### A two-profile upper bound on all 666 positive edge repairs

Consider any nonnegative physical increments $x_o$ on all 666 fresh endpoint classes, while keeping the parent witnesses, the global budget and the edgewise trace repair rule fixed. Take the first-family row $a=1$ and the second-family row $(a,b,c,d)=(1,1,1,221)$. Both their even and odd parents are row zero. Let $c_{Ao},c_{Bo}$ be the counts of orbit $o$ in these rows, and let $\omega_o$ be its boundary-action weight in units of $\pi^2$. The exhaustive integer check gives
$$
  \omega_o\le \frac{c_{Ao}+2c_{Bo}}{224}\qquad(1\le o\le666).
$$
Multiplying by $x_o$ and summing shows that the normalized area gain for this whole family is at most $\pi^2(3/224)(U-P_0)/U$. Here $P_0=U$, so the upper bound on the additional action is exactly zero. Every one of the 666 classes has positive multiplicity in at least one of the two saturated rows.

### Replay

Keep the three lower-bound JavaScript files together and run

~~~sh
node issue163_dyadic_lift.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The certificates use integer arithmetic for the trace, orbit counts and action comparisons. The displayed decimals use a directed rational lower enclosure of $\pi$.
