# Lifting the signed field to 224 antipodal anchor pairs

For the same orientable circle fillings, the signed 112-point certificate gives
$$
 \mathrm{Area}(M)\ge \frac{617165758412709490}{10^{18}}\pi^2>6.091181885431729436 .
$$
The 224-point construction gives
$$
 \mathrm{Area}(M)\ge \frac{617165761918607805}{10^{18}}\pi^2>6.091181920033558876 .
$$
Both statements use the finite transported certificate in the supplied bundle. The 224-point replay first checks the full signed 112-point field and then checks 1,898,400 rooted child profiles. [Signed 112-point proof](issue163_reweighted_field.md)

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
The checker compares the 220 third-orbit choices having the same boundary weight and the same two dual-row counts. For each choice it starts at $L=U-P_0$ and takes the minimum of all positive-load ratios. If an earlier ratio has already decreased $L$, every earlier inequality continues to hold. Rows with zero load satisfy the inherited inequality. Every admissible occurrence of a pair of labels $x,y$ at separation $k$ is counted by testing the indices in $[x-1,x+2]\cap[y-k-1,y-k+2]\cap[0,223-k]$, using the four possible offsets.

In units of $1/(2\cdot224^2)$ the three raw boundary-action weights are $448,896,1792$. The normalized area gain is exactly $\pi^2(3/224)L/U$. The replay gives $U=639413036587531299403539588646$, $P_0=639412869205988776176689091810$ and $L=167381542523226850496836$ in the common trace units.

### A two-profile upper bound on all 666 positive edge repairs

Consider any nonnegative physical increments $x_o$ on all 666 fresh endpoint classes, while keeping the parent witnesses, the global budget and the edgewise trace repair rule fixed. Take the first-family row $a=1$ and the second-family row $(a,b,c,d)=(1,1,1,221)$. Both their even and odd parents are row zero. Let $c_{Ao},c_{Bo}$ be the counts of orbit $o$ in these rows, and let $\omega_o$ be its boundary-action weight in units of $\pi^2$. The exhaustive integer check gives
$$
  \omega_o\le \frac{c_{Ao}+2c_{Bo}}{224}\qquad(1\le o\le666).
$$
Multiplying by $x_o$ and summing shows that the normalized area gain for this whole family is at most $\pi^2(3/224)(U-P_0)/U$. The three chosen increments attain this upper bound exactly. This solves the entire nonnegative 224-point edge-repair problem for this fixed parent certificate.

The optimal three-orbit choice uses the full budget on both dual rows. Its 224-point row $A_{224}$ is therefore saturated.

### All later dyadic levels

The two saturated rows also give a uniform argument for an arbitrarily long chain of nonnegative repairs. Let $N=2m\ge8$. Consider the rooted profiles
$$
 A_N=(0,0,1,2,\ldots,N-2),\qquad B_N=(1,1,1,1,2,3,\ldots,N-3).
$$
The even and odd parents of $A_N$ are $A_m$ and the straight row $(0,1,\ldots,m-1)$, which is a signed cyclic shift of $A_m$. Both parents of $B_N$ are $A_m$. Every new endpoint orbit occurs in at least one of $A_N,B_N$. Indeed, use the orbit symmetries to put the separation at $1\le k\le N/2$ and the first label at $x=0$ or $1$. Compatibility forces $k-1\le y\le k$ for $x=0$ and $k-2\le y\le k+1$ for $x=1$, subject to valid labels. The first two entries of $A_N$ realize both choices for $x=0$. For $x=1$ and $k\ge3$, the first four entries of $B_N$ realize all four choices. For $k=1,2$ that row supplies all positive choices, and swapping the pair handles $y=0$.

On a profile whose inherited trace equals the common budget, every orbit present must have zero nonnegative increment under the edgewise trace repair rule. If the starting $A_m$ is saturated, both displayed children are saturated, every new increment is zero, and $A_N$ is saturated again. Induction covers every subsequent doubling.

The conclusion also holds if we raise the common trace budget. Start at the optimized 224-point field and write its raw action as $\pi^2 C$ and its certified budget in physical units as $T$. The saturated profile $A_{224}$ has trace $T$. At all later levels the inherited traces of $A_N$ and $B_N$ are at least $T$. If a budget $U'\ge T$ applies at every stage, each row has room for total increment at most $U'-T$. Every endpoint orbit appears in at least one of the two rows. An orbit contains at most 16 triples, obtained by changing the separation between $k$ and $N-k$, swapping the labels, and complementing either label. Each triple has raw boundary weight at most $\pi^2/N$. Consequently the raw action gain at level $N$ is at most $\pi^2(32/N)(U'-T)$. Summing for $N=448,896,\ldots$ gives
$$
 \frac{\text{certified area}}{\pi^2}
 \le \frac{C+(32/224)(U'-T)}{U'} \le \frac{C}{T},
$$
since $C/T>0.61>32/224$. This proves exhaustion for any number of doublings with these starting coefficients and witnesses, direct-sum inheritance, and nonnegative increments charged edge by edge to diagonal trace.

The absolute-value trace charge also settles signed increments under this same rule. Each triple has nonnegative boundary weight in the chosen orientation. Replacing an increment $x_o$ by $|x_o|$ preserves its contribution to every edgewise trace charge and weakly increases its boundary action. The inherited trace at each later level is consequently the same. Applying this replacement at every level reduces signed increments to the nonnegative case proved above. To benefit from coefficient cancellation one must change the norm witness or the charging rule.

### Replay

Keep the three lower-bound JavaScript files together and run

~~~sh
node issue163_dyadic_lift.cjs /path/to/bundle/research/output/improve112_6081_certificate
~~~

The certificates use integer arithmetic for the trace, orbit counts and action comparisons. The displayed decimals use a directed rational lower enclosure of $\pi$.
