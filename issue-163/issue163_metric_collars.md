# How much of a filling lies near its boundary?

Let $`I`$ be the infimum of the areas of smooth compact connected orientable fillings of the isometrically embedded circle of length $`2\pi`$, over every genus. Let $`C_*=6.095910645232136335\ldots`$ denote the certified lower bound for $`I`$ and $`B=6.095889052386098292\ldots`$ the boundary action of the bisected-gap form. The following comparison gives a metric region of guaranteed area on which to test directional loss in the comass. [Exact values and tensor inequality](issue163_comass_residual.md)

Write $`v(x)=d_M(x,\partial M)`$ and $`V(t)=\mathrm{Area}\{v\lt t\}`$. For every filling and $`t\ge0`$,

~~~math
 V(t)\ge H_I(t)\ge H_{C_*}(t),\qquad
 H_c(t)=c\big[1-(1-\pi t/c)_+^2\big].
~~~

In particular, the collar of metric width $`0.22`$ has area greater than $`1.303938`$. This covers the part of the collar beyond the first cut point of the boundary normals as well.

## Cutting and capping a level set

First take a smooth function $`f`$ which is zero on the external boundary and positive inside, with Lipschitz constant at most $`1+\varepsilon`$. At a positive regular value $`s`$, keep the component of $`\{f\le s\}`$ containing the external boundary. Its other boundary components are finitely many smooth circles. Cap a circle of length $`l_i`$ with a scaled copy of an isometric filling of the unit circle of circumference $`2\pi`$ having area at most $`I+\delta`$. An excursion through this cap costs at least the shorter seam arc. Replacing excursions by seam arcs gives paths in the old filling and protects all external distances. It suffices to approximate paths by piecewise smooth paths transverse to the seams. Orient the caps compatibly. In arclength and normal coordinates the glued metric is continuous. Smooth it from above in seam neighborhoods with area error tending to zero, preserving the external boundary. [Details of seam smoothing](issue163_genus_reduction.md#proof)

Write $`V_f(s)=\mathrm{Area}\{f\lt s\}`$ and $`L_f(s)=\mathrm{length}\{f=s\}`$. The cap cost is at most $`(I+\delta)\sum_i l_i^2/(4\pi^2)`$ and $`\sum_i l_i\le L_f(s)`$. Letting $`\delta`$ tend to zero gives

~~~math
 I\le V_f(s)+\frac{I}{4\pi^2}L_f(s)^2,\qquad
 V_f'(s)\ge\frac{2\pi}{1+\varepsilon}\sqrt{(1-V_f(s)/I)_+}
 \quad\text{for almost every }s>0.
~~~

The derivative inequality follows from coarea at regular values and Sard's theorem. While $`V_f\lt I`$, compose with $`y\mapsto 2I(1-\sqrt{1-y/I})`$. The derivative of the composition is at least $`2\pi/(1+\varepsilon)`$ almost everywhere. A monotone function's total increase dominates the integral of its almost-everywhere derivative, including across critical values. Inverting gives $`V_f(s)\ge H_I(s/(1+\varepsilon))`$. The same inequality holds after $`V_f`$ reaches $`I`$.

The distance $`v`$ is smooth in a normal neighborhood of the boundary. Keep it fixed on a smaller collar and smooth on its complement to get $`\|f-v\|_\infty\le\varepsilon`$ and the stated Lipschitz bound. One construction uses sufficiently small coordinate balls on which the metric varies by a factor arbitrarily close to one, convolution on each ball and a smooth partition of unity. The partition derivative terms involve only the uniform approximation errors on the finitely many balls. Choose those errors small enough also to preserve positivity off the smaller collar. Since $`V(t)\ge V_f(t-\varepsilon)`$ for $`t\gt \varepsilon`$, passage to the limit proves the claim. The last comparison uses that $`H_c(t)`$ is increasing in $`c`$.

## A local test at the scale of 6.15

Choose any fixed rotation of the 112-pair grid and any admissible profile $`P_j`$ with the triangular boundary trace. For the certified normalized diagonal $`D_j`$ in its cell, let $`T=\sum_j D_j\nabla P_j\otimes\nabla P_j`$, $`\tau=\mathrm{tr}(T)`$ and $`r=(\lambda_{\max}(T)-\lambda_{\min}(T))/\tau`$. Give $`r`$ value zero when the trace vanishes. The comass comparison gives $`\tau\le1`$ and $`B\le\int_M\tau\sqrt{1-r^2}\,dA`$. Write $`m_t=\int_{v\lt t}\tau\,dA`$, $`m=\int_M\tau\,dA`$ and set $`q_t^2=m_t^{-1}\int_{v\lt t}\tau r^2\,dA`$ when $`m_t\gt 0`$, with $`q_t=0`$ otherwise. Then

~~~math
 A\ge B+H_{C_*}(t)\big(1-\sqrt{1-q_t^2}\big).
~~~

Indeed, Jensen's inequality bounds the collar contribution to the action by $`m_t\sqrt{1-q_t^2}\le V(t)\sqrt{1-q_t^2}`$. The complement contributes at most $`A-V(t)`$. Also $`m\ge B`$ and $`m-m_t\le A-V(t)`$. Thus a filling of area $`A\lt D=6.15`$ must satisfy

~~~math
 \frac{m_t}{m}>1-\frac{D-H_{C_*}(t)}{B},\qquad
 q_t<\sqrt{1-\left(1-\frac{D-B}{H_{C_*}(t)}\right)^2}
 \quad\text{if }H_{C_*}(t)>D-B.
~~~

| Metric width | Guaranteed collar area exceeds | Trace fraction if area is below 6.15 exceeds | Necessary upper bound for collar RMS | Round hemisphere RMS, numerical |
|---:|---:|---:|---:|---:|
| 0.05 | 0.310111 | 0.04199 | 0.564386 | 0.6172–0.6198 |
| 0.10 | 0.612127 | 0.09153 | 0.411075 | 0.4742–0.4767 |
| 0.22 | 1.303938 | 0.20502 | 0.285087 | 0.3296–0.3318 |
| 0.40 | 2.254225 | 0.36091 | 0.217790 | 0.2494–0.2513 |

For example, $`q_{0.22}\ge0.30`$ in any filling implies $`A\gt 6.155949`$. The final column uses 96 radial by 8 angular midpoint samples with the antipodal distance-difference profile on the unit round hemisphere. Each interval encloses the range of the existing diagonal proposals **at those sample points**. At width $`0.22`$ a 24-by-6 mesh gives $`0.3298`$–$`0.3322`$. These are quadrature results without a discretization error bound. The metric collar area is controlled in every genus. A sufficient lower bound on its directional imbalance in every putative smaller filling remains open.

From the repository's <code>issue-163</code> directory run

~~~sh
node issue163_hemisphere_moments.cjs issue163_inputs --collars
~~~
